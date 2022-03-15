//! The C front-end

mod ast_utils;
mod parser;
mod term;
mod types;

use super::{FrontEnd, Mode};
use crate::circify::{Circify, Loc, Val};
use crate::front::c::ast_utils::*;
use crate::front::c::term::*;
use crate::front::c::types::*;
use crate::front::field_list::FieldList;
use crate::ir::opt::cfold::fold;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;
use lang_c::ast::*;
use lang_c::span::Node;
use log::debug;

use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;

use crate::front::PROVER_VIS;
use crate::front::PUBLIC_VIS;

/// Inputs to the C compiler
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
    /// The file to look for concrete arguments to main in. Optional.
    ///
    /// ## Examples
    ///
    /// If main takes `x: u64, y: field`, this file might contain
    ///
    /// ```ignore
    /// x 4
    /// y -1
    /// ```
    pub inputs: Option<PathBuf>,
    /// The mode to generate for (MPC or proof). Effects visibility.
    pub mode: Mode,
}

/// The C front-end. Implements [FrontEnd].
pub struct C;

impl FrontEnd for C {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let parser = parser::CParser::new();
        let p = parser.parse_file(&i.file).unwrap();
        let mut g = CGen::new(i.inputs, i.mode, p.unit);
        g.visit_files();
        g.entry_fn("main");
        g.circ.consume().borrow().clone()
    }
}

#[derive(Clone)]
enum CLoc {
    Var(Loc),
    Member(Box<CLoc>, String),
    Idx(Box<CLoc>, CTerm),
}

impl CLoc {
    fn loc(&self) -> &Loc {
        match self {
            CLoc::Var(l) => l,
            CLoc::Idx(i, _) => i.loc(),
            CLoc::Member(i, _) => i.loc(),
        }
    }
}

struct CGen {
    circ: Circify<Ct>,
    mode: Mode,
    tu: TranslationUnit,
    structs: HashMap<String, Ty>,
    functions: HashMap<String, FnInfo>,
}

impl CGen {
    fn new(inputs: Option<PathBuf>, mode: Mode, tu: TranslationUnit) -> Self {
        let this = Self {
            circ: Circify::new(Ct::new(inputs.map(parser::parse_inputs))),
            mode,
            tu,
            structs: HashMap::default(),
            functions: HashMap::default(),
        };
        this.circ
            .cir_ctx()
            .cs
            .borrow_mut()
            .metadata
            .add_prover_and_verifier();
        this
    }

    /// Unwrap a result of an error and abort
    fn err<E: Display>(&self, e: E) -> ! {
        println!("Error: {}", e);
        std::process::exit(1)
    }

    /// Unwrap result of a computation
    fn unwrap<CTerm, E: Display>(&self, r: Result<CTerm, E>) -> CTerm {
        r.unwrap_or_else(|e| self.err(e))
    }

    pub fn d_type_(&mut self, ds: Vec<Node<DeclarationSpecifier>>) -> Option<Ty> {
        assert!(!ds.is_empty());
        let res: Vec<Option<Ty>> = ds
            .iter()
            .map(|d| match &d.node {
                DeclarationSpecifier::TypeSpecifier(t) => self.type_(t.node.clone()),
                _ => unimplemented!("Unimplemented declaration type: {:#?}", d),
            })
            .collect();
        compress_type(res)
    }

    pub fn s_type_(&mut self, ss: Vec<Node<SpecifierQualifier>>) -> Option<Ty> {
        assert!(!ss.is_empty());
        let res: Vec<Option<Ty>> = ss
            .iter()
            .map(|s| match &s.node {
                SpecifierQualifier::TypeSpecifier(t) => self.type_(t.node.clone()),
                _ => unimplemented!("Unimplemented specifier type: {:#?}", s),
            })
            .collect();
        compress_type(res)
    }

    fn type_(&mut self, t: TypeSpecifier) -> Option<Ty> {
        return match t {
            TypeSpecifier::Int => Some(Ty::Int(true, 32)),
            TypeSpecifier::Unsigned => Some(Ty::Int(false, 32)), // Some(Ty::Int(false, 32)),
            TypeSpecifier::Bool => Some(Ty::Bool),
            TypeSpecifier::Void => None,
            TypeSpecifier::Struct(s) => {
                let StructType {
                    kind: _kind,
                    identifier,
                    declarations,
                } = s.node;
                let name = identifier.unwrap().node.name;
                let mut fs: Vec<(String, Ty)> = Vec::new();
                match declarations {
                    Some(decls) => {
                        for d in decls.into_iter() {
                            match d.node {
                                StructDeclaration::Field(f) => {
                                    let base_field_type =
                                        self.s_type_(f.node.specifiers.clone()).unwrap();
                                    for struct_decl in f.node.declarators.iter() {
                                        let name = name_from_decl(
                                            &struct_decl.node.declarator.clone().unwrap().node,
                                        );
                                        let decl =
                                            struct_decl.node.declarator.clone().unwrap().node;
                                        let derived_ty = self.get_derived_type(
                                            base_field_type.clone(),
                                            decl.derived,
                                        );
                                        // fs.push((name, derived_ty));
                                        unimplemented!();
                                    }
                                }
                                StructDeclaration::StaticAssert(_a) => {
                                    unimplemented!("Struct static assert not implemented!");
                                }
                            }
                        }
                    }
                    None => {}
                }
                Some(Ty::Struct(name, FieldList::new(fs)))
            }
            _ => unimplemented!("Type {:#?} not implemented yet.", t),
        };
    }

    fn get_inner_derived_type(&mut self, base_ty: Ty, d: DerivedDeclarator) -> Ty {
        match d.clone() {
            DerivedDeclarator::Array(arr) => {
                if let ArraySize::VariableExpression(expr) = &arr.node.size {
                    let expr_ = self.gen_expr(expr.node.clone());
                    let size = self.fold_(expr_) as usize;
                    return Ty::Array(size, Box::new(base_ty));
                }
                panic!("Derived type not array");
            }
            DerivedDeclarator::Pointer(_) => {
                // let num_bits = base_ty.num_bits();
                // TODO: assume 32 bit ptrs for now.
                return Ty::Ptr(32, Box::new(base_ty));
            }
            _ => panic!("Not implemented: {:#?}", d),
        }
    }

    pub fn get_derived_type(&mut self, base_ty: Ty, derived: Vec<Node<DerivedDeclarator>>) -> Ty {
        if derived.is_empty() {
            return base_ty;
        }
        let mut derived_ty: Ty = base_ty;
        for d in derived.iter().rev() {
            let inner_derived_ty = self.get_inner_derived_type(derived_ty.clone(), d.node.clone());
            derived_ty = inner_derived_ty;
        }
        derived_ty
    }

    pub fn get_decl_info(&mut self, decl: Declaration) -> Vec<DeclInfo> {
        let mut ty: Ty = self.d_type_(decl.specifiers).unwrap();
        for d in decl.declarators.iter() {
            let derived = &d.node.declarator.node.derived;
            let derived_ty = self.get_derived_type(ty, derived.to_vec());
            ty = derived_ty;
        }

        // Save struct declarations to the cache
        let new_ty: Ty = match ty.clone() {
            Ty::Struct(name, fs) => {
                if fs.clone().len() > 0 {
                    self.structs.insert(name.to_string(), ty.clone());
                    ty
                } else {
                    self.structs.get(&name).unwrap().clone()
                }
            }
            _ => ty,
        };

        let mut res: Vec<DeclInfo> = Vec::new();
        for node in decl.declarators.into_iter() {
            let name = name_from_decl(&node.node.declarator.node);
            let d = DeclInfo {
                name,
                ty: new_ty.clone(),
            };
            res.push(d);
        }
        res
    }

    pub fn get_param_info(&mut self, decl: ParameterDeclaration, v: bool) -> ParamInfo {
        let mut vis: Option<PartyId> = None;
        let base_ty: Option<Ty>;
        if v {
            vis = interpret_visibility(&decl.specifiers[0].node, self.mode);
            base_ty = self.d_type_(decl.specifiers[1..].to_vec());
        } else {
            base_ty = self.d_type_(decl.specifiers);
        }
        let d = &decl.declarator.as_ref().unwrap().node;
        let derived_ty = self.get_derived_type(base_ty.unwrap(), d.derived.to_vec());
        let name = name_from_decl(d);
        ParamInfo {
            name,
            ty: derived_ty,
            vis,
        }
    }

    pub fn get_fn_info(&mut self, fn_def: &FunctionDefinition) -> FnInfo {
        let name = name_from_func(fn_def);
        let ret_ty = self.ret_ty_from_func(fn_def);
        let args = args_from_func(fn_def).unwrap();
        let body = body_from_func(fn_def);

        FnInfo {
            name,
            ret_ty,
            args: args.to_vec(),
            body,
        }
    }

    fn ret_ty_from_func(&mut self, fn_def: &FunctionDefinition) -> Option<Ty> {
        self.d_type_(fn_def.specifiers.clone())
    }

    pub fn field_select(&self, struct_: &CTerm, field: &str) -> Result<CTerm, String> {
        if let CTermData::CStruct(_, fs) = &struct_.term {
            if let Some((_, term_)) = fs.search(field) {
                return Ok(term_.clone());
                // let struct_terms = struct_.term.terms(self.circ.cir_ctx());
                // let field_term = term(Op::Field(idx), struct_terms);
                // let res = match term_.term.type_() {
                //     Ty::Bool => Ok(cterm(CTermData::CBool(field_term))),
                //     Ty::Int(b, s) => Ok(cterm(CTermData::CInt(b, s, field_term))),
                //     Ty::Array(_s, _t) => {
                //         unimplemented!("array in structs not implemented yet")
                //         // Ty::Array(s, t) => {
                //         //     let expr =
                //         //     Ok(cterm(CTermData::CArray(*t, term_)))
                //         // },
                //     }
                //     Ty::Struct(_, _) => Ok(fs.search(field).unwrap().1.clone()),
                // };
            } else {
                return Err(format!("No field '{}'", field));
            }
        } else {
            return Err(format!("{} is not a struct", struct_));
        }
    }

    pub fn field_store(&self, struct_: CTerm, field: &str, val: CTerm) -> Result<CTerm, String> {
        if let CTermData::CStruct(struct_ty, fs) = &struct_.term {
            if let Some((idx, _)) = fs.search(field) {
                let mut new_fs = fs.clone();
                new_fs.set(idx, val);
                let res = cterm(CTermData::CStruct(struct_ty.clone(), new_fs.clone()));
                return Ok(res);
                //get term
                // let struct_terms = term_.term.terms(self.circ.cir_ctx());
                // let field_term = term(Op::Field(idx), struct_terms);

                //get val term
                // let val_term = val.term.term(self.circ.cir_ctx());

                // term![Op::Update(idx); struct_.term.clone(), val.term],

                //update term
                // let updated_term = term![Op::Update(idx); val_term];
                // let updated_cterm = match &term_.term {
                //     CTermData::CBool(_) => cterm(CTermData::CBool(updated_term)),
                //     CTermData::CInt(b, s, _) => cterm(CTermData::CInt(*b, *s, updated_term)),
                //     CTermData::CArray(_inner_ty, _alloc_id) => {
                //         unimplemented!("array in structs not implemented yet")
                //     }
                //     CTermData::CStruct(inner_ty, inner_fs) => {
                //         let mut new_inner_fs = inner_fs.clone();
                //         new_inner_fs.set(idx, val);
                //         cterm(CTermData::CStruct(inner_ty.clone(), new_inner_fs.clone()))
                //     }
                // };
            } else {
                return Err(format!("No field '{}'", field));
            }
        } else {
            return Err(format!("{} is not a struct", struct_));
        }
    }

    fn array_select(&self, array: CTerm, idx: CTerm) -> Result<CTerm, String> {
        match (array.clone().term, idx.term) {
            (CTermData::CArray(ty, id), CTermData::CInt(_, _, idx)) => {
                let i = id.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", array));
                Ok(cterm(match ty {
                    Ty::Bool => CTermData::CBool(self.circ.load(i, idx)),
                    Ty::Int(s, w) => CTermData::CInt(s, w, self.circ.load(i, idx)),
                    // TODO: Flatten array so this case doesn't occur
                    // Ty::Array(_,t) => {
                    //     CTermData::CArray(*t, id)
                    // }
                    _ => unimplemented!(),
                }))
            }
            (a, b) => Err(format!("[Array Select] cannot index {} by {}", b, a)),
        }
    }

    pub fn array_store(&mut self, array: CTerm, idx: CTerm, val: CTerm) -> Result<CTerm, String> {
        match (array.clone().term, idx.term) {
            (CTermData::CArray(_, id), CTermData::CInt(_, _, idx_term)) => {
                let i = id.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", array.clone()));
                let new_val = val.term.term(&self.circ.cir_ctx());
                self.circ.store(i, idx_term, new_val);
                Ok(val)
            }
            (a, b) => Err(format!("[Array Store] cannot index {} by {}", b, a)),
        }
    }

    /// Computes base[val / loc]    
    fn rebuild_lval(&mut self, base: CTerm, loc: CLoc, val: CTerm) -> Result<CTerm, String> {
        match loc {
            CLoc::Var(_) => Ok(val),
            CLoc::Idx(inner_loc, idx) => {
                let old_inner = self.array_select(base.clone(), idx.clone())?;
                let new_inner = self.rebuild_lval(old_inner, *inner_loc, val)?;
                self.array_store(base, idx, new_inner)
            }
            CLoc::Member(inner_loc, field) => {
                let old_inner = self.field_select(&base, &field)?;
                let new_inner = self.rebuild_lval(old_inner, *inner_loc, val)?;
                self.field_store(base, &field, new_inner)
            }
        }
    }

    fn gen_lval(&mut self, expr: Node<Expression>) -> CLoc {
        match expr.node {
            Expression::Identifier(_) => {
                let base_name = name_from_expr(expr);
                CLoc::Var(Loc::local(base_name))
            }
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Index => {
                        let base = self.gen_lval(*bin_op.lhs);
                        let idx = self.gen_expr(bin_op.rhs.node);
                        CLoc::Idx(Box::new(base), idx)
                    }
                    _ => unimplemented!("Invalid left hand value"),
                }
            }
            Expression::Member(node) => {
                let MemberExpression {
                    operator: _operator,
                    expression,
                    identifier,
                } = node.node;
                let base_name = name_from_expr(*expression);
                let field_name = identifier.node.name;
                CLoc::Member(Box::new(CLoc::Var(Loc::local(base_name))), field_name)
            }
            _ => unimplemented!("Invalid left hand value"),
        }
    }

    fn gen_assign(&mut self, loc: CLoc, val: CTerm) -> Result<CTerm, String> {
        match loc {
            CLoc::Var(l) => Ok(self
                .circ
                .assign(l, Val::Term(val.clone()))
                .map_err(|e| format!("{}", e))?
                .unwrap_term()),
            CLoc::Idx(l, idx) => {
                let old_inner: CTerm = match *l.clone() {
                    CLoc::Var(inner_loc) => {
                        let base = self
                            .circ
                            .get_value(inner_loc.clone())
                            .map_err(|e| format!("{}", e))?
                            .unwrap_term();
                        base
                    }
                    CLoc::Member(inner_loc, field) => {
                        let base = self
                            .circ
                            .get_value(inner_loc.loc().clone())
                            .map_err(|e| format!("{}", e))?
                            .unwrap_term();
                        self.field_select(&base, &field).unwrap()
                    }
                    CLoc::Idx(inner_loc, idx) => {
                        let base = self
                            .circ
                            .get_value(inner_loc.loc().clone())
                            .map_err(|e| format!("{}", e))?
                            .unwrap_term();
                        self.array_select(base.clone(), idx.clone()).unwrap()
                    }
                };
                self.array_store(old_inner, idx, val)

                // println!("in index!!");
                // let inner_loc = &*l.loc();
                // println!("inner loc: {:#?}", inner_loc);
                // let base = self
                //     .circ
                //     .get_value(inner_loc.clone())
                //     .map_err(|e| format!("{}", e))?
                //     .unwrap_term();
                // println!("base: {:#?}", base);
                // println!("getting old value rip");
                // let old_inner = self.array_select(base.clone(), idx.clone())?;
                // println!("after array select");
                // let new_inner = self.rebuild_lval(old_inner.clone(), *l.clone(), val)?;
            }
            CLoc::Member(l, field) => {
                let inner_loc = &*l.loc();
                let base = self
                    .circ
                    .get_value(inner_loc.clone())
                    .map_err(|e| format!("{}", e))?
                    .unwrap_term();
                let old_inner = self.field_select(&base, &field)?;
                let new_inner = self.rebuild_lval(old_inner, *l.clone(), val)?;
                let res = self.field_store(base, &field, new_inner);
                Ok(self
                    .circ
                    .assign(inner_loc.clone(), Val::Term(res.unwrap().clone()))
                    .map_err(|e| format!("{}", e))?
                    .unwrap_term())
            }
        }
    }

    fn fold_(&mut self, expr: CTerm) -> i32 {
        let term_ = fold(&expr.term.term(&self.circ.cir_ctx()));
        let cterm_ = cterm(CTermData::CInt(true, 32, term_));
        let val = const_int(cterm_).ok().unwrap();
        val.to_i32().unwrap()
    }

    fn const_(&self, c: Constant) -> CTerm {
        match c {
            // TODO: move const integer function out to separate function
            Constant::Integer(i) => cterm(CTermData::CInt(
                true,
                32,
                bv_lit(i.number.parse::<i32>().unwrap(), 32),
            )),
            _ => unimplemented!("Constant {:#?} hasn't been implemented", c),
        }
    }

    fn get_bin_op(&self, op: BinaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            BinaryOperator::Plus => add,
            BinaryOperator::AssignPlus => add,
            BinaryOperator::AssignDivide => div,
            BinaryOperator::Minus => sub,
            BinaryOperator::Multiply => mul,
            BinaryOperator::Divide => div,
            BinaryOperator::Equals => eq,
            BinaryOperator::Greater => ugt,
            BinaryOperator::GreaterOrEqual => uge,
            BinaryOperator::Less => ult,
            BinaryOperator::LessOrEqual => ule,
            BinaryOperator::BitwiseAnd => bitand,
            BinaryOperator::BitwiseOr => bitor,
            BinaryOperator::BitwiseXor => bitxor,
            BinaryOperator::LogicalAnd => and,
            BinaryOperator::LogicalOr => or,
            BinaryOperator::Modulo => rem,
            BinaryOperator::ShiftLeft => shl,
            BinaryOperator::ShiftRight => shr,
            _ => unimplemented!("BinaryOperator {:#?} hasn't been implemented", op),
        }
    }

    fn get_u_op(&self, op: UnaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            UnaryOperator::PostIncrement => add,
            _ => unimplemented!("UnaryOperator {:#?} hasn't been implemented", op),
        }
    }

    fn gen_expr(&mut self, expr: Expression) -> CTerm {
        let res = match expr.clone() {
            Expression::Identifier(node) => Ok(self
                .unwrap(self.circ.get_value(Loc::local(node.node.name.clone())))
                .unwrap_term()),
            Expression::Constant(node) => Ok(self.const_(node.node)),
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Assign => {
                        let loc = self.gen_lval(*bin_op.lhs);
                        let val = self.gen_expr(bin_op.rhs.node);
                        self.gen_assign(loc, val)
                    }
                    BinaryOperator::AssignPlus | BinaryOperator::AssignDivide => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let i = self.gen_expr(bin_op.lhs.node.clone());
                        let rhs = self.gen_expr(bin_op.rhs.node);
                        let loc = self.gen_lval(*bin_op.lhs);
                        let val = f(i, rhs).unwrap();
                        self.gen_assign(loc, val)
                    }
                    BinaryOperator::Index => {
                        let a = self.gen_expr(bin_op.lhs.node);
                        let b = self.gen_expr(bin_op.rhs.node);
                        self.array_select(a, b)
                    }
                    _ => {
                        let f = self.get_bin_op(bin_op.operator.node.clone());
                        let mut a = self.gen_expr(bin_op.lhs.node);
                        let mut b = self.gen_expr(bin_op.rhs.node);
                        // TODO: fix hack, const int check for shifting
                        if bin_op.operator.node == BinaryOperator::ShiftLeft
                            || bin_op.operator.node == BinaryOperator::ShiftRight
                        {
                            let a_t = fold(&a.term.term(&self.circ.cir_ctx()));
                            a = cterm(CTermData::CInt(true, 32, a_t));

                            let b_t = fold(&b.term.term(&self.circ.cir_ctx()));
                            b = cterm(CTermData::CInt(true, 32, b_t));
                        }
                        f(a, b)
                    }
                }
            }
            Expression::UnaryOperator(node) => {
                let u_op = node.node;
                match u_op.operator.node {
                    UnaryOperator::PostIncrement => {
                        let f = self.get_u_op(u_op.operator.node);
                        let i = self.gen_expr(u_op.operand.node.clone());
                        let one = cterm(CTermData::CInt(true, 32, bv_lit(1, 32)));
                        let loc = self.gen_lval(*u_op.operand);
                        let val = f(i, one).unwrap();
                        self.gen_assign(loc, val)
                    }
                    _ => unimplemented!("UnaryOperator {:#?} hasn't been implemented", u_op),
                }
            }
            Expression::Cast(node) => {
                let CastExpression {
                    type_name,
                    expression,
                } = node.node;
                let to_ty = self.s_type_(type_name.node.specifiers);
                let expr = self.gen_expr(expression.node);
                Ok(cast(to_ty, expr))
            }
            Expression::Call(node) => {
                let CallExpression { callee, arguments } = node.node;
                let fname = name_from_expr(*callee);

                let f = self
                    .functions
                    .get(&fname)
                    .unwrap_or_else(|| panic!("No function '{}'", fname))
                    .clone();

                let FnInfo {
                    name,
                    ret_ty,
                    args: parameters,
                    body,
                } = f;

                // Add parameters
                let args = arguments
                    .iter()
                    .map(|e| self.gen_expr(e.node.clone()))
                    .collect::<Vec<_>>();

                // setup stack frame for entry function
                self.circ.enter_fn(name, ret_ty.clone());
                assert_eq!(parameters.len(), args.len());

                for (p, a) in parameters.iter().zip(args) {
                    let param_info = self.get_param_info(p.clone(), false);
                    let r = self.circ.declare_init(
                        param_info.name.clone(),
                        param_info.ty,
                        Val::Term(a),
                    );
                    self.unwrap(r);
                }

                // println!("body: {:#?}", body.clone());

                self.gen_stmt(body);

                let ret = self
                    .circ
                    .exit_fn()
                    .map(|a| a.unwrap_term())
                    .unwrap_or_else(|| cterm(CTermData::CBool(bool_lit(false))));

                match ret_ty {
                    None => Ok(ret),
                    _ => Ok(cast(ret_ty, ret)),
                }
            }
            Expression::Member(member) => {
                let MemberExpression {
                    operator: _operator,
                    expression,
                    identifier,
                } = member.node;
                let base = self.gen_expr(expression.node);
                let field = identifier.node.name;
                self.field_select(&base, &field)
            }
            _ => unimplemented!("Expr {:#?} hasn't been implemented", expr),
        };
        self.unwrap(res)
    }

    fn gen_init(&mut self, derived_ty: Ty, init: Initializer) -> CTerm {
        println!("init: {:#?}", init);
        println!("derived ty: {}", derived_ty);
        match init {
            Initializer::Expression(e) => self.gen_expr(e.node),
            Initializer::List(l) => match derived_ty.clone() {
                Ty::Array(n, _) => {
                    let mut values: Vec<CTerm> = Vec::new();
                    let inner_type = derived_ty.inner_ty();
                    println!("inner type: {}", inner_type);
                    for li in l {
                        let expr =
                            self.gen_init(inner_type.clone(), li.node.initializer.node.clone());
                        println!("expr: {:#?}", expr);
                        values.push(expr)
                    }
                    println!("values len: {:#?}", values.len());
                    println!("values: {:#?}", values[0]);
                    assert!(n == values.len());
                    let id = self
                        .circ
                        .zero_allocate(values.len(), 32, inner_type.num_bits());

                    for (i, v) in values.iter().enumerate() {
                        println!("i: {}, v: {:#?}", i, v);
                        let offset = bv_lit(i, 32);
                        println!("offset: {:#?}", offset);
                        let v_ = v.term.term(&self.circ.cir_ctx());
                        println!("v_: {:#?}", v_);
                        self.circ.store(id, offset, v_);
                    }
                    cterm(CTermData::CArray(inner_type, Some(id)))
                }
                Ty::Struct(_base, fs) => {
                    assert!(fs.clone().len() == l.len());
                    derived_ty.default(&mut self.circ)
                }
                _ => unreachable!("Initializer list for non-list type: {:#?}", l),
            },
        }
    }

    fn gen_decl(&mut self, decl: Declaration) -> Vec<CTerm> {
        let decl_infos = self.get_decl_info(decl.clone());
        let mut exprs: Vec<CTerm> = Vec::new();
        for (d, info) in decl.declarators.iter().zip(decl_infos.iter()) {
            let expr: CTerm;
            if let Some(init) = d.node.initializer.clone() {
                println!("HERE! {:#?}", decl);
                expr = self.gen_init(info.ty.clone(), init.node);
            } else {
                expr = info.ty.default(&mut self.circ)
            }
            let res = self.circ.declare_init(
                info.name.clone(),
                info.ty.clone(),
                Val::Term(cast(Some(info.ty.clone()), expr.clone())),
            );
            self.unwrap(res);
            exprs.push(expr);
        }
        exprs
    }

    //TODO: This function is not quite right because the loop body could modify the iteration variable.
    fn get_const_iters(&mut self, for_stmt: ForStatement) -> ConstIteration {
        let init: Option<ConstIteration> = match for_stmt.initializer.node {
            ForInitializer::Declaration(d) => {
                // TODO: need to identify which is the looping variable
                let exprs = self.gen_decl(d.node);
                assert!(exprs.len() == 1);
                let val = self.fold_(exprs[0].clone());
                Some(ConstIteration { val })
            }
            ForInitializer::Expression(e) => {
                if let Expression::BinaryOperator(_) = e.node {
                    let expr = self.gen_expr(e.node);
                    let val = self.fold_(expr);
                    Some(ConstIteration { val })
                } else {
                    None
                }
            }
            _ => None,
        };

        let cond: Option<ConstIteration> = match for_stmt.condition.unwrap().node {
            Expression::BinaryOperator(bin_op) => {
                let expr = self.gen_expr(bin_op.node.rhs.node);
                let val = self.fold_(expr);
                match bin_op.node.operator.node {
                    BinaryOperator::Less => Some(ConstIteration { val }),
                    BinaryOperator::LessOrEqual => Some(ConstIteration { val: val + 1 }),
                    _ => None,
                }
            }
            _ => None,
        };

        let step: Option<ConstIteration> = match for_stmt.step.unwrap().node {
            Expression::UnaryOperator(u_op) => match u_op.node.operator.node {
                UnaryOperator::PostIncrement | UnaryOperator::PreIncrement => {
                    Some(ConstIteration { val: 1 })
                }
                _ => None,
            },
            Expression::BinaryOperator(bin_op) => match bin_op.node.operator.node {
                BinaryOperator::AssignPlus => {
                    let expr = self.gen_expr(bin_op.node.rhs.node);
                    let val = self.fold_(expr);
                    Some(ConstIteration { val })
                }
                _ => None,
            },
            _ => None,
        };

        // TODO: error checking here
        let init_ = init.unwrap();
        let cond_ = cond.unwrap();
        let incr_ = step.unwrap();

        let start = init_.val;
        let end = cond_.val;
        let incr = incr_.val;

        ConstIteration {
            val: ((end - start - 1) / incr) + 1,
        }
    }

    fn gen_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Compound(nodes) => {
                for node in nodes {
                    match node.node {
                        BlockItem::Declaration(decl) => {
                            self.gen_decl(decl.node);
                        }
                        BlockItem::Statement(stmt) => {
                            self.gen_stmt(stmt.node);
                        }
                        BlockItem::StaticAssert(_sa) => {
                            unimplemented!("Static Assert not supported yet")
                        }
                    }
                }
            }
            Statement::If(node) => {
                let cond = self.gen_expr(node.node.condition.node);
                let t_res = self
                    .circ
                    .enter_condition(cond.term.term(&self.circ.cir_ctx()));
                self.unwrap(t_res);
                self.gen_stmt(node.node.then_statement.node);
                self.circ.exit_condition();
                if let Some(f_cond) = node.node.else_statement {
                    let f_res = self
                        .circ
                        .enter_condition(term!(Op::Not; cond.term.term(&self.circ.cir_ctx())));
                    self.unwrap(f_res);
                    self.gen_stmt(f_cond.node);
                    self.circ.exit_condition();
                }
            }
            Statement::Return(ret) => {
                match ret {
                    Some(expr) => {
                        let ret = self.gen_expr(expr.node);
                        let ret_res = self.circ.return_(Some(ret));
                        self.unwrap(ret_res);
                    }
                    None => {
                        let ret_res = self.circ.return_(None);
                        self.unwrap(ret_res);
                    }
                };
            }

            Statement::Expression(expr) => {
                let e = expr.unwrap().node;
                self.gen_expr(e);
            }
            Statement::For(for_stmt) => {
                // TODO: Add enter_breakable
                self.circ.enter_scope();
                let const_iters = self.get_const_iters(for_stmt.node.clone());
                // TODO: Loop 5 times if const not specified
                let bound = const_iters.val;

                for _ in 0..bound {
                    self.circ.enter_scope();
                    self.gen_stmt(for_stmt.node.statement.node.clone());
                    self.circ.exit_scope();
                    self.gen_expr(for_stmt.node.step.as_ref().unwrap().node.clone());
                }
                self.circ.exit_scope();
            }
            _ => unimplemented!("Statement {:#?} hasn't been implemented", stmt),
        }
    }

    fn entry_fn(&mut self, n: &str) {
        debug!("Entry: {}", n);
        // find the entry function
        let f = self
            .functions
            .get(n)
            .unwrap_or_else(|| panic!("No function '{}'", n))
            .clone();

        // setup stack frame for entry function
        self.circ.enter_fn(f.name.to_owned(), f.ret_ty.clone());

        for arg in f.args.iter() {
            let param_info = self.get_param_info(arg.clone(), true);
            let r = self.circ.declare(
                param_info.name.clone(),
                &param_info.ty,
                true,
                param_info.vis,
            );
            self.unwrap(r);
        }

        self.gen_stmt(f.body.clone());
        if let Some(r) = self.circ.exit_fn() {
            match self.mode {
                Mode::Mpc(_) => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.term.terms(&self.circ.cir_ctx());
                    self.circ
                        .cir_ctx()
                        .cs
                        .borrow_mut()
                        .outputs
                        .extend(ret_terms);
                }
                Mode::Proof => {
                    let ty = f.ret_ty.as_ref().unwrap();
                    let name = "return".to_owned();
                    let term = r.unwrap_term();
                    let _r = self.circ.declare(name.clone(), ty, false, PROVER_VIS);
                    self.circ.assign_with_assertions(name, term, ty, PUBLIC_VIS);
                    unimplemented!();
                }
                _ => unimplemented!("Mode: {}", self.mode),
            }
        }
    }

    fn visit_files(&mut self) {
        let TranslationUnit(nodes) = self.tu.clone();
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    self.gen_decl(decl.node.clone());
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    let fn_info = self.get_fn_info(&fn_def.node);
                    let fname = fn_info.name.clone();
                    self.functions.insert(fname, fn_info);
                }
                _ => unimplemented!("Haven't implemented node: {:?}", n.node),
            };
        }
    }
}
