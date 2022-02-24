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
use crate::ir::opt::cfold::fold;
use crate::ir::proof::{self, ConstraintMetadata};
use crate::ir::term::*;
use lang_c::ast::*;
use lang_c::span::Node;
use log::debug;

use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;

/// The prover visibility
const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
/// Public visibility
const PUBLIC_VIS: Option<PartyId> = None;

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

enum CLoc {
    Var(Loc),
    Member(Box<CLoc>, String),
    Idx(Box<CLoc>, CTerm),
}

impl CLoc {
    fn loc(&self) -> &Loc {
        match self {
            CLoc::Var(l) => l,
            CLoc::Member(i, _) => i.loc(),
            CLoc::Idx(i, _) => i.loc(),
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

    pub fn field_select(&self, struct_: &CTerm, field: &str) -> Result<CTerm, String> {
        if let CTermData::CStruct(_, fs) = &struct_.term {
            if let Some((idx, term_)) = fs.search(field) {
                let struct_terms = struct_.term.terms(self.circ.cir_ctx());
                let field_term = term(Op::Field(idx), struct_terms);
                let res = match term_.term.type_() {
                    Ty::Bool => Ok(cterm(CTermData::CBool(field_term))),
                    Ty::Int(b, s) => Ok(cterm(CTermData::CInt(b, s, field_term))),
                    Ty::Array(_s, _t) => {
                        unimplemented!("array in structs not implemented yet")
                        // Ty::Array(s, t) => {
                        //     let expr =
                        //     Ok(cterm(CTermData::CArray(*t, term_)))
                        // },
                    }
                    Ty::Struct(_, _) => Ok(fs.search(field).unwrap().1.clone()),
                };
                return res;
            } else {
                return Err(format!("No field '{}'", field));
            }
        } else {
            return Err(format!("{} is not a struct", struct_));
        }
    }

    pub fn field_store(&self, struct_: CTerm, field: &str, val: CTerm) -> Result<CTerm, String> {
        if let CTermData::CStruct(struct_ty, fs) = &struct_.term {
            if let Some((idx, term_)) = fs.search(field) {
                //get term
                let struct_terms = term_.term.terms(self.circ.cir_ctx());
                let field_term = term(Op::Field(idx), struct_terms);

                //get val term
                let val_term = val.term.term(self.circ.cir_ctx());

                // term![Op::Update(idx); struct_.term.clone(), val.term],

                //update term
                let updated_term = term![Op::Update(idx); field_term, val_term];

                let updated_cterm = match &term_.term {
                    CTermData::CBool(_) => cterm(CTermData::CBool(updated_term)),
                    CTermData::CInt(b, s, _) => cterm(CTermData::CInt(*b, *s, updated_term)),
                    CTermData::CArray(_inner_ty, _alloc_id) => {
                        unimplemented!("array in structs not implemented yet")
                    }
                    CTermData::CStruct(inner_ty, inner_fs) => {
                        let mut inner_fs_clone = inner_fs.clone();
                        let updated_fs = inner_fs_clone.replace(field, val);
                        cterm(CTermData::CStruct(inner_ty.clone(), updated_fs.clone()))
                    }
                };
                println!("UPDATED CTERM: {:?}", updated_cterm);
                let mut fs_clone = fs.clone();
                let updated_fs = fs_clone.replace(field, updated_cterm);
                return Ok(cterm(CTermData::CStruct(
                    struct_ty.clone(),
                    updated_fs.clone(),
                )));
            } else {
                return Err(format!("No field '{}'", field));
            }
        } else {
            return Err(format!("{} is not a struct", struct_));
        }

        // match struct_.term.type_() {
        //     Ty::Struct(_, map) => {
        //         if let Some((idx, ty)) = map.search(field) {
        //             if ty == &val.term.type_() {

        //                 // term![Op::Update(idx); struct_.term.term(self.circ.cir_ctx()), val.term.term(self.circ.cir_ctx())],

        //                 // Ok(cterm(CTermData::CStruct(
        //                 //     struct_.term.type_().clone(),
        //                 //     fs
        //                 // )))
        //             } else {
        //                 Err(format!(
        //                     "term {} assigned to field {} of type {}",
        //                     val,
        //                     field,
        //                     map.get(idx).1
        //                 ))
        //             }
        //         } else {
        //             Err(format!("No field '{}'", field))
        //         }
        //     }
        //     a => Err(format!("{} is not a struct", a)),
        // }
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
            CLoc::Member(inner_loc, field) => {
                let old_inner = self.field_select(&base, &field)?;
                let new_inner = self.rebuild_lval(old_inner, *inner_loc, val)?;
                self.field_store(base, &field, new_inner)
            }
            CLoc::Idx(inner_loc, idx) => {
                let old_inner = self.array_select(base.clone(), idx.clone())?;
                let new_inner = self.rebuild_lval(old_inner, *inner_loc, val)?;
                self.array_store(base, idx, new_inner)
            }
        }
    }

    fn mod_lval(&mut self, l: CLoc, t: CTerm) -> Result<CTerm, String> {
        let var = l.loc().clone();
        let old = self
            .circ
            .get_value(var.clone())
            .map_err(|e| format!("{}", e))?
            .unwrap_term();

        match l {
            CLoc::Idx(_, offset) => self.array_store(old, offset, t),
            _ => {
                let res = self.rebuild_lval(old, l, t)?;
                Ok(self
                    .circ
                    .assign(var, Val::Term(res.clone()))
                    .map_err(|e| format!("{}", e))?
                    .unwrap_term())
            }
        }
    }

    fn lval(&mut self, expr: Node<Expression>) -> CLoc {
        match expr.node {
            Expression::Identifier(_) => {
                let base_name = name_from_expr(expr);
                CLoc::Var(Loc::local(base_name))
            }
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Index => {
                        let base_name = name_from_expr(*bin_op.lhs);
                        let idx = self.gen_expr(bin_op.rhs.node);
                        CLoc::Idx(Box::new(CLoc::Var(Loc::local(base_name))), idx)
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

    fn fold_(&mut self, expr: CTerm) -> i32 {
        let term_ = fold(&expr.term.term(&self.circ.cir_ctx()));
        let cterm_ = cterm(CTermData::CInt(true, 32, term_));
        println!("cterm: {:#?}", cterm_);
        let val = const_int(cterm_).ok().unwrap();
        val.to_i32().unwrap()
    }

    fn inner_derived_type_(&mut self, base_ty: Ty, d: DerivedDeclarator) -> Ty {
        match d {
            DerivedDeclarator::Array(arr) => {
                if let ArraySize::VariableExpression(expr) = &arr.node.size {
                    let expr_ = self.gen_expr(expr.node.clone());
                    println!("INNER DERIVE TYPE: {:#?}", expr_);
                    let size = self.fold_(expr_) as usize;
                    return Ty::Array(size, Box::new(base_ty));
                }
                Ty::Array(0, Box::new(base_ty))
            }
            DerivedDeclarator::Pointer(_ptr) => {
                unimplemented!("pointers not implemented yet");
            }
            _ => panic!("Not implemented: {:#?}", d),
        }
    }

    fn derived_type_(&mut self, base_ty: Ty, derived: Vec<Node<DerivedDeclarator>>) -> Ty {
        if derived.is_empty() {
            return base_ty;
        }
        let mut derived_ty = base_ty.clone();
        for d in derived {
            let next_ty = self.inner_derived_type_(base_ty.clone(), d.node.clone());
            match derived_ty {
                Ty::Array(s, _) => derived_ty = Ty::Array(s, Box::new(next_ty)),
                _ => derived_ty = next_ty,
            }
        }
        derived_ty
    }

    /// Interpret the party association of input parameters
    pub fn interpret_visibility(&mut self, ext: &DeclarationSpecifier) -> Option<PartyId> {
        if let DeclarationSpecifier::Extension(nodes) = ext {
            assert!(nodes.len() == 1);
            let node = nodes.first().unwrap();
            if let Extension::Attribute(attr) = &node.node {
                let name = &attr.name;
                return match name.node.as_str() {
                    "public" => PUBLIC_VIS,
                    "private" => match self.mode {
                        Mode::Mpc(n_parties) => {
                            assert!(attr.arguments.len() == 1);
                            let arg = attr.arguments.first().unwrap();
                            let cons = self.gen_expr(arg.node.clone());
                            let num_val = const_int(cons).ok()?;
                            if num_val <= n_parties {
                                Some(num_val.to_u8()?)
                            } else {
                                self.err(format!(
                                    "Party number {} greater than the number of parties ({})",
                                    num_val, n_parties
                                ))
                            }
                        }
                        Mode::Proof => PROVER_VIS,
                        _ => unimplemented!("Mode {} is not supported.", self.mode),
                    },
                    _ => panic!("Unknown visibility: {:#?}", name),
                };
            }
        }
        panic!("Bad visibility declaration.");
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
        println!("gen_expr: {:#?}", expr);
        let res = match expr.clone() {
            Expression::Identifier(node) => Ok(self
                .unwrap(self.circ.get_value(Loc::local(node.node.name.clone())))
                .unwrap_term()),
            Expression::Constant(node) => Ok(self.const_(node.node)),
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Assign => {
                        let e = self.gen_expr(bin_op.rhs.node);
                        let lval = self.lval(*bin_op.lhs);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
                    }
                    BinaryOperator::AssignPlus | BinaryOperator::AssignDivide => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let i = self.gen_expr(bin_op.lhs.node.clone());
                        let rhs = self.gen_expr(bin_op.rhs.node);
                        let e = f(i, rhs).unwrap();
                        let lval = self.lval(*bin_op.lhs);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
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
                        let e = f(i, one).unwrap();
                        let lval = self.lval(*u_op.operand);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
                    }
                    _ => unimplemented!("UnaryOperator {:#?} hasn't been implemented", u_op),
                }
            }
            Expression::Cast(node) => {
                let CastExpression {
                    type_name,
                    expression,
                } = node.node;
                let to_ty = s_type_(type_name.node.specifiers, &self.structs);
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
                    let base_ty = d_type_(p.specifiers.to_vec(), &self.structs);
                    let d = &p.declarator.as_ref().unwrap().node;
                    let derived_ty = self.derived_type_(base_ty.unwrap(), d.derived.to_vec());
                    let name = name_from_decl(d);
                    let d_res = self.circ.declare_init(name, derived_ty, Val::Term(a));
                    self.unwrap(d_res);
                }

                self.gen_stmt(body);

                let ret = self
                    .circ
                    .exit_fn()
                    .map(|a| a.unwrap_term())
                    .unwrap_or_else(|| cterm(CTermData::CBool(bool_lit(false))));
                Ok(cast(ret_ty, ret))
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
        match init {
            Initializer::Expression(e) => self.gen_expr(e.node),
            Initializer::List(l) => {
                match derived_ty.clone() {
                    Ty::Array(n, _) => {
                        let mut values: Vec<CTerm> = Vec::new();
                        let inner_type = derived_ty.inner_ty();
                        for li in l {
                            let expr =
                                self.gen_init(inner_type.clone(), li.node.initializer.node.clone());
                            values.push(expr)
                        }
                        assert!(n == values.len());
                        let id = self
                            .circ
                            .zero_allocate(values.len(), 32, inner_type.num_bits());

                        for (i, v) in values.iter().enumerate() {
                            let offset = bv_lit(i, 32);
                            let v_ = v.term.term(&self.circ.cir_ctx());
                            self.circ.store(id, offset, v_);
                        }
                        cterm(CTermData::CArray(inner_type, Some(id)))
                    }
                    Ty::Struct(_base, fs) => {
                        assert!(fs.clone().len() == l.len());

                        // initialize struct
                        let mut s = derived_ty.default();

                        // store fields in struct
                        for ((field, ty), li) in fs.fields().zip(l.iter()) {
                            let val = self.gen_init(ty.clone(), li.node.initializer.node.clone());
                            let res = self.field_store(s, &field, val);
                            s = res.unwrap();
                        }

                        // return struct
                        s
                    }
                    _ => unreachable!("Initializer list for non-list type: {:#?}", l),
                }
            }
        }
    }

    fn gen_decl(&mut self, decl: Declaration) -> Vec<CTerm> {
        let decl_infos = get_decl_info(decl.clone(), &mut self.structs);
        let mut exprs: Vec<CTerm> = Vec::new();
        for (d, info) in decl.declarators.iter().zip(decl_infos.iter()) {
            let base_ty: Ty = info.ty.clone();
            let derived = &d.node.declarator.node.derived;
            let derived_ty = self.derived_type_(base_ty, derived.to_vec());
            let expr: CTerm;
            if let Some(init) = d.node.initializer.clone() {
                expr = self.gen_init(derived_ty.clone(), init.node);
            } else {
                expr = match derived_ty {
                    Ty::Array(size, ref ty) => {
                        let id = self.circ.zero_allocate(size, 32, ty.num_bits());
                        cterm(CTermData::CArray(*ty.clone(), Some(id)))
                    }
                    _ => derived_ty.default(),
                }
            }
            let res = self.circ.declare_init(
                info.name.clone(),
                derived_ty.clone(),
                Val::Term(cast(Some(derived_ty), expr.clone())),
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
                if let Expression::BinaryOperator(bin_op) = e.node {
                    let expr = self.gen_expr(bin_op.node.rhs.node);
                    let val = self.fold_(expr);
                    // let ass_res = self.circ.assign(
                    //     Loc::local(name.clone()),
                    //     Val::Term(expr.clone()),
                    // );
                    // self.unwrap(ass_res);
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
                    println!("BEFORE FOLD {:#?}", expr);
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
            // TODO: self.gen_decl(arg);
            let p = &arg.specifiers[0];
            let vis = self.interpret_visibility(&p.node);
            let base_ty = d_type_(arg.specifiers[1..].to_vec(), &self.structs);
            let d = &arg.declarator.as_ref().unwrap().node;
            let derived_ty = self.derived_type_(base_ty.unwrap(), d.derived.to_vec());
            let name = name_from_decl(d);
            let r = self.circ.declare(name.clone(), &derived_ty, true, vis);
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
                    debug!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    let fn_info = ast_utils::get_fn_info(&fn_def.node, &self.structs);
                    let fname = fn_info.name.clone();
                    self.functions.insert(fname, fn_info);
                }
                _ => unimplemented!("Haven't implemented node: {:?}", n.node),
            };
        }
    }
}
