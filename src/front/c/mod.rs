//! The C front-end

mod ast_utils;
mod parser;
mod term;
mod types;

use super::FrontEnd;
use crate::circify::{Circify, Loc, Val};
use crate::circify::mem::MemManager;
use crate::front::c::ast_utils::*;
use crate::front::c::term::*;
use crate::front::c::types::*;
use crate::ir::opt::cfold::fold;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;
use lang_c::ast::*;
use lang_c::span::Node;
use log::debug;

// use std::collections::HashMap;
use std::cell::RefMut;
use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;

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

#[derive(Clone, Copy, Debug)]
/// Kind of circuit to generate. Effects privacy labels.
pub enum Mode {
    /// Generating an MPC circuit. Inputs are public or private (to a party in 1..N).
    Mpc(u8),
    /// Generating for a proof circuit. Inputs are public of private (to the prover).
    Proof,
    /// Generating for an optimization circuit. Inputs are existentially quantified.
    /// There should be only one output, which will be maximized.
    Opt,
}

impl Display for Mode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            &Mode::Mpc(n) => write!(f, "{}-pc", n),
            &Mode::Proof => write!(f, "proof"),
            &Mode::Opt => write!(f, "opt"),
        }
    }
}

/// The C front-end. Implements [FrontEnd].
pub struct C;

impl FrontEnd for C {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let parser = parser::CParser::new();
        let p = parser.parse_file(&i.file).unwrap();
        let mut g = CGen::new(i.inputs, i.mode, p.unit);
        g.gen();
        g.circ.consume().borrow().clone()
    }
}

struct CGen {
    circ: Circify<Ct>,
    mode: Mode,
    tu: TranslationUnit,
}

enum CLoc {
    Var(Loc),
    Idx(Box<CLoc>, CTerm),
}

impl CLoc {
    fn loc(&self) -> &Loc {
        match self {
            CLoc::Var(l) => l,
            CLoc::Idx(i, _) => i.loc(),
        }
    }
}

impl CGen {
    fn new(inputs: Option<PathBuf>, mode: Mode, tu: TranslationUnit) -> Self {
        let this = Self {
            circ: Circify::new(Ct::new(inputs.map(|i| parser::parse_inputs(i)))),
            mode,
            tu,
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

    fn get_mem(&self) -> RefMut<MemManager> {
        self.circ.cir_ctx().mem.borrow_mut()
    }

    fn array_select(&self, array: CTerm, idx: CTerm) -> Result<CTerm, String> {
        let mem = self.get_mem();
        match (array.clone().term, idx.term) {
            (CTermData::CArray(ty, id), CTermData::CInt(_, _, idx)) => {
                let i = id.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", array));
                Ok(CTerm {
                    term: match ty {
                        Ty::Bool => {
                            CTermData::CBool(mem.load(i, idx))
                        }
                        Ty::Int(s,w) => {
                            CTermData::CInt(s, w, mem.load(i, idx))
                        } 
                        // TODO: Flatten array so this case doesn't occur
                        // Ty::Array(_,t) => {
                        //     CTermData::CArray(*t, id)
                        // }
                        _ => unimplemented!()
                    }, 
                    udef: false,
                })  
            }
            (a, b) => Err(format!("[Array Select] cannot index {} by {}", b, a))
        }
    }

    pub fn array_store(&self, array: CTerm, idx: CTerm, val: CTerm) -> Result<CTerm, String> {
        match (array.clone().term, idx.term) {
            (CTermData::CArray(_, id), CTermData::CInt(_, _, idx_term)) => {
                let i = id.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", array.clone()));
                let mut mem = self.get_mem();
                let new_val = val.term.term(&mem);
                mem.store(i, idx_term, new_val);
                Ok(val.clone())
            }
            (a, b) => Err(format!("[Array Store] cannot index {} by {}", b, a)),
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
            CLoc::Var(_) => {
                self.circ
                    .assign(var, Val::Term(t.clone()))
                    .map_err(|e| format!("{}", e))
                    .map(|_| t)
            },
            CLoc::Idx(_, offset) => self.array_store(old, offset, t)
        }

    }

    fn lval(&mut self, expr: Box<Node<Expression>>) -> CLoc {
        match expr.node {
            Expression::Identifier(_) => {
                let base_name = name_from_ident(&expr.node);
                CLoc::Var(Loc::local(base_name))
            }
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Index => {
                        let base_name = name_from_ident(&bin_op.lhs.node);
                        let idx = self.gen_expr(bin_op.rhs.node);
                        CLoc::Idx(Box::new(CLoc::Var(Loc::local(base_name))), idx)
                    }
                    _ => unimplemented!("Invalid left hand value"),
                }
            }
            _ => unimplemented!("Invalid left hand value"),
        }
    }
    
    fn fold_(&mut self, expr: CTerm) -> i32 {
        let mem = self.get_mem();
        let term_ = fold(&expr.term.term(&mem));
        let cterm_ = CTerm {
            term: CTermData::CInt(true, 32, term_),
            udef: false,
        };
        let val = const_int(cterm_).ok().unwrap();
        val.to_i32().unwrap()
    }

    fn inner_derived_type_(&mut self, base_ty: Ty, d: DerivedDeclarator) -> Ty {
        match d {
            DerivedDeclarator::Array(arr) => {
                if let ArraySize::VariableExpression(expr) =
                    &arr.node.size
                {
                    let expr_ = self.gen_expr(expr.node.clone());
                    let size = self.fold_(expr_) as usize;
                    return Ty::Array(
                        Some(size),
                        Box::new(base_ty),
                    )
                } 
                return Ty::Array(
                    None,
                    Box::new(base_ty),
                )
            }
            DerivedDeclarator::Pointer(_ptr) => {
                unimplemented!("pointers not implemented yet");
            }
            _ => panic!("Not implemented: {:#?}", d),
        }
    }

    fn derived_type_(&mut self, base_ty: Ty, derived: Vec<Node<DerivedDeclarator>>) -> Ty {
        if derived.len() == 0 {
            return base_ty;
        }
        let mut derived_ty = base_ty.clone();
        for d in derived {
            let next_ty = self.inner_derived_type_(base_ty.clone(), d.node.clone());
            match derived_ty {
                Ty::Array(s,_) => {
                    derived_ty = Ty::Array(s, Box::new(next_ty))
                }
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
                    "public" => PUBLIC_VIS.clone(),
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
            Constant::Integer(i) => CTerm {
                term: CTermData::CInt(true, 32, bv_lit(i.number.parse::<i32>().unwrap(), 32)),
                udef: false,
            },
            _ => unimplemented!("Constant {:#?} hasn't been implemented", c),
        }
    }

    fn get_bin_op(&self, op: BinaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            BinaryOperator::Plus => add,
            BinaryOperator::AssignPlus => add,
            BinaryOperator::Minus => sub,
            BinaryOperator::Multiply => mul,
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
                        let e = self.gen_expr(bin_op.rhs.node);
                        let lval = self.lval(bin_op.lhs);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
                    } 
                    BinaryOperator::AssignPlus => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let i = self.gen_expr(bin_op.lhs.node.clone());
                        let rhs = self.gen_expr(bin_op.rhs.node);
                        let e = f(i, rhs).unwrap();
                        let lval = self.lval(bin_op.lhs);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
                    }
                    BinaryOperator::Index => {
                        let a = self.gen_expr(bin_op.lhs.node);
                        let b = self.gen_expr(bin_op.rhs.node);
                        self.array_select(a,b)
                    }
                    _ => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let a = self.gen_expr(bin_op.lhs.node);
                        let b = self.gen_expr(bin_op.rhs.node);
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
                        let one = CTerm {
                            term: CTermData::CInt(true, 32, bv_lit(1, 32)),
                            udef: false
                        };
                        let e = f(i, one).unwrap();
                        let lval = self.lval(u_op.operand);
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
                let to_ty = s_type_(type_name.node.specifiers);
                let expr = self.gen_expr(expression.node);
                Ok(cast(to_ty, expr))
            }
            _ => unimplemented!("Expr {:#?} hasn't been implemented", expr),
        };
        self.unwrap(res)
    }

    fn gen_init(&mut self, derived_ty: Ty, init: Initializer) -> CTerm {
        match init {
            Initializer::Expression(e) => self.gen_expr(e.node),
            Initializer::List(l) => {
                // TODO: check length of values to initialized number
                let mut values: Vec<CTerm> = Vec::new();
                let inner_type = inner_ty(derived_ty.clone());
                for li in l.clone() {
                    let expr = self.gen_init(inner_type.clone(), li.node.initializer.node.clone());
                    values.push(expr)
                }
                let mut mem = self.get_mem();
                let id = mem.zero_allocate(values.len(), 32, num_bits(inner_type.clone()));

                for (i,v) in values.iter().enumerate() {
                    let offset = bv_lit(i, 32);
                    let v_ = v.term.term(&mem);
                    mem.store(id, offset, v_);
                }

                CTerm {
                    term: CTermData::CArray(inner_type, Some(id)), 
                    udef: false,
                }
            }
        }
    }

    fn gen_decl(&mut self, decl: Declaration) -> CTerm {
        let decl_info = get_decl_info(decl.clone());
        let d = decl.declarators.first().unwrap().node.clone();
        let base_ty: Ty = decl_info.ty;
        let derived = &d.declarator.node.derived;
        let derived_ty = self.derived_type_(base_ty, derived.to_vec());
        let expr: CTerm;
        if let Some(init) = d.initializer {
            expr = self.gen_init(derived_ty.clone(), init.node);
        } else {
            expr = match derived_ty {
                // TODO: clean this up
                Ty::Array(size, ref ty) => {
                    let mut mem = self.get_mem();
                    let id = mem.zero_allocate(size.unwrap(), 32, num_bits(*ty.clone()));
                    CTerm {
                        term: CTermData::CArray(*ty.clone(), Some(id)), 
                        udef: false,
                    }
                }
                _ => derived_ty.default()
            }
        }

        let res = self.circ.declare_init(
            decl_info.name,
            derived_ty.clone(),
            Val::Term(cast(Some(derived_ty.clone()), expr.clone())),
        );
        self.unwrap(res);
        expr
    }

    fn get_const_iters(&mut self, for_stmt: ForStatement) -> Option<ConstIteration> {
        let init: Option<ConstIteration> = match for_stmt.initializer.node {
            ForInitializer::Declaration(d) => {
                let decl_info = get_decl_info(d.node.clone());
                let name = decl_info.name; 
                let expr = self.gen_decl(d.node.clone());
                let val = self.fold_(expr);
                Some(
                    ConstIteration {
                        name,
                        val
                    }
                )
            }
            ForInitializer::Expression(e) => {
                if let Expression::BinaryOperator(bin_op) = e.node {
                    let name = name_from_ident(&bin_op.node.lhs.node);
                    let expr = self.gen_expr(bin_op.node.rhs.node);
                    let val = self.fold_(expr);
                    return Some(
                        ConstIteration {
                            name,
                            val
                        }
                    );
                }
                None
            }
            _ => None
        };

        let cond: Option<ConstIteration> = match for_stmt.condition.unwrap().node {
            Expression::BinaryOperator(bin_op) => {
                let name = name_from_ident(&bin_op.node.lhs.node);
                let expr = self.gen_expr(bin_op.node.rhs.node);
                let val = self.fold_(expr);
                match bin_op.node.operator.node {
                    BinaryOperator::Less => {
                        Some(
                            ConstIteration {
                                name,
                                val: val,
                            }
                        )
                    } 
                    BinaryOperator::LessOrEqual => {
                        Some(
                            ConstIteration {
                                name,
                                val: val + 1,
                            }
                        )
                    }
                    _ => None
                }                        
            }
            _ => None
        };
        
        // TODO: add options for i += 1 
        let step: Option<ConstIteration> = match for_stmt.step.unwrap().node {
            Expression::UnaryOperator(u_op) => {
                let name = name_from_ident(&u_op.node.operand.node);
                match u_op.node.operator.node {
                    UnaryOperator::PostIncrement | UnaryOperator::PreIncrement => {
                        Some(
                            ConstIteration {
                                name,
                                val: 1,
                            }
                        )
                    }
                    _ => None
                }
            }
            _ => None
        };

        // TODO: error checking here
        let init_ = init.unwrap();
        let cond_ = cond.unwrap();
        let incr_ = step.unwrap();

        let init_name = init_.name;
        let start = init_.val;
        let cond_name = cond_.name;
        let end = cond_.val;
        let incr_name = incr_.name;
        let incr = incr_.val;

        if init_name == cond_name && cond_name == incr_name {
            return Some(
                ConstIteration {
                    name: init_name,
                    val: ((end - start - 1) / incr) + 1
                }
            );
        }
        None
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
                // TODO Cast to boolean for condition ;
                let t_term = cond.term.term(&self.get_mem());
                let t_res = self.circ.enter_condition(t_term);
                self.unwrap(t_res);
                self.gen_stmt(node.node.then_statement.node);
                self.circ.exit_condition();

                if let Some(f_cond) = node.node.else_statement {
                    let f_term = term!(Op::Not; cond.term.term(&self.get_mem()));
                    let f_res = self.circ.enter_condition(f_term);
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
                // TODO: Is this the right name?
                let const_iters = self.get_const_iters(for_stmt.node.clone());
                // Loop 5 times if const not specified
                let bound = const_iters.unwrap_or(ConstIteration {
                    name: "".to_string(),
                    val: 5
                }).val;

                for _ in 0..bound {
                    self.circ.enter_scope();
                    self.circ.enter_breakable("FOR_LOOP".to_string());

                    // TODO: something is wrong here.
                    self.gen_stmt(for_stmt.node.statement.node.clone());
                    self.gen_expr(for_stmt.node.step.as_ref().unwrap().node.clone());

                    self.circ.exit_breakable();
                    self.circ.exit_scope();
    
                }
            }
            _ => unimplemented!("Statement {:#?} hasn't been implemented", stmt),
        }
    }

    fn gen(&mut self) {
        let TranslationUnit(nodes) = self.tu.clone();
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    debug!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    debug!("{:#?}", fn_def.node.clone());
                    let fn_info = ast_utils::get_fn_info(&fn_def.node);
                    self.circ.enter_fn(fn_info.name.to_owned(), fn_info.ret_ty);
                    for arg in fn_info.args.iter() {
                        let p = &arg.specifiers[0];
                        let vis = self.interpret_visibility(&p.node);
                        let base_ty = d_type_(arg.specifiers[1..].to_vec());
                        let d = &arg.declarator.as_ref().unwrap().node;
                        let derived_ty = self.derived_type_(base_ty.unwrap(), d.derived.to_vec());
                        let name = name_from_decl(d);
                        let r = self.circ.declare(name.clone(), &derived_ty, true, vis);
                        self.unwrap(r);
                    }
                    self.gen_stmt(fn_info.body.clone());
                    if let Some(r) = self.circ.exit_fn() {
                        let ret_term = r.unwrap_term();
                        let ret_terms = ret_term.term.terms();
                        self.circ
                            .cir_ctx()
                            .cs
                            .borrow_mut()
                            .outputs
                            .extend(ret_terms);
                    }
                }
                _ => unimplemented!("Haven't implemented node: {:?}", n.node),
            }
        }
    }
}
