//! The C front-end

mod ast_utils;
mod parser;
mod term;
mod types;

use super::FrontEnd;
use crate::circify::{Circify, Loc, Val};
use crate::front::c::ast_utils::*;
use crate::front::c::term::*;
use crate::front::c::types::*;
use crate::ir::proof;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;
use lang_c::ast::*;
use lang_c::span::Node;
use log::debug;

// use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;

const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
const PUBLIC_VIS: Option<PartyId> = None;

/// Inputs to the C compiler
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,

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
        let mut g = CGen::new(i.inputs, i.mode, p.source, p.unit);
        g.gen();
        g.circ.consume().borrow().clone()
    }
}

struct CGen {
    circ: Circify<Ct>,
    mode: Mode,
    source: String,
    tu: TranslationUnit,
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

impl CGen {
    fn new(inputs: Option<PathBuf>, mode: Mode, source: String, tu: TranslationUnit) -> Self {
        let this = Self {
            circ: Circify::new(Ct::new(inputs.map(|i| parser::parse_inputs(i)))),
            mode,
            source,
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

    /// Unwrap a result with a span-dependent error
    fn err<E: Display>(&self, e: E) -> ! {
        println!("Error: {}", e);
        std::process::exit(1)
    }

    fn unwrap<CTerm, E: Display>(&self, r: Result<CTerm, E>) -> CTerm {
        r.unwrap_or_else(|e| self.err(e))
    }

    fn apply_lval_mod(&mut self, base: CTerm, loc: CLoc, val: CTerm) -> Result<CTerm, String> {
        match loc {
            CLoc::Var(_) => Ok(val),
            CLoc::Idx(inner_loc, idx) => {
                let old_inner = array_select(base.clone(), idx.clone())?;
                let new_inner = self.apply_lval_mod(old_inner, *inner_loc, val)?;
                array_store(base, idx, new_inner)
            }
            _ => unimplemented!("Have not implemented apply_lval_mod"),
        }
    }

    fn mod_lval(&mut self, l: CLoc, t: CTerm) -> Result<(), String> {
        let var = l.loc().clone();
        let old = self
            .circ
            .get_value(var.clone())
            .map_err(|e| format!("{}", e))?
            .unwrap_term();
        let new = self.apply_lval_mod(old, l, t)?;
        self.circ
            .assign(var, Val::Term(new))
            .map_err(|e| format!("{}", e))
            .map(|_| ())
    }

    fn lval(&mut self, expr: Box<Node<Expression>>) -> CLoc {
        match expr.node {
            Expression::Identifier(ref node) => {
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

    fn const_(&self, c: Constant) -> CTerm {
        match c {
            Constant::Integer(i) => CTerm {
                term: CTermData::CInt(32, bv_lit(i.number.parse::<i32>().unwrap(), 32)),
                udef: false,
            },
            _ => unimplemented!("Constant {:#?} hasn't been implemented", c),
        }
    }

    fn interpret_visibility(&mut self, ext: &DeclarationSpecifier) -> Option<PartyId> {
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

    fn get_bin_op(&self, op: BinaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            BinaryOperator::Plus => add,
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
            BinaryOperator::Index => array_select,
            _ => unimplemented!("BinaryOperator {:#?} hasn't been implemented", op),
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
                        println!("lhs: {:#?}", bin_op.lhs.node);
                        println!("rhs: {:#?}", bin_op.rhs.node);
                        let e = self.gen_expr(bin_op.rhs.node);
                        let lval = self.lval(bin_op.lhs);
                        let mod_res = self.mod_lval(lval, e.clone());
                        self.unwrap(mod_res);
                        Ok(e)
                    }
                    _ => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let a = self.gen_expr(bin_op.lhs.node);
                        let b = self.gen_expr(bin_op.rhs.node);
                        f(a, b)
                    }
                }
            }
            Expression::Cast(node) => {
                let CastExpression {
                    type_name,
                    expression,
                } = node.node;
                let to_ty = cast_type(type_name.node);
                let expr = self.gen_expr(expression.node);
                Ok(cast(to_ty, expr))
            }
            _ => unimplemented!("Expr {:#?} hasn't been implemented", expr),
        };
        self.unwrap(res)
    }

    fn gen_init(&mut self, init: Initializer) -> CTerm {
        match init {
            Initializer::Expression(e) => self.gen_expr(e.node),
            Initializer::List(l) => {
                let mut values: Vec<CTerm> = Vec::new();
                for li in l {
                    let expr = self.gen_init(li.node.initializer.node);
                    values.push(expr)
                }
                let arr = new_array(values);
                arr.unwrap()
            }
        }
    }

    fn gen_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Compound(nodes) => {
                for node in nodes {
                    match node.node {
                        BlockItem::Declaration(node) => {
                            let decl = node.node;
                            let decl_info = get_decl_info(decl.clone());

                            // get derived types
                            // Array, Pointer ...
                            let d = decl.declarators.first().unwrap().node.clone();
                            let derived = &d.declarator.node.derived;
                            let mut derived_ty: Ty = decl_info.ty;

                            if derived.len() != 0 {
                                for d in derived {
                                    match &d.node {
                                        DerivedDeclarator::Array(arr) => {
                                            let _quals = &arr.node.qualifiers;
                                            if let ArraySize::VariableExpression(size) =
                                                &arr.node.size
                                            {
                                                if let Expression::Constant(con) = &size.node {
                                                    if let Constant::Integer(i) = &con.node {
                                                        let len: usize =
                                                            i.number.parse::<usize>().unwrap();
                                                        match derived_ty {
                                                            Ty::Array(_, _) => {
                                                                derived_ty = Ty::Array(
                                                                    len,
                                                                    Box::new(derived_ty),
                                                                )
                                                            }
                                                            _ => {
                                                                derived_ty = Ty::Array(
                                                                    len,
                                                                    Box::new(derived_ty.clone()),
                                                                )
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                        DerivedDeclarator::Pointer(_ptr) => {
                                            unimplemented!("pointers not implemented yet");
                                        }
                                        _ => panic!("Not implemented: {:#?}", d),
                                    }
                                }
                            }
                            let expr: CTerm;
                            if let Some(init) = d.initializer {
                                expr = self.gen_init(init.node);
                            } else {
                                expr = derived_ty.default();
                            }

                            let res = self.circ.declare_init(
                                decl_info.name,
                                derived_ty.clone(),
                                Val::Term(cast(Some(derived_ty.clone()), expr)),
                            );
                            self.unwrap(res);
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
                // TODO Cast to boolean for condition;
                let t_res = self.circ.enter_condition(cond.term.term());
                self.unwrap(t_res);
                self.gen_stmt(node.node.then_statement.node);
                self.circ.exit_condition();

                if let Some(f_cond) = node.node.else_statement {
                    let f_res = self.circ.enter_condition(term!(Op::Not; cond.term.term()));
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
                // match e {
                //     Expression::BinaryOperator(node) => {
                //         match node.node {
                //             BinaryOperatorExpression{ operator, lhs, rhs } => {
                //                 debug!("op: {:#?}", operator);
                //                 debug!("lhs: {:#?}", lhs);
                //                 debug!("rhs: {:#?}", rhs);

                //                 println!("op: {:#?}", operator);
                //                 println!("lhs: {:#?}", lhs);
                //                 println!("rhs: {:#?}", rhs);
                //                 let l = self.gen_expr(lhs.node);
                //                 let r = self.gen_expr(rhs.node);

                //                 println!("l expr: {:#?}", l);
                //                 println!("r expr: {:#?}", r);

                //                 match operator.node {
                //                     // TODO: REVERSE SEARCH NAME FROM TERM IN CTX
                //                     // INDEX NEEDS TO STORE INTO CONTEXT
                //                     BinaryOperator::Assign => {
                //                         println!("L Type: {:#?}", l.term.type_());
                //                         println!("R Type: {:#?}", r.term.type_());

                //                         // let res = self.circ.assign(
                //                         //     Loc::local(name_from_lex(l.term.term().to_string())),
                //                         //     Val::Term(r)
                //                         // );
                //                         // self.unwrap(res);
                //                     }
                //                     _ => unimplemented!("Statement expression operator {:#?}", operator)
                //                 }
                //             }
                //         }
                //     }
                //     _ => unimplemented!("Statement expression {:#?} hasn't been implemented", e),
                // }
            }
            _ => unimplemented!("Statement {:#?} hasn't been implemented", stmt),
        }
    }

    fn gen(&mut self) {
        let TranslationUnit(nodes) = self.tu.clone();
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    println!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    // println!("{:#?}", fn_def.node.clone());
                    let fn_info = ast_utils::get_fn_info(&fn_def.node);
                    self.circ.enter_fn(fn_info.name.to_owned(), fn_info.ret_ty);
                    for arg in fn_info.args.iter() {
                        assert!(arg.specifiers.len() == 2);
                        let p = &arg.specifiers[0];
                        let vis = self.interpret_visibility(&p.node);
                        let t = &arg.specifiers[1];
                        let ty = type_(&t.node);
                        let d = &arg.declarator.as_ref().unwrap().node;
                        let name = name_from_decl(d);
                        let r = self.circ.declare(name.clone(), &ty.unwrap(), true, vis);
                        self.unwrap(r);
                    }
                    //TODO: move this out for just the main function as entry
                    println!("body: {:#?}", fn_info.body);
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
