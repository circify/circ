//! The C front-end

mod ast_utils;
mod parser;
mod term;
mod types;

use super::FrontEnd;
use crate::circify::Circify;

use crate::front::c::term::*;
use crate::ir::proof;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;
use lang_c::ast::*;

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
        // g.circ.consume().borrow().clone()

        Computation {
            outputs: vec![],
            metadata: ComputationMetadata::default(),
            values: None,
        }
    }
}

struct CGen {
    circ: Circify<Ct>,
    mode: Mode,
    source: String,
    tu: TranslationUnit,
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

    fn get_bin_op(&self, op: BinaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            plus => add,
            _ => unimplemented!("BinaryOperator {:#?} hasn't been implemented", op),
        }
    }

    fn gen_expr(&self, expr: Expression) -> CTerm {
        let res = match expr.clone() {
            // Expression::Identifier(node) => {
            //     Ok(self.unwrap(self.circ.get_value(Loc::local(node.name.clone()))).unwrap_term()),
            // }
            Expression::BinaryOperator(node) => {
                let bin_expr = node.node;
                println!("{:#?}", bin_expr);
                let f = self.get_bin_op(bin_expr.operator.node);
                let a = self.gen_expr(bin_expr.lhs.node);
                let b = self.gen_expr(bin_expr.rhs.node);
                f(a, b)

                // println!("lhs: {:#?}", lhs);
                // println!("rhs: {:#?}", rhs);
            }
            _ => unimplemented!("Expr {:#?} hasn't been implemented", expr),
        };
        self.unwrap(res)
    }

    fn gen_stmt(&self, stmt: Statement) {
        match stmt {
            Statement::Compound(nodes) => {
                for node in nodes {
                    match node.node {
                        BlockItem::Declaration(_decl) => {
                            unimplemented!("Declaration not supported yet")
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
            Statement::Return(ret) => {
                match ret {
                    Some(expr) => {
                        self.gen_expr(expr.node);
                    }
                    None => {}
                };
            }
            Statement::Expression(expr) => {}
            _ => unimplemented!("Statement {:#?} hasn't been implemented", stmt),
        }
    }

    fn gen(&self) {
        let TranslationUnit(nodes) = &self.tu;
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    println!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    let fn_info = ast_utils::get_fn_info(&fn_def.node);
                    self.gen_stmt(fn_info.body.clone());
                    // println!("{}", fn_info);
                }
                _ => panic!("Haven't implemented node: {:?}", n.node),
            }
        }
    }
}
