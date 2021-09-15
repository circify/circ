//! The C front-end

mod parser;
mod term;

use super::FrontEnd;
use crate::circify::{Circify, Loc, Val};
use crate::ir::proof::{self, ConstraintMetadata};
use crate::ir::term::*;
use lang_c::ast::{
    Declarator, DeclaratorKind,
    ExternalDeclaration, TranslationUnit, 
};
use lang_c::span::Node;
use lang_c::visit;
use lang_c::visit::Visit;
use log::debug;
// use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::path::{Path, PathBuf};

use term::*;

const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
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

pub struct C;

impl FrontEnd for C {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let parser = parser::CParser::new();
        let p = parser.parse_file(&i.file).unwrap();
        let mut g = CGen::new(p.source, p.unit, i.mode);
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
    source: String, 
    tu: TranslationUnit,
    mode: Mode,
}

impl CGen {
    fn new(source: String, tu: TranslationUnit, mode: Mode) -> Self {
        Self { source, tu, mode }
    }

    fn get_name(&self, dec: &Declarator) -> String {
        match dec.kind.node {
            DeclaratorKind::Identifier(ref id) => id.node.name.clone(),
            _ => panic!("Declarator Identified not found: {:?}", id.node),
        }
    }

    fn gen(&mut self) {
        let TranslationUnit(nodes) = &self.tu;
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    println!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    let fn_name = self.get_name(&fn_def.node.declarator.node);
                    let ret_ty = 
                }
                _ => panic!("Haven't implemented node: {:?}", n.node),
            }
        }
    }
}



