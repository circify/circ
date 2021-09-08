//! The C front-end

mod parser;
mod term;

use super::FrontEnd;
use crate::circify::{Circify, Loc, Val};
use crate::ir::proof::{self, ConstraintMetadata};
use crate::ir::term::*;
use std::fmt::{self, Display, Formatter};
use std::path::{Path, PathBuf};
use lang_c::driver::{Config, parse};

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
        

        let config = Config::default();
        println!("{:?}", parse(&config, i.file));

        // let mut g = CGen::new(i.inputs, asts, i.mode);
        // g.visit_files();
        // g.file_stack.push(i.file);
        // g.entry_fn("main");
        // g.file_stack.pop();
        // g.circ.consume().borrow().clone()

        Computation {
            outputs: vec![],
            metadata: ComputationMetadata::default(),
            values: None,
        }
    }
}


// struct CGen<'ast> {
//     circ: Circify<C>,
//     asts: HashMap<PathBuf, ast::File<'ast>>,
//     file_stack: Vec<PathBuf>,
//     functions: HashMap<(PathBuf, String), ast::Function<'ast>>,
//     import_map: HashMap<(PathBuf, String), (PathBuf, String)>,
//     mode: Mode,
// }

// impl<'ast> CGen<'ast> {
//     fn new(inputs: Option<PathBuf>, asts: HashMap<PathBuf, ast::File<'ast>>, mode: Mode) -> Self {
//         let this = Self {
//             circ: Circify::new(ZoKrates::new(inputs.map(|i| parser::parse_inputs(i)))),
//             asts,
//             stdlib: parser::ZStdLib::new(),
//             file_stack: vec![],
//             functions: HashMap::new(),
//             import_map: HashMap::new(),
//             mode,
//         };
//         this.circ
//             .cir_ctx()
//             .cs
//             .borrow_mut()
//             .metadata
//             .add_prover_and_verifier();
//         this
//     }

//     /// Unwrap a result with a span-dependent error
//     fn err<E: Display>(&self, e: E, s: &ast::Span) -> ! {
//         println!("Error: {}", e);
//         println!("In: {}", self.cur_path().display());
//         for l in s.lines() {
//             println!("  {}", l);
//         }
//         std::process::exit(1)
//     }
// }


