//! Input language front-ends

#[cfg(feature = "c")]
pub mod c;
pub mod datalog;
#[cfg(all(feature = "smt", feature = "zok"))]
pub mod zsharp;

use crate::ir::proof;
use crate::ir::term::{Computation, PartyId};

use std::fmt::{self, Display, Formatter};

/// The prover visibility
pub const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
/// Public visibility
pub const PUBLIC_VIS: Option<PartyId> = None;

/// A front-end
pub trait FrontEnd {
    /// Representation of an input program (possibly with argument assignments) for this language
    type Inputs;

    /// Compile the program (and possibly assignment) to constraints
    fn gen(i: Self::Inputs) -> Computation;
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
    /// Find inputs that yeild an output at least this large,
    /// and then prove knowledge of them.
    ProofOfHighValue(u64),
}

impl Display for Mode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Mode::Mpc(n) => write!(f, "{}-pc", n),
            Mode::Proof => write!(f, "proof"),
            Mode::Opt => write!(f, "opt"),
            Mode::ProofOfHighValue(v) => write!(f, "proof_of_high_value({})", v),
        }
    }
}
