//! Input language front-ends

pub mod c;
pub mod datalog;
#[allow(clippy::all)]
pub mod zokrates;

use super::ir::term::Computation;
use std::fmt::{self, Display, Formatter};

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
