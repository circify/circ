//! Input language front-ends

#[cfg(feature = "c")]
pub mod c;
pub mod datalog;
#[cfg(all(feature = "smt", feature = "zok"))]
pub mod zsharp;

use crate::ir::{
    proof,
    term::{PartyId, Sort},
};

use super::ir::term::Computation;
use lazy_static::lazy_static;
use rug::Integer;
use std::{
    fmt::{self, Display, Formatter},
    sync::Arc,
};

/// The prover visibility
pub const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
/// Public visibility
pub const PUBLIC_VIS: Option<PartyId> = None;

// The modulus for Z#.
// TODO: handle this better!
#[cfg(feature = "bls12381")]
lazy_static! {
    /// The modulus for Z#
    pub static ref ZSHARP_MODULUS: Integer = Integer::from_str_radix(
        "52435875175126190479447740508185965837690552500527637822603658699938581184513", // BLS12-381 group order
        10
    )
    .unwrap();
}

#[cfg(not(feature = "bls12381"))]
lazy_static! {
    /// The modulus for Z#
    pub static ref ZSHARP_MODULUS: Integer = Integer::from_str_radix(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617", // BN-254 group order
        10
    )
    .unwrap();
}

lazy_static! {
    /// The modulus for Z#, as an ARC
    pub static ref ZSHARP_MODULUS_ARC: Arc<Integer> = Arc::new(ZSHARP_MODULUS.clone());
    /// The modulus for Z#, as an IR sort
    pub static ref ZSHARP_FIELD_SORT: Sort = Sort::Field(ZSHARP_MODULUS_ARC.clone());
}

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
