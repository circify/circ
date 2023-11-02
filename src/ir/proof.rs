//! Proof-system-specfic extensions to [crate::ir] types.
use fxhash::FxHashSet;

use super::term::*;

/// The prover's canonical party name
pub const PROVER_NAME: &str = "prover";
/// The verifier's canonical party name
pub const VERIFIER_NAME: &str = "verifier";
/// The prover's canonical party id
pub const PROVER_ID: PartyId = 0;
/// The verifier's canonical party id
pub const VERIFIER_ID: PartyId = 1;

/// Extra [ComputationMetadata] methods for proof systems
pub trait ConstraintMetadata {
    /// Add a prover and verifier party to this comptuation's metadata
    fn add_prover_and_verifier(&mut self);
}

impl ConstraintMetadata for ComputationMetadata {
    fn add_prover_and_verifier(&mut self) {
        assert_eq!(self.add_party(PROVER_NAME.into()), PROVER_ID);
        assert_eq!(self.add_party(VERIFIER_NAME.into()), VERIFIER_ID);
    }
}

/// Extra [Computation] methods for proof systems
pub trait Constraints {
    /// Build a [Computation] from assertions, a list of public inputs, and values
    fn from_constraint_system_parts(assertions: Vec<Term>, public_inputs: Vec<Term>) -> Self;
}

impl Constraints for Computation {
    fn from_constraint_system_parts(assertions: Vec<Term>, public_inputs: Vec<Term>) -> Self {
        let mut metadata = ComputationMetadata::default();
        let all_vars = {
            let mut set = FxHashSet::default();
            for a in &assertions {
                for t in PostOrderIter::new(a.clone()) {
                    if let Op::Var(..) = t.op() {
                        set.insert(t.clone());
                    }
                }
            }
            set
        };
        let public_inputs_set: FxHashSet<String> = public_inputs
            .iter()
            .filter_map(|t| {
                if let Op::Var(n, _) = &t.op() {
                    Some(n.clone())
                } else {
                    None
                }
            })
            .collect();

        for v in public_inputs {
            if let Op::Var(n, s) = &v.op() {
                metadata.new_input(n.to_owned(), None, s.clone());
            } else {
                panic!()
            }
        }
        for v in all_vars {
            if let Op::Var(n, s) = &v.op() {
                if !public_inputs_set.contains(n) {
                    metadata.new_input(n.to_owned(), Some(PROVER_ID), s.clone());
                }
            } else {
                panic!()
            }
        }
        Self {
            outputs: assertions,
            metadata,
            precomputes: Default::default(),
            persistent_arrays: Default::default(),
            ram_arrays: Default::default(),
        }
    }
}
