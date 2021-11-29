//! Proof-system-specfic extensions to [crate::ir] types.

use super::term::*;
use fxhash::{FxHashMap, FxHashSet};
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
    fn from_constraint_system_parts(
        assertions: Vec<Term>,
        public_inputs: FxHashSet<String>,
        values: Option<FxHashMap<String, Value>>,
    ) -> Self;
}

impl Constraints for Computation {
    fn from_constraint_system_parts(
        assertions: Vec<Term>,
        public_inputs: FxHashSet<String>,
        values: Option<FxHashMap<String, Value>>,
    ) -> Self {
        let mut metadata = ComputationMetadata::default();
        let all_vars = {
            let mut set = FxHashSet::default();
            for a in &assertions {
                for t in PostOrderIter::new(a.clone()) {
                    match &t.op {
                        Op::Var(name, _) => {
                            set.insert(name.to_owned());
                        }
                        _ => {}
                    }
                }
            }
            set
        };
        for v in all_vars {
            if public_inputs.contains(&v) {
                metadata.new_input(v, None);
            } else {
                metadata.new_input(v, Some(PROVER_ID));
            }
        }
        Self {
            outputs: assertions,
            metadata,
            values,
        }
    }
}
