//! Non-cryptographic pre-computation.
//!
//! Conceptually, this machinery allows a party with input material for one computation to map it
//! into input material for another computation.

use fxhash::{FxHashMap, FxHashSet};

use crate::ir::term::*;

/// A "precomputation".
///
/// Expresses a computation to be run in advance by a single party.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct PreComp {
    /// A map from output names to the terms that compute them.
    pub outputs: FxHashMap<String, Term>,
}

impl PreComp {
    /// Create a new precomputation
    pub fn new() -> Self {
        Self::default()
    }
    /// Add a new output variable to the precomputation. `value` is the term that computes its value.
    pub fn add_output(&mut self, name: String, value: Term) {
        let old = self.outputs.insert(name, value);
        assert!(old.is_none());
    }
    /// Evaluate the precomputation.
    ///
    /// Requires an input environment that binds all inputs for the underlying computation.
    pub fn eval(&self, env: &FxHashMap<String, Value>) -> FxHashMap<String, Value> {
        dbg!(self);
        dbg!(env);
        for k in env.keys() {
            if self.outputs.contains_key(k) {
                panic!("Input {} to the precomputation is also an output", k)
            }
        }
        let mut outputs = env.clone();
        let mut value_cache: TermMap<Value> = TermMap::new();
        // iterate over all terms, evaluating them using the cache.
        for o in self.outputs.values() {
            eval_cached(o, env, &mut value_cache);
        }
        outputs.extend(
        self.outputs
            .iter()
            .map(|(name, term)| (name.clone(), value_cache.get(term).unwrap().clone())));
        outputs
    }
    /// Compute the inputs for this precomputation
    pub fn inputs_to_terms(&self) -> FxHashMap<String, Term> {
        PostOrderIter::new(term(Op::Tuple, self.outputs.values().cloned().collect()))
            .filter_map(|t| match &t.op {
                Op::Var(name, _) => Some((name.clone(), t.clone())),
                _ => None,
            })
            .collect()
    }

    /// Compute the inputs for this precomputation
    pub fn inputs(&self) -> FxHashSet<String> {
        self.inputs_to_terms().into_keys().collect()
    }

    /// Bind the outputs of `self` to the inputs of `other`.
    pub fn sequential_compose(&self, other: &PreComp) -> PreComp {
        let self_outputs: FxHashSet<String> = self.outputs.keys().cloned().collect();
        let other_inputs: FxHashSet<String> = other.inputs();
        assert!(self_outputs.is_subset(&other_inputs),
            "Tried to compose two precomputations, but their interfaces did not match. The first computation had unmatched outputs\n{:?}", self_outputs.difference(&other_inputs).collect::<Vec<_>>());
        let other_inputs_to_terms: FxHashMap<String, Term> = other.inputs_to_terms();
        let mut sub_cache: TermMap<Term> = other_inputs_to_terms
            .into_iter()
            .filter_map(|(name, var_term)| {
                self.outputs.get(&name).map(|val| (var_term, val.clone()))
            })
            .collect();
        Self {
            outputs: other
                .outputs
                .iter()
                .map(|(name, term)| (name.clone(), extras::substitute_cache(term, &mut sub_cache)))
                .collect(),
        }
    }
}
