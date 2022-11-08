//! Non-cryptographic pre-computation.
//!
//! Conceptually, this machinery allows a party with input material for one computation to map it
//! into input material for another computation.

use fxhash::{FxHashMap, FxHashSet};

use crate::ir::term::*;

/// A "precomputation".
///
/// Expresses a computation to be run in advance by a single party.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct PreComp {
    /// A map from output names to the terms that compute them.
    outputs: FxHashMap<String, Term>,
    sequence: Vec<(String, Sort)>,
    inputs: FxHashSet<(String, Sort)>,
}

impl PreComp {
    /// Create a new precomputation
    pub fn new() -> Self {
        Self::default()
    }
    /// immutable access to the outputs
    pub fn outputs(&self) -> &FxHashMap<String, Term> {
        &self.outputs
    }
    /// immutable access to the outputs
    pub fn sequence(&self) -> &[(String, Sort)] {
        &self.sequence
    }
    /// immutable access to the outputs
    pub fn inputs(&self) -> &FxHashSet<(String, Sort)> {
        &self.inputs
    }
    /// Add an input
    pub fn add_input(&mut self, name: String, sort: Sort) {
        self.inputs.insert((name, sort));
    }
    /// Add a new output variable to the precomputation. `value` is the term that computes its value.
    pub fn add_output(&mut self, name: String, value: Term) {
        let sort = check(&value);
        self.sequence.push((name.clone(), sort));
        let old = self.outputs.insert(name, value);
        assert!(old.is_none());
    }
    /// Retain only the parts of this precomputation that can be evaluated from
    /// the `known` inputs.
    pub fn restrict_to_inputs(&mut self, known: FxHashSet<String>) {
        let os = &mut self.outputs;
        let seq = &mut self.sequence;
        let o_tuple = term(Op::Tuple, os.values().cloned().collect());
        let to_remove = &mut TermSet::new();
        for t in PostOrderIter::new(o_tuple) {
            if let Op::Var(ref name, _) = &t.op {
                if !known.contains(name) {
                    to_remove.insert(t);
                }
            } else if t.cs.iter().any(|c| to_remove.contains(c)) {
                to_remove.insert(t);
            }
        }

        seq.retain(|(name, _sort)| {
            let o = os.get(name).unwrap();
            let drop = to_remove.contains(o);
            if drop {
                os.remove(name);
            }
            !drop
        });
    }

    /// Evaluate the precomputation.
    ///
    /// Requires an input environment that binds all inputs for the underlying computation.
    pub fn eval(&self, env: &FxHashMap<String, Value>) -> FxHashMap<String, Value> {
        let mut value_cache: TermMap<Value> = TermMap::new();
        let mut env = env.clone();
        // iterate over all terms, evaluating them using the cache.
        for (o_name, _o_sort) in &self.sequence {
            let o = self.outputs.get(o_name).unwrap();
            eval_cached(o, &env, &mut value_cache);
            env.insert(o_name.clone(), value_cache.get(o).unwrap().clone());
        }
        env
    }

    /// Get all outputs, in seqence, as a tuple
    pub fn tuple(&self) -> Term {
        term(
            Op::Tuple,
            self.sequence
                .iter()
                .map(|o| self.outputs.get(&o.0).unwrap())
                .cloned()
                .collect(),
        )
    }

    /// Recompute the inputs.
    fn recompute_inputs(&mut self) {
        let mut inputs = FxHashSet::default();
        for t in PostOrderIter::new(self.tuple()) {
            if let Op::Var(name, sort) = &t.op {
                inputs.insert((name.clone(), sort.clone()));
            }
        }
        self.inputs = inputs;
    }

    /// Bind the outputs of `self` to the inputs of `other`.
    pub fn sequential_compose(mut self, other: &PreComp) -> PreComp {
        for (o_name, o_sort) in &other.sequence {
            let o = other.outputs.get(o_name).unwrap().clone();
            assert!(!self.outputs.contains_key(o_name));
            self.outputs.insert(o_name.clone(), o);
            self.sequence.push((o_name.clone(), o_sort.clone()));
        }
        self.recompute_inputs();
        self
    }
}

impl Serialize for PreComp {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let bytes = text::serialize_precompute(self);
        serializer.serialize_str(&bytes)
    }
}

struct PreCompDeserVisitor;

impl<'de> Visitor<'de> for PreCompDeserVisitor {
    type Value = PreComp;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "a string (that textually defines a term)")
    }

    fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
    where
        E: std::error::Error,
    {
        Ok(text::parse_precompute(v.as_bytes()))
    }
}

impl<'de> Deserialize<'de> for PreComp {
    fn deserialize<D>(deserializer: D) -> Result<PreComp, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_str(PreCompDeserVisitor)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use text::parse_term;

    #[test]
    fn restrict_to_inputs() {
        let mut p = PreComp::new();
        p.add_output(
            "out0".into(),
            parse_term(b"(declare ((a bool) (b (bv 4))) (and a (= b #b0000)))"),
        );
        p.add_output(
            "out1".into(),
            parse_term(b"(declare ((a bool) (b (bv 4))) (xor a true))"),
        );
        p.add_output(
            "out2".into(),
            parse_term(b"(declare ((a bool) (b (bv 4))) (bvuge b #b1000))"),
        );

        let mut p_with_a = p.clone();
        p_with_a.restrict_to_inputs(vec!["a".into()].into_iter().collect());
        assert_eq!(
            p_with_a.sequence.iter().map(|(n, _)| n).collect::<Vec<_>>(),
            vec!["out1"]
        );
        assert_eq!(p_with_a.outputs.len(), 1);

        let mut p_with_b = p.clone();
        p_with_b.restrict_to_inputs(vec!["b".into()].into_iter().collect());
        assert_eq!(
            p_with_b.sequence.iter().map(|(n, _)| n).collect::<Vec<_>>(),
            vec!["out2"]
        );
        assert_eq!(p_with_b.outputs.len(), 1);

        let mut p_both = p.clone();
        p_both.restrict_to_inputs(vec!["a".into(), "b".into()].into_iter().collect());
        assert_eq!(p_both.sequence, p.sequence);
        assert_eq!(p_both.outputs.len(), 3);

        let mut p_extra = p.clone();
        p_extra.restrict_to_inputs(
            vec!["a".into(), "b".into(), "c".into()]
                .into_iter()
                .collect(),
        );
        assert_eq!(p_extra.sequence, p.sequence);
        assert_eq!(p_extra.outputs.len(), 3);
    }
}
