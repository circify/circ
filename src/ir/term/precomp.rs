//! Non-cryptographic pre-computation.
//!
//! Conceptually, this machinery allows a party with input material for one computation to map it
//! into input material for another computation.

use fxhash::{FxHashMap, FxHashSet};

use crate::ir::term::*;

use log::trace;

use std::cell::RefCell;

/// A "precomputation".
///
/// Expresses a computation to be run in advance by a single party.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreComp {
    #[serde(with = "crate::ir::term::serde_mods::map")]
    /// A map from output names to the terms that compute them.
    pub outputs: FxHashMap<String, Term>,
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
    /// Overwrite a step
    pub fn change_output(&mut self, name: &str, value: Term) {
        *self.outputs.get_mut(name).unwrap() = value;
    }
    /// Retain only the parts of this precomputation that can be evaluated from
    /// the `known` inputs.
    pub fn restrict_to_inputs(&mut self, known: FxHashSet<String>) {
        let os = &mut self.outputs;
        let seq = &mut self.sequence;
        let o_tuple = term(Op::Tuple, os.values().cloned().collect());
        let to_remove = &mut TermSet::default();
        for t in PostOrderIter::new(o_tuple) {
            if let Op::Var(var) = &t.op() {
                if !known.contains(&*var.name) {
                    to_remove.insert(t);
                }
            } else if t.cs().iter().any(|c| to_remove.contains(c)) {
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
        let mut value_cache: TermMap<Value> = TermMap::default();
        let mut env = env.clone();
        // iterate over all terms, evaluating them using the cache.
        for (o_name, _o_sort) in &self.sequence {
            let o = self.outputs.get(o_name).unwrap();
            eval_cached(o, &env, &mut value_cache);
            let value = value_cache.get(o).unwrap().clone();
            trace!("pre {o_name} => {value}");
            env.insert(o_name.clone(), value);
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

    /// Visit all terms
    pub fn terms_postorder(&self) -> impl Iterator<Item = Term> {
        PostOrderIter::from_roots_and_skips(self.outputs.values().cloned(), Default::default())
    }

    /// Recompute the inputs.
    fn recompute_inputs(&mut self) {
        let mut inputs = FxHashSet::default();
        for t in PostOrderIter::new(self.tuple()) {
            if let Op::Var(var) = &t.op() {
                inputs.insert((var.name.to_string(), var.sort.clone()));
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

    /// Reduce the precomputation to a single, step-less map.
    pub fn flatten(&mut self) {
        let mut out: FxHashMap<String, Term> = Default::default();
        let mut cache: TermMap<Term> = Default::default();
        for (name, sort) in &self.sequence {
            let term = extras::substitute_cache(self.outputs.get(name).unwrap(), &mut cache);
            let var_term = var(name.clone(), sort.clone());
            out.insert(name.into(), term.clone());
            cache.insert(var_term, term);
        }
        self.outputs = out;
    }

    /// Compute a topo order
    pub fn topo_order(&self) -> FxHashMap<String, usize> {
        let mut order: FxHashMap<String, usize> = FxHashMap::default();
        let mut stack: Vec<Term> = self
            .outputs
            .iter()
            .map(|(name, t)| var(name.clone(), check(t)))
            .collect();
        let mut post_visited: TermSet = Default::default();
        let mut pre_visited: TermSet = Default::default();
        while let Some(t) = stack.pop() {
            if post_visited.contains(&t) {
                continue;
            }
            if pre_visited.insert(t.clone()) {
                // children not yet pushed
                stack.push(t.clone());
                if let Op::Var(var) = t.op() {
                    if let Some(c) = self.outputs.get(&*var.name) {
                        if !post_visited.contains(c) {
                            assert!(!pre_visited.contains(c), "loop on {} {}", c.id(), c);
                            stack.push(c.clone());
                        }
                    }
                } else {
                    for c in t.cs() {
                        if !post_visited.contains(c) {
                            assert!(!pre_visited.contains(c), "loop on {} {}", c.id(), c);
                            stack.push(c.clone());
                        }
                    }
                }
            } else {
                post_visited.insert(t.clone());
                if let Op::Var(var) = t.op() {
                    order.insert(var.name.to_string(), order.len());
                }
            }
        }
        order
    }

    /// Put the outputs back into a topo order
    pub fn reorder(&mut self) {
        let order = self.topo_order();
        self.sequence
            .sort_by_cached_key(|(name, _sort)| order.get(name).unwrap());
        trace!("{}", text::serialize_precompute(self));
        #[cfg(debug_assertions)]
        self.check_topo_order();
    }

    #[allow(dead_code)]
    /// Check that no variables is used before defintion.
    pub fn check_topo_order(&self) {
        let defined: TermSet = self
            .sequence
            .iter()
            .map(|(n, s)| var(n.clone(), s.clone()))
            .collect();
        let seen = RefCell::new(TermSet::default());
        for (name, sort) in &self.inputs {
            seen.borrow_mut().insert(var(name.clone(), sort.clone()));
        }
        for (name, sort) in &self.sequence {
            let t = self.outputs.get(name).unwrap();
            for desc in extras::PostOrderSkipIter::new(t.clone(), &|n| seen.borrow().contains(n)) {
                if desc.is_var() && defined.contains(&desc) {
                    // we haven't seen this, or it would have been skipped.
                    panic!("variable {} used before definition", desc);
                }
                seen.borrow_mut().insert(desc);
            }
            seen.borrow_mut().insert(var(name.clone(), sort.clone()));
        }
    }

    /// Check that a topo-order exists
    #[allow(dead_code)]
    pub fn check_topo_orderable(&self) {
        let mut stack: Vec<Term> = self
            .outputs
            .iter()
            .map(|(name, t)| var(name.clone(), check(t)))
            .collect();
        let mut post_visited: TermSet = Default::default();
        let mut pre_visited: TermSet = Default::default();
        while let Some(t) = stack.pop() {
            if post_visited.contains(&t) {
                continue;
            }
            if pre_visited.insert(t.clone()) {
                // children not yet pushed
                stack.push(t.clone());
                if let Op::Var(var) = t.op() {
                    if let Some(c) = self.outputs.get(&*var.name) {
                        if !post_visited.contains(c) {
                            assert!(!pre_visited.contains(c), "loop on {} {}", c.id(), c);
                            stack.push(c.clone());
                        }
                    }
                } else {
                    for c in t.cs() {
                        if !post_visited.contains(c) {
                            assert!(!pre_visited.contains(c), "loop on {} {}", c.id(), c);
                            stack.push(c.clone());
                        }
                    }
                }
            } else {
                post_visited.insert(t.clone());
            }
        }
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
