//! Non-cryptographic pre-computation.
//!
//! Conceptually, this machinery allows a party with input material for one computation to map it
//! into input material for another computation.

// use std::time::Instant;

use std::{time::Instant};

use fxhash::{FxHashMap, FxHashSet};
use itertools::Itertools;
// use std::time::{Instant};

use crate::{ir::term::*, target::r1cs::R1cs};
use smallvec::SmallVec;

/// A "precomputation".
///
/// Expresses a computation to be run in advance by a single party.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreComp {
    /// A map from output names to the terms that compute them.
    pub outputs: FxHashMap<String, Term>,
    /// The sequence of output names
    pub sequence: Vec<String>,
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
    /// Add a new output variable to the precomputation. `value` is the term that computes its value.
    pub fn add_output(&mut self, name: String, value: Term) {
        self.sequence.push(name.clone());
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

        seq.retain(|s| {
            let o = os.get(s).unwrap();
            let drop = to_remove.contains(o);
            if drop {
                os.remove(s);
            }
            !drop
        });
    }

    /// transform Term to NumTerm
    pub fn transform_terms(
        &self,
        index_cache: &mut TermMap<usize>,
        term_arr: &mut Vec<NumTerm>,
    ) {

        for o_name in &self.sequence {
            let t = self.outputs.get(o_name).unwrap();
            let mut stack = vec![(false, t.clone())];
            while let Some((children_pushed, node)) = stack.pop() {
                if index_cache.contains_key(&node) {
                    continue;
                }
                if children_pushed {
                    let mut cs_arr = SmallVec::<[usize; 3]>::new();
                    for child in &node.cs {
                        cs_arr.push(*index_cache.get(child).unwrap());
                    }
                    let new_num_term = NumTerm {
                        op: NumOp::Op(node.op.clone()),
                        cs: cs_arr,
                    };
                    index_cache.insert(node, term_arr.len());
                    term_arr.push(new_num_term);
                } else {
                    stack.push((true, node.clone()));
                    for c in &node.cs {
                        if !index_cache.contains_key(c) {
                            stack.push((false, c.clone()));
                        }
                    }
                }
            }
        }
    }

    /// function
    pub fn eval(&self, env: &FxHashMap<String, Value>) -> FxHashMap<String, Value>{
        let mut value_cache: TermMap<Value> = TermMap::new();
        let mut env = env.clone();
        // iterate over all terms, evaluating them using the cache.
        for o_name in &self.sequence {
            let o = self.outputs.get(o_name).unwrap();
            eval_cached(o, &env, &mut value_cache);
            env.insert(o_name.clone(), value_cache.get(o).unwrap().clone());
        }
        env
    }

    /// eval preprocess
    pub fn eval_preprocess(
        &self,
        r1cs: &R1cs<String>,
    ) -> (Vec<NumTerm>, FxHashMap<String, usize>) {
        let mut term_arr = Vec::<NumTerm>::new();
        let mut index_cache = TermMap::<usize>::new();
        self.transform_terms(&mut index_cache, &mut term_arr);
        for term in &mut term_arr {
            if let NumOp::Op(op) = &term.op {
                if let Op::Var(o_name, _) = op {
                    if let Some(o) = self.outputs.get(o_name) {
                        let term_idx = *index_cache.get(o).unwrap();
                        term.op = NumOp::Var(term_idx);
                    }
                }
            } else {
                panic!("Op should not be transformed here!");
            }
        }
        let mut name_idxes = FxHashMap::default();
        for (_, name) in r1cs.idxs_signals.iter().sorted() {
            let o = self.outputs.get(name).unwrap();
            let term_idx = *index_cache.get(o).unwrap();
            name_idxes.insert(name.clone(), term_idx);
        }
        (term_arr, name_idxes)
    }

    /// real evaluation
    pub fn real_eval(name_idxes: &FxHashMap<String, usize>, term_arr: &Vec<NumTerm>, env: &FxHashMap<String, Value>) -> FxHashMap<String, Value> {
        let t1 = Instant::now();
        let mut val_arr = vec![Option::None; term_arr.len()];
        for term_idx in 0..term_arr.len() {
            eval_value_efficient(term_idx, term_arr, &mut val_arr, env);
        }
        println!("real eval take {}", t1.elapsed().as_millis());
        let mut map = FxHashMap::default();
        for (name, idx) in name_idxes {
            map.insert(name.clone(), val_arr[*idx].clone().unwrap());
        }
        println!("all eval take {}", t1.elapsed().as_millis());
        map
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
    pub fn sequential_compose(mut self, other: &PreComp) -> PreComp {
        for o_name in &other.sequence {
            let o = other.outputs.get(o_name).unwrap().clone();
            assert!(!self.outputs.contains_key(o_name));
            self.outputs.insert(o_name.clone(), o);
            self.sequence.push(o_name.clone());
        }
        self
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
        assert_eq!(p_with_a.sequence, vec!["out1"]);
        assert_eq!(p_with_a.outputs.len(), 1);

        let mut p_with_b = p.clone();
        p_with_b.restrict_to_inputs(vec!["b".into()].into_iter().collect());
        assert_eq!(p_with_b.sequence, vec!["out2"]);
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
