//! # Tuple elimination pass
//!
//! Elimates tuple-related terms.
//!
//! The idea is to do a bottom-up pass, in which all tuple's are lift to the top level, and then
//! then removed.
//!
//! ## Phase 1
//!
//! Phase 1 (lifting tuples) is defined by the following big-step rewrites.
//!
//! Notational conventions:
//! * lowercase letters are used to match sorts/terms before rewriting.
//! * uppercase letters denote their (big-step) rewritten counterparts.
//! * () denote AST structure
//! * [] denote repeated structures, i.e. like var-args.
//! * `f(x, *)` denotes a partial application of `f`, i.e. the function that sends `y` to `f(x,y)`.
//! * In the results of rewriting we often have terms which are tuples at the top-level. I.e. their
//!   sort contains no tuple sort that is not the child of a tuple sort. Similarly, the terms are
//!   tuples at the top-level: no field or update operators are present, and the only tuple
//!   operators are the children of other tuple operators.
//!   * Such sorts/terms can be viewed as structured collections of non-tuple elements, i.e., as
//!     functors whose pure elements are non-tuples.
//!   * The `map`, `bimap`, and `list` functions apply to those functors.
//!     * i.e., `map f (tuple x tuple y z))` is `(tuple (f x) (tuple (f y) (f z)))`.
//!     * i.e., `list (tuple x tuple y z))` is `(x y z)`
//!
//! Assumptions:
//! * We assume that array keys are of scalar sort
//! * We assume that variables are of scalar sort. See [super::scalarize_vars].
//! * We *do not* describe the pass as applied to constant values. That part of the pass is
//!   entirely analagous to terms.
//!
//! Sort rewrites:
//! * `(tuple [t_i]_i) -> (tuple [T_i]_i)`
//! * `(array k t) -> map (array k *) T
//!
//! Term rewrites:
//! * `(ite c t f) -> bimap (ite C * *) T F`
//! * `(eq c t f) -> (and (list (bimap (= * *) T F)))`
//! * `(tuple [t_i]_i) -> (tuple [T_i]_i)`
//! * `(field_j t) -> get T j`
//! * `(update_j t) -> update T j V`
//! * `(select a i) -> map (select * I) A`
//! * `(store a i v) -> bimap (store * I *) A V`
//! * `(OTHER [t_i]_i) -> (OTHER [T_i]_i)`
//! * constants: *omitted*
//!
//! The result of this phase is a computation whose only tuple-terms are at the top of the
//! computation graph
//!
//! ## Phase 2
//!
//! We replace each output `t` with the sequence of outputs `(list T)`.

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::{
    check, extras, leaf_term, term, Array, Computation, Op, PostOrderIter, Sort, Term, Value, AND,
};
use std::collections::BTreeMap;

use itertools::zip_eq;

#[derive(Clone, PartialEq, Eq, Debug)]
struct TupleTree(Term);

impl TupleTree {
    fn flatten(&self) -> impl Iterator<Item = Term> {
        let mut out = Vec::new();
        fn rec_unroll_into(t: &Term, out: &mut Vec<Term>) {
            if t.op == Op::Tuple {
                for c in &t.cs {
                    rec_unroll_into(c, out);
                }
            } else {
                out.push(t.clone());
            }
        }
        rec_unroll_into(&self.0, &mut out);
        out.into_iter()
    }
    fn structure(&self, flattened: impl IntoIterator<Item = Term>) -> Self {
        fn term_structure(t: &Term, iter: &mut impl Iterator<Item = Term>) -> Term {
            if t.op == Op::Tuple {
                term(
                    Op::Tuple,
                    t.cs.iter().map(|c| term_structure(c, iter)).collect(),
                )
            } else {
                iter.next().expect("bad structure")
            }
        }
        Self(term_structure(&self.0, &mut flattened.into_iter()))
    }
    fn well_formed(&self) -> bool {
        for t in PostOrderIter::new(self.0.clone()) {
            if t.op != Op::Tuple {
                for c in &t.cs {
                    if c.op == Op::Tuple {
                        return false;
                    }
                }
            }
        }
        true
    }
    #[allow(dead_code)]
    fn assert_well_formed(&self) {
        assert!(
            self.well_formed(),
            "The following is not a well-formed tuple tree {}",
            extras::Letified(self.0.clone())
        );
    }
    fn map(&self, f: impl FnMut(Term) -> Term) -> Self {
        self.structure(self.flatten().map(f))
    }
    fn bimap(&self, mut f: impl FnMut(Term, Term) -> Term, other: &Self) -> Self {
        self.structure(itertools::zip_eq(self.flatten(), other.flatten()).map(|(a, b)| f(a, b)))
    }
    fn get(&self, i: usize) -> Self {
        assert_eq!(&self.0.op, &Op::Tuple);
        assert!(i < self.0.cs.len());
        Self(self.0.cs[i].clone())
    }
    fn update(&self, i: usize, v: &Term) -> Self {
        assert_eq!(&self.0.op, &Op::Tuple);
        assert!(i < self.0.cs.len());
        let mut cs = self.0.cs.clone();
        cs[i] = v.clone();
        Self(term(Op::Tuple, cs))
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct ValueTupleTree(Value);

impl ValueTupleTree {
    fn flatten(&self) -> Vec<Value> {
        let mut out = Vec::new();
        fn rec_unroll_into(t: &Value, out: &mut Vec<Value>) {
            match t {
                Value::Tuple(vs) => {
                    for c in vs {
                        rec_unroll_into(c, out);
                    }
                }
                _ => out.push(t.clone()),
            }
        }
        rec_unroll_into(&self.0, &mut out);
        out
    }
    fn structure(&self, flattened: impl IntoIterator<Item = Value>) -> Self {
        fn term_structure(t: &Value, iter: &mut impl Iterator<Item = Value>) -> Value {
            match t {
                Value::Tuple(vs) => {
                    Value::Tuple(vs.iter().map(|c| term_structure(c, iter)).collect())
                }
                _ => iter.next().expect("bad structure"),
            }
        }
        Self(term_structure(&self.0, &mut flattened.into_iter()))
    }
}

fn termify_val_tuples(v: Value) -> Term {
    if let Value::Tuple(vs) = v {
        term(Op::Tuple, vs.into_iter().map(termify_val_tuples).collect())
    } else {
        leaf_term(Op::Const(v))
    }
}

fn untuple_value(v: &Value) -> Value {
    match v {
        Value::Tuple(xs) => Value::Tuple(xs.iter().map(untuple_value).collect()),
        Value::Array(Array {
            key_sort,
            default,
            map,
            size,
        }) => {
            let def = untuple_value(default);
            let flat_def = ValueTupleTree(def.clone()).flatten();
            let mut map: BTreeMap<_, _> = map
                .iter()
                .map(|(k, v)| (k, ValueTupleTree(untuple_value(v)).flatten()))
                .collect();
            let mut flat_out: Vec<Value> = flat_def
                .into_iter()
                .rev()
                .map(|d| {
                    let mut submap: BTreeMap<Value, Value> = BTreeMap::new();
                    for (k, v) in &mut map {
                        submap.insert((**k).clone(), v.pop().unwrap());
                    }
                    Value::Array(Array::new(key_sort.clone(), Box::new(d), submap, *size))
                })
                .collect();
            flat_out.reverse();
            ValueTupleTree(def).structure(flat_out).0
        }
        _ => v.clone(),
    }
}

struct TupleLifter;

impl RewritePass for TupleLifter {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        match &orig.op {
            Op::Const(v) => Some(termify_val_tuples(untuple_value(v))),
            Op::Ite => {
                let mut cs = rewritten_children();
                let f = TupleTree(cs.pop().unwrap());
                let t = TupleTree(cs.pop().unwrap());
                let c = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                Some(t.bimap(|a, b| term![Op::Ite; c.clone(), a, b], &f).0)
            }
            Op::Eq => {
                let mut cs = rewritten_children();
                let b = TupleTree(cs.pop().unwrap());
                let a = TupleTree(cs.pop().unwrap());
                debug_assert!(cs.is_empty());
                let eqs = zip_eq(a.flatten(), b.flatten()).map(|(a, b)| term![Op::Eq; a, b]);
                Some(term(AND, eqs.collect()))
            }
            Op::Store => {
                let mut cs = rewritten_children();
                let v = TupleTree(cs.pop().unwrap());
                let i = cs.pop().unwrap();
                let a = TupleTree(cs.pop().unwrap());
                debug_assert!(cs.is_empty());
                Some(a.bimap(|a, v| term![Op::Store; a, i.clone(), v], &v).0)
            }
            Op::Select => {
                let mut cs = rewritten_children();
                let i = cs.pop().unwrap();
                let a = TupleTree(cs.pop().unwrap());
                debug_assert!(cs.is_empty());
                Some(a.map(|a| term![Op::Select; a, i.clone()]).0)
            }
            Op::Field(i) => {
                let mut cs = rewritten_children();
                let t = TupleTree(cs.pop().unwrap());
                debug_assert!(cs.is_empty());
                Some(t.get(*i).0)
            }
            Op::Update(i) => {
                let mut cs = rewritten_children();
                let v = cs.pop().unwrap();
                let t = TupleTree(cs.pop().unwrap());
                debug_assert!(cs.is_empty());
                Some(t.update(*i, &v).0)
            }
            // The default rewrite is correct here.
            Op::Tuple => None,
            _ => None,
        }
    }
}

#[allow(dead_code)]
fn tuple_free(t: Term) -> bool {
    PostOrderIter::new(t).all(|c| !matches!(check(&c), Sort::Tuple(..)))
}

/// Run the tuple elimination pass.
pub fn eliminate_tuples(cs: &mut Computation) {
    let mut pass = TupleLifter;
    pass.traverse(cs);
    cs.outputs = std::mem::take(&mut cs.outputs)
        .into_iter()
        .flat_map(|o| TupleTree(o).flatten())
        .collect();
    #[cfg(debug_assertions)]
    for o in &cs.outputs {
        assert!(tuple_free(o.clone()));
    }
}
