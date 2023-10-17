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
//!
//! ## Data representation
//!
//! Since the rewrite produces a large number of (possibly big) tuples, and we sometimes apply
//! update operators to those tuples, we represent the rewritten tuple trees using an immutable,
//! fast vector type, instead of standard terms. This allows for log-time updates.

use crate::ir::term::{
    bv_lit, check, leaf_term, term, Array, Computation, Node, Op, PostOrderIter, Sort, Term,
    TermMap, Value, AND,
};
use std::collections::BTreeMap;

use itertools::zip_eq;

#[derive(Clone, PartialEq, Eq, Debug)]
enum TupleTree {
    NonTuple(Term),
    Tuple(im::Vector<TupleTree>),
}

impl TupleTree {
    fn flatten(&self) -> impl Iterator<Item = Term> {
        let mut out = Vec::new();
        fn rec_unroll_into(t: &TupleTree, out: &mut Vec<Term>) {
            match t {
                TupleTree::NonTuple(t) => out.push(t.clone()),
                TupleTree::Tuple(t) => {
                    for c in t {
                        rec_unroll_into(c, out);
                    }
                }
            }
        }
        rec_unroll_into(self, &mut out);
        out.into_iter()
    }
    fn structure(&self, flattened: impl IntoIterator<Item = Term>) -> Self {
        fn term_structure(t: &TupleTree, iter: &mut impl Iterator<Item = Term>) -> TupleTree {
            match t {
                TupleTree::Tuple(tt) => {
                    TupleTree::Tuple(tt.iter().map(|c| term_structure(c, iter)).collect())
                }
                TupleTree::NonTuple(_) => TupleTree::NonTuple(iter.next().expect("bad structure")),
            }
        }
        term_structure(self, &mut flattened.into_iter())
    }
    fn map(&self, f: impl FnMut(Term) -> Term) -> Self {
        self.structure(self.flatten().map(f))
    }
    fn bimap(&self, mut f: impl FnMut(Term, Term) -> Term, other: &Self) -> Self {
        self.structure(itertools::zip_eq(self.flatten(), other.flatten()).map(|(a, b)| f(a, b)))
    }
    fn transpose_map(vs: Vec<Self>, f: impl FnMut(Vec<Term>) -> Term) -> Self {
        assert!(!vs.is_empty());
        let n = vs[0].flatten().count();
        let mut ts = vec![Vec::new(); n];
        for v in &vs {
            for (i, t) in v.flatten().enumerate() {
                ts[i].push(t);
            }
        }
        vs[0].structure(ts.into_iter().map(f))
    }
    fn get(&self, i: usize) -> Self {
        match self {
            TupleTree::NonTuple(cs) => {
                if let Sort::Tuple(_) = check(cs) {
                    TupleTree::NonTuple(term![Op::Field(i); cs.clone()])
                } else if let Sort::Array(_, _, _) = check(cs) {
                    TupleTree::NonTuple(term![Op::Select; cs.clone(), bv_lit(i, 32)])
                } else {
                    panic!("Get ({}) on non-tuple {:?}", i, self)
                }
            }
            TupleTree::Tuple(t) => {
                assert!(i < t.len());
                t.get(i).unwrap().clone()
            }
        }
    }
    fn update(&self, i: usize, v: &TupleTree) -> Self {
        match self {
            TupleTree::NonTuple(_) => panic!("Update ({}) on non-tuple {:?}", i, self),
            TupleTree::Tuple(t) => {
                assert!(i < t.len());
                TupleTree::Tuple(t.update(i, v.clone()))
            }
        }
    }
    fn unwrap_non_tuple(self) -> Term {
        match self {
            TupleTree::NonTuple(t) => t,
            _ => panic!("{:?} is tuple!", self),
        }
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
                    for c in vs.iter() {
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

fn termify_val_tuples(v: Value) -> TupleTree {
    if let Value::Tuple(vs) = v {
        TupleTree::Tuple(Vec::from(vs).into_iter().map(termify_val_tuples).collect())
    } else {
        TupleTree::NonTuple(leaf_term(Op::Const(v)))
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

fn find_tuple_term(t: Term) -> Option<Term> {
    PostOrderIter::new(t).find(|c| matches!(check(c), Sort::Tuple(..)))
}

#[allow(dead_code)]
fn tuple_free(t: Term) -> bool {
    find_tuple_term(t).is_none()
}

/// Run the tuple elimination pass.
pub fn eliminate_tuples(cs: &mut Computation) {
    let mut lifted: TermMap<TupleTree> = TermMap::default();
    for t in cs.terms_postorder() {
        let mut cs: Vec<TupleTree> = t
            .cs()
            .iter()
            .map(|c| lifted.get(c).unwrap().clone())
            .collect();
        let new_t = match t.op() {
            Op::Const(v) => termify_val_tuples(untuple_value(v)),
            Op::Ite => {
                let f = cs.pop().unwrap();
                let t = cs.pop().unwrap();
                let c = cs.pop().unwrap().unwrap_non_tuple();
                debug_assert!(cs.is_empty());
                t.bimap(|a, b| term![Op::Ite; c.clone(), a, b], &f)
            }
            Op::Eq => {
                let b = cs.pop().unwrap();
                let a = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                let eqs = zip_eq(a.flatten(), b.flatten()).map(|(a, b)| term![Op::Eq; a, b]);
                TupleTree::NonTuple(term(AND, eqs.collect()))
            }
            Op::Store => {
                let v = cs.pop().unwrap();
                let i = cs.pop().unwrap().unwrap_non_tuple();
                let a = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                a.bimap(|a, v| term![Op::Store; a, i.clone(), v], &v)
            }
            Op::Array(k, _v) => TupleTree::transpose_map(cs, |children| {
                assert!(!children.is_empty());
                let v_s = check(&children[0]);
                term(Op::Array(k.clone(), v_s), children)
            }),
            Op::Fill(key_sort, size) => {
                let values = cs.pop().unwrap();
                values.map(|v| term![Op::Fill(key_sort.clone(), *size); v])
            }
            Op::Select => {
                let i = cs.pop().unwrap().unwrap_non_tuple();
                let a = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                a.map(|a| term![Op::Select; a, i.clone()])
            }
            Op::Field(i) => {
                let t = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                t.get(*i)
            }
            Op::Update(i) => {
                let v = cs.pop().unwrap();
                let t = cs.pop().unwrap();
                debug_assert!(cs.is_empty());
                t.update(*i, &v)
            }
            Op::Tuple => TupleTree::Tuple(cs.into()),
            _ => TupleTree::NonTuple(term(
                t.op().clone(),
                cs.into_iter().map(|c| c.unwrap_non_tuple()).collect(),
            )),
        };
        lifted.insert(t, new_t);
    }
    cs.outputs = std::mem::take(&mut cs.outputs)
        .into_iter()
        .flat_map(|o| lifted.get(&o).unwrap().clone().flatten())
        .collect();
    #[cfg(debug_assertions)]
    for o in &cs.outputs {
        if let Some(t) = find_tuple_term(o.clone()) {
            panic!("Tuple term {}", t)
        }
    }
}
