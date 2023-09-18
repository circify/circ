//! Oblivious Array Elimination
//!
//! This module attempts to identify *oblivious* arrays: those that are only accessed at constant
//! indices. These arrays can be replaced with tuples. Then, a tuple elimination pass can be run.
//!
//! It operates in a single IO (inputs->outputs) pass, that computes three maps:
//!
//!    * `R`: the rewrite map
//!    * `T`: the map from a term, to one whose sort has arrays replaced with tuples.
//!
//! terms *if possible*:
//!
//!    * `r = ite(c, a, b)`: tuple `r` iff `a` and `b` are tupled
//!    * `r = a[i\v]`: tuple `r` iff `i` is contant and `a` is tupled
//!    * `r = a[i]`:
//!       * if `i` is contant and
//!       * if `r` is a
//!
//! If
//!
//! It operates in two passes:
//!
//!    1. determine which arrays are oblivious
//!    2. replace those oblivious arrays with tuples
//!
//! ## Pass 1: Identifying oblivious arrays
//!
//! First, we compute which array terms have all their values at known positions. This is a IO
//! traversal.
//!
//! We maintain a set of non-oblivious arrays, initially empty. We traverse the whole computation
//! system, performing the following inferences:
//!
//!    * If `a[i]` for non-constant `i`, then `a` and `a[i]` are not oblivious;
//!    * If `a[i]`, `a` and `a[i]`  are equi-oblivious
//!    * If `a[i\v]` for non-constant `i`, then neither `a[i\v]` nor `a` are oblivious
//!    * If `a[i\v]`, then `a[i\v]` and `a` are equi-oblivious
//!    * If `ite(c,a,b)`, then `ite(c,a,b)`, `a`, and `b` are equi-oblivious
//!    * If `a=b`, then `a` and `b` are equi-oblivious
//!
//! This procedure is iterated to fixpoint.
//!
//! Notice that we flag some *array* terms as non-oblivious, and we also flag their derived select
//! terms as non-oblivious. This makes it easy to see which selects should be replaced later.
//!
//! ### Sharing & Constant Arrays
//!
//! This pass is effective given the somewhat naive assumption that array terms in the term graph
//! can be separated into different "threads", which are not connected. Sometimes they are,
//! especially by constant arrays.
//!
//! For example, consider code like this:
//!
//! ```ignore
//! x = [0, 0, 0, 0]
//! y = [0, 0, 0, 0]
//! // oblivious modifications to x
//! // non-oblivious modifications to y
//! ```
//!
//! In this situation, we would hope that x and its derived arrays will be identified as
//! "oblivious" while y will not.
//!
//! However, because of term sharing, the constant array [0,0,0,0] happens to be the root of both
//! x's and y's store chains. If the constant array is `c`, then the first store to x might be
//! `c[0\v1]` while the first store to y might be `c[i2\v2]`. The "store" rule for non-oblivious
//! analysis would say that `c` is non-oblivious (b/c of the second store) and therefore the whole
//! x store chain would b too...
//!
//! The problem isn't just with constants. If any non-oblivious stores branch off an otherwise
//! oblivious store chain, the same thing happens.
//!
//! Since constants are a pervasive problem, we special-case them, omitting them from the analysis.
//!
//! We probably want a better idea of what this pass does (and how to handle arrays) at some
//! point...
//!
//! ## Pass 2: Replacing oblivious arrays with term lists.
//!
//! In this pass, the goal is to
//!
//!    * map array terms to tuple terms
//!    * map array selections to tuple field gets
//!
//! In both cases we look at the non-oblivious array/select set to see whether to do the
//! replacement.
//!

use crate::ir::term::extras::as_uint_constant;
use crate::ir::term::*;

use log::{debug, trace};

#[derive(Default)]
struct OblivRewriter {
    tups: TermMap<Term>,
    terms: TermMap<Term>,
}

fn suitable_const(t: &Term) -> bool {
    t.is_const() && matches!(check(t), Sort::BitVector(_) | Sort::Field(_) | Sort::Bool)
}

impl OblivRewriter {
    fn get_t(&self, t: &Term) -> &Term {
        self.tups.get(t).unwrap_or(self.terms.get(t).unwrap())
    }
    fn get(&self, t: &Term) -> &Term {
        self.terms.get(t).unwrap()
    }
    fn visit(&mut self, t: &Term) {
        let (tup_opt, term_opt) = match t.op() {
            Op::Const(v @ Value::Array(_)) => (Some(leaf_term(Op::Const(arr_val_to_tup(v)))), None),
            Op::Array(_k, _v) => (
                Some(term(
                    Op::Tuple,
                    t.cs().iter().map(|c| self.get_t(c)).cloned().collect(),
                )),
                None,
            ),
            Op::Fill(_k, size) => (
                Some(term(Op::Tuple, vec![self.get_t(&t.cs()[0]).clone(); *size])),
                None,
            ),
            Op::Store => {
                let a = &t.cs()[0];
                let i = &t.cs()[1];
                let v = &t.cs()[2];
                (
                    if let Some(aa) = self.tups.get(a) {
                        if suitable_const(i) {
                            debug!("simplify store {}", i);
                            Some(term![Op::Update(get_const(i)); aa.clone(), self.get_t(v).clone()])
                        } else {
                            None
                        }
                    } else {
                        None
                    },
                    None,
                )
            }
            Op::Select => {
                let a = &t.cs()[0];
                let i = &t.cs()[1];
                if let Some(aa) = self.tups.get(a) {
                    if suitable_const(i) {
                        debug!("simplify select {}", i);
                        let tt = term![Op::Field(get_const(i)); aa.clone()];
                        (
                            Some(tt.clone()),
                            if check(&tt).is_scalar() {
                                Some(tt)
                            } else {
                                None
                            },
                        )
                    } else {
                        (None, None)
                    }
                } else {
                    (None, None)
                }
            }
            Op::Ite => {
                let cond = &t.cs()[0];
                let case_t = &t.cs()[1];
                let case_f = &t.cs()[2];
                (
                    if let (Some(tt), Some(ff)) = (self.tups.get(case_t), self.tups.get(case_f)) {
                        Some(term![Op::Ite; self.get(cond).clone(), tt.clone(), ff.clone()])
                    } else {
                        None
                    },
                    None,
                )
            }
            Op::Eq => {
                let a = &t.cs()[0];
                let b = &t.cs()[1];
                (
                    None,
                    if let (Some(aa), Some(bb)) = (self.tups.get(a), self.tups.get(b)) {
                        Some(term![Op::Eq; aa.clone(), bb.clone()])
                    } else {
                        None
                    },
                )
            }
            Op::Tuple => panic!("Tuple in obliv"),
            _ => (None, None),
        };
        if let Some(tup) = tup_opt {
            trace!("Tuple rw: \n{}\nto\n{}", t, tup);
            self.tups.insert(t.clone(), tup);
        }
        let new_t = term_opt.unwrap_or_else(|| {
            term(
                t.op().clone(),
                t.cs().iter().map(|c| self.get(c)).cloned().collect(),
            )
        });

        self.terms.insert(t.clone(), new_t);
    }
}

/// Eliminate oblivious arrays. See module documentation.
pub fn elim_obliv(c: &mut Computation) {
    let mut pass = OblivRewriter::default();
    for t in c.terms_postorder() {
        pass.visit(&t);
    }
    for o in &mut c.outputs {
        debug_assert!(check(o).is_scalar());
        *o = pass.get(o).clone();
    }
}

fn arr_val_to_tup(v: &Value) -> Value {
    match v {
        Value::Array(Array {
            default, map, size, ..
        }) => Value::Tuple({
            let mut vec = vec![arr_val_to_tup(default); *size].into_boxed_slice();
            for (i, v) in map {
                vec[i.as_usize().expect("non usize key")] = arr_val_to_tup(v);
            }
            vec
        }),
        v => v.clone(),
    }
}

#[track_caller]
fn get_const(t: &Term) -> usize {
    as_uint_constant(t)
        .unwrap_or_else(|| panic!("non-const {}", t))
        .to_usize()
        .expect("oversize")
}

#[cfg(test)]
mod test {
    use super::*;

    fn v_bv(n: &str, w: usize) -> Term {
        leaf_term(Op::Var(n.to_owned(), Sort::BitVector(w)))
    }

    fn array_free(t: &Term) -> bool {
        for c in PostOrderIter::new(t.clone()) {
            if let Sort::Array(..) = check(&c) {
                return false;
            }
        }
        true
    }

    fn count_selects(t: &Term) -> usize {
        PostOrderIter::new(t.clone())
            .filter(|t| matches!(t.op(), Op::Select))
            .count()
    }

    #[test]
    fn obliv() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), bv_lit(3, 4), bv_lit(1, 4)],
              term![Op::Store; z, bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let mut c = Computation::default();
        c.outputs.push(t);
        elim_obliv(&mut c);
        assert!(array_free(&c.outputs[0]));
    }

    #[test]
    fn not_obliv() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), v_bv("a", 4), bv_lit(1, 4)],
              term![Op::Store; z, bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let mut c = Computation::default();
        c.outputs.push(t);
        elim_obliv(&mut c);
        assert!(!array_free(&c.outputs[0]));
    }

    #[test]
    fn mix_diff_constant() {
        let z0 = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let z1 = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            5
        )))];
        let t0 = term![Op::Select;
            term![Op::Store; z0, v_bv("a", 4), bv_lit(1, 4)],
            bv_lit(3, 4)
        ];
        let t1 = term![Op::Select;
            term![Op::Store; z1, bv_lit(3, 4), bv_lit(1, 4)],
            bv_lit(3, 4)
        ];
        let mut c = Computation::default();
        c.outputs.push(t0);
        c.outputs.push(t1);
        elim_obliv(&mut c);
        assert!(!array_free(&c.outputs[0]));
        assert!(array_free(&c.outputs[1]));
    }

    #[test]
    fn mix_same_constant() {
        let z = term![Op::Const(Value::Array(Array::new(
            Sort::BitVector(4),
            Box::new(Sort::BitVector(4).default_value()),
            Default::default(),
            6
        )))];
        let t0 = term![Op::Select;
            term![Op::Store; z.clone(), v_bv("a", 4), bv_lit(1, 4)],
            bv_lit(3, 4)
        ];
        let t1 = term![Op::Select;
            term![Op::Store; z, bv_lit(3, 4), bv_lit(1, 4)],
            bv_lit(3, 4)
        ];
        let mut c = Computation::default();
        c.outputs.push(t0);
        c.outputs.push(t1);
        elim_obliv(&mut c);
        assert!(!array_free(&c.outputs[0]));
        assert!(array_free(&c.outputs[1]));
    }

    #[test]
    fn linear_stores_branching_selects() {
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs ) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#a (mod 11) #f0 4 ()))
                            (a1 (store a0 #f0 #f1))
                            (x0 (select a1 #f0))
                            (x1 (select a1 #f1))
                            (a2 (store a1 #f0 #f1))
                            (x2 (select a2 #f2))
                            (x3 (select a2 #f3))
                            (a3 (store a2 #f1 #f1))
                            (x4 (select a3 #f0))
                            (x5 (select a3 #f1))
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 0);
    }

    #[test]
    fn linear_stores_branching_selects_partial() {
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (i (mod 11))) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#a (mod 11) #f0 4 ()))
                            (a1 (store a0 #f0 #f1))
                            (x0 (select a1 #f0))
                            (x1 (select a1 #f1))
                            (a2 (store a1 #f0 #f1))
                            (x2 (select a2 #f2))
                            (x3 (select a2 #f3))
                            (a3 (store a2 i #f1))
                            (x4 (select a3 #f0))
                            (x5 (select a3 #f1))
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 2);
    }

    #[test]
    fn linear_stores_branching_selects_partial_2() {
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (i (mod 11))) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#a (mod 11) #f0 4 ()))
                            (a1 (store a0 #f0 #f1))
                            (x0 (select a1 #f0))
                            (x1 (select a1 #f1))
                            (a2 (store a1 i #f1))
                            (x2 (select a2 #f2))
                            (x3 (select a2 #f3))
                            (a3 (store a2 #f0 #f1))
                            (x4 (select a3 #f0))
                            (x5 (select a3 #f1))
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 4);
    }

    #[test]
    fn nest_obliv() {
        env_logger::try_init().ok();
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (i (mod 11))) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#l (mod 11) ((#l (mod 11) (#f1 #f0)) (#l (mod 11) (#f0 #f1)))))
                            (a1 (store a0 #f0 (store (select a0 #f0) #f1 #f1)))
                            (x0 (select (select a1 #f0) #f0))
                            (x1 (select (select a1 #f1) #f0))
                            (a2 (store a1 #f1 (store (select a1 #f1) #f1 #f1)))
                            (x2 (select (select a2 #f0) #f1))
                            (x3 (select (select a2 #f1) #f1))
                            (a3 (store a2 #f1 (store (select a2 #f1) #f0 #f1)))
                            (x4 (select (select a3 #f1) #f0))
                            (x5 (select (select a3 #f0) #f1))
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 0);
    }

    #[test]
    fn nest_obliv_partial() {
        env_logger::try_init().ok();
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (i (mod 11))) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#l (mod 11) ((#l (mod 11) (#f1 #f0)) (#l (mod 11) (#f0 #f1)))))
                            (a1 (store a0 #f0 (store (select a0 #f0) #f1 #f1)))
                            (x0 (select (select a1 #f0) #f0))
                            (x1 (select (select a1 #f1) #f0))
                            (a2 (store a1 i (store (select a1 i) #f1 #f1))) ; not elim
                            (x2 (select (select a2 #f0) #f1)) ; not elim (2)
                            (x3 (select (select a2 #f1) #f1)) ; not elim (2)
                            (a3 (store a2 #f1 (store (select a2 #f1) #f0 #f1))) ; not elim (dup)
                            (x4 (select (select a3 #f1) #f0)) ; not elim (2)
                            (x5 (select (select a3 #f0) #f1)) ; not elim (2)
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        let before = count_selects(&c.outputs[0]);
        elim_obliv(&mut c);
        assert!(count_selects(&c.outputs[0]) < before);
    }

    #[test]
    fn nest_no_obliv() {
        env_logger::try_init().ok();
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties ) (inputs (i (mod 11))) (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (a0 (#l (mod 11) ((#l (mod 11) (#f1 #f0)) (#l (mod 11) (#f0 #f1)))))
                            (a1 (store a0 i (store (select a0 i) #f1 #f1)))
                            (x0 (select (select a1 #f0) #f0))
                            (x1 (select (select a1 #f1) #f0))
                            (a2 (store a1 #f0 (store (select a1 #f0) #f1 #f1))) ; not elim
                            (x2 (select (select a2 #f0) #f1)) ; not elim (2)
                            (x3 (select (select a2 #f1) #f1)) ; not elim (2)
                            (a3 (store a2 #f1 (store (select a2 #f1) #f0 #f1))) ; not elim (dup)
                            (x4 (select (select a3 #f1) #f0)) ; not elim (2)
                            (x5 (select (select a3 #f0) #f1)) ; not elim (2)
                        )
                        (+ x0 x1 x2 x3 x4 x5)
                    ))
                )
            ",
        );
        let before = count_selects(&c.outputs[0]);
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), before);
    }

    #[test]
    fn two_array_ptr_chase_eq_size() {
        env_logger::try_init().ok();
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties )
                              (inputs (x0 (mod 11))
                                      (x1 (mod 11))
                                      (x2 (mod 11))
                                      (x3 (mod 11))
                                      (x4 (mod 11))
                                      (i0 (mod 11))
                                      (i1 (mod 11))
                                      (i2 (mod 11))
                                      (i3 (mod 11))
                              )
                              (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (ax (store (store (store (store (#a (mod 11) #f0 4 ()) #f0 x0) #f1 x1) #f2 x2) #f3 x3))
                            (ai (store (store (store (store (#a (mod 11) #f0 4 ()) #f0 i0) #f1 i1) #f2 i2) #f3 i3))
                            (xi0 (select ax (select ai #f0)))
                            (xi1 (select ax (select ai #f1)))
                            (xi2 (select ax (select ai #f2)))
                            (xi3 (select ax (select ai #f3)))
                        )
                        (+ xi0 xi1 xi2 xi3)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 4);
    }

    #[test]
    fn two_array_ptr_chase_ne_size() {
        env_logger::try_init().ok();
        let mut c = text::parse_computation(
            b"
                (computation
                    (metadata (parties )
                              (inputs (x0 (mod 11))
                                      (x1 (mod 11))
                                      (x2 (mod 11))
                                      (x3 (mod 11))
                                      (x4 (mod 11))
                                      (i0 (mod 11))
                                      (i1 (mod 11))
                                      (i2 (mod 11))
                              )
                              (commitments))
                    (precompute () () (#t ))
                    (set_default_modulus 11
                    (let
                        (
                            (ax (store (store (store (store (#a (mod 11) #f0 4 ()) #f0 x0) #f1 x1) #f2 x2) #f3 x3))
                            (ai (store (store (store (#a (mod 11) #f0 4 ()) #f0 i0) #f1 i1) #f2 i2))
                            (xi0 (select ax (select ai #f0)))
                            (xi1 (select ax (select ai #f1)))
                            (xi2 (select ax (select ai #f2)))
                        )
                        (+ xi0 xi1 xi2)
                    ))
                )
            ",
        );
        elim_obliv(&mut c);
        assert_eq!(count_selects(&c.outputs[0]), 3);
    }
}
