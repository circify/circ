//! Oblivious Array Elimination
//!
//! This module attempts to identify *oblivious* arrays: those that are only accessed at constant
//! indices. These arrays can be replaced with tuples. Then, a tuple elimination pass can be run.
//!
//! It operates in two passes:
//!
//!    1. determine which arrays are oblivious
//!    2. replace oblivious arrays with tuples
//!
//!
//! ## Pass 1: Identifying oblivious arrays
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

use super::super::visit::*;
use crate::ir::term::extras::as_uint_constant;
use crate::ir::term::*;

use log::debug;

struct NonOblivComputer {
    not_obliv: TermSet,
}

impl NonOblivComputer {
    fn mark(&mut self, a: &Term) -> bool {
        if !a.is_const() && self.not_obliv.insert(a.clone()) {
            debug!("Not obliv: {}", a);
            true
        } else {
            false
        }
    }

    fn bi_implicate(&mut self, a: &Term, b: &Term) -> bool {
        if !a.is_const() && !b.is_const() {
            match (self.not_obliv.contains(a), self.not_obliv.contains(b)) {
                (false, true) => {
                    self.not_obliv.insert(a.clone());
                    true
                }
                (true, false) => {
                    self.not_obliv.insert(b.clone());
                    true
                }
                _ => false,
            }
        } else {
            false
        }
    }

    fn new() -> Self {
        Self {
            not_obliv: TermSet::default(),
        }
    }
}

impl ProgressAnalysisPass for NonOblivComputer {
    fn visit(&mut self, term: &Term) -> bool {
        match &term.op() {
            Op::Store | Op::CStore => {
                let a = &term.cs()[0];
                let i = &term.cs()[1];
                let v = &term.cs()[2];
                let mut progress = false;
                if let Sort::Array(..) = check(v) {
                    // Imprecisely, mark v as non-obliv iff the array is.
                    progress = self.bi_implicate(term, v) || progress;
                }
                if let Op::Const(_) = i.op() {
                    progress = self.bi_implicate(term, a) || progress;
                } else {
                    progress = self.mark(a) || progress;
                    progress = self.mark(term) || progress;
                }
                if let Sort::Array(..) = check(v) {
                    // Imprecisely, mark v as non-obliv iff the array is.
                    progress = self.bi_implicate(term, v) || progress;
                }
                progress
            }
            Op::Array(..) => {
                let mut progress = false;
                if !term.cs().is_empty() {
                    if let Sort::Array(..) = check(&term.cs()[0]) {
                        progress = self.bi_implicate(term, &term.cs()[0]) || progress;
                        for i in 0..term.cs().len() - 1 {
                            progress =
                                self.bi_implicate(&term.cs()[i], &term.cs()[i + 1]) || progress;
                        }
                        for i in (0..term.cs().len() - 1).rev() {
                            progress =
                                self.bi_implicate(&term.cs()[i], &term.cs()[i + 1]) || progress;
                        }
                        progress = self.bi_implicate(term, &term.cs()[0]) || progress;
                    }
                }
                progress
            }
            Op::Fill(..) => {
                let v = &term.cs()[0];
                if let Sort::Array(..) = check(v) {
                    self.bi_implicate(term, &term.cs()[0])
                } else {
                    false
                }
            }
            Op::Select => {
                // Even though the selected value may not have array sort, we still flag it as
                // non-oblivious so we know whether to replace it or not.
                let a = &term.cs()[0];
                let i = &term.cs()[1];
                let mut progress = false;
                if let Op::Const(_) = i.op() {
                    // pass
                } else {
                    progress = self.mark(a) || progress;
                    progress = self.mark(term) || progress;
                }
                progress = self.bi_implicate(term, a) || progress;
                progress
            }
            Op::Var(..) => {
                if let Sort::Array(..) = check(term) {
                    self.mark(term)
                } else {
                    false
                }
            }
            Op::Ite => {
                let t = &term.cs()[1];
                let f = &term.cs()[2];
                if let Sort::Array(..) = check(t) {
                    let mut progress = self.bi_implicate(term, t);
                    progress = self.bi_implicate(t, f) || progress;
                    progress = self.bi_implicate(term, f) || progress;
                    progress
                } else {
                    false
                }
            }
            Op::Eq => {
                let a = &term.cs()[0];
                let b = &term.cs()[1];
                if let Sort::Array(..) = check(a) {
                    self.bi_implicate(a, b)
                } else {
                    false
                }
            }
            Op::Tuple => {
                panic!("Tuple in obliv")
            }
            _ => false,
        }
    }
}

struct Replacer {
    /// The maximum size of arrays that will be replaced.
    not_obliv: TermSet,
}

impl Replacer {
    fn should_replace(&self, a: &Term) -> bool {
        !self.not_obliv.contains(a)
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

fn term_arr_val_to_tup(a: Term) -> Term {
    match &a.op() {
        Op::Const(v @ Value::Array(..)) => leaf_term(Op::Const(arr_val_to_tup(v))),
        _ => a,
    }
}

#[track_caller]
fn get_const(t: &Term) -> usize {
    as_uint_constant(t)
        .unwrap_or_else(|| panic!("non-const {}", t))
        .to_usize()
        .expect("oversize")
}

impl RewritePass for Replacer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        //debug!("Visit {}", extras::Letified(orig.clone()));
        let get_cs = || -> Vec<Term> {
            rewritten_children()
                .into_iter()
                .map(term_arr_val_to_tup)
                .collect()
        };
        match &orig.op() {
            Op::Var(name, Sort::Array(..)) => {
                if self.should_replace(orig) {
                    let precomp = extras::array_to_tuple(orig);
                    let new_name = format!("{name}.tup");
                    let new_sort = check(&precomp);
                    computation.extend_precomputation(new_name.clone(), precomp);
                    Some(leaf_term(Op::Var(new_name, new_sort)))
                } else {
                    None
                }
            }
            Op::Select => {
                // we mark the selected term as non-obliv...
                if self.should_replace(orig) {
                    let mut cs = get_cs();
                    debug_assert_eq!(cs.len(), 2);
                    let k_const = get_const(&cs.pop().unwrap());
                    Some(term(Op::Field(k_const), cs))
                } else {
                    None
                }
            }
            Op::Store => {
                if self.should_replace(orig) {
                    let mut cs = get_cs();
                    debug_assert_eq!(cs.len(), 3);
                    let k_const = get_const(&cs.remove(1));
                    Some(term(Op::Update(k_const), cs))
                } else {
                    None
                }
            }
            Op::CStore => {
                if self.should_replace(orig) {
                    let mut cs = get_cs();
                    debug_assert_eq!(cs.len(), 4);
                    let cond = cs.remove(3);
                    let k_const = get_const(&cs.remove(1));
                    let orig = cs[0].clone();
                    Some(term![ITE; cond, term(Op::Update(k_const), cs), orig])
                } else {
                    None
                }
            }
            Op::Array(..) => {
                if self.should_replace(orig) {
                    Some(term(Op::Tuple, get_cs()))
                } else {
                    None
                }
            }
            Op::Fill(_, size) => {
                if self.should_replace(orig) {
                    Some(term(Op::Tuple, vec![get_cs().pop().unwrap(); *size]))
                } else {
                    None
                }
            }
            Op::Ite => {
                if self.should_replace(orig) {
                    Some(term(Op::Ite, get_cs()))
                } else {
                    None
                }
            }
            Op::Eq => {
                if self.should_replace(&orig.cs()[0]) {
                    Some(term(Op::Eq, get_cs()))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// Eliminate oblivious arrays. See module documentation.
pub fn elim_obliv(t: &mut Computation) {
    let mut prop_pass = NonOblivComputer::new();
    prop_pass.traverse(t);
    let mut replace_pass = Replacer {
        not_obliv: prop_pass.not_obliv,
    };
    <Replacer as RewritePass>::traverse_full(&mut replace_pass, t, false, false)
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
}
