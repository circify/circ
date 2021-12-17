//! Oblivious Array Elimination
//!
//! This module attempts to identify *oblivious* arrays: those that are only accessed at constant
//! indices. These arrays can be replaced with tuples.
//!
//! It operates in two passes:
//!
//!    1. determine which arrays are oblivious
//!    2. replace oblivious arrays with (haskell) lists of terms.
//!
//!
//! ## Pass 1: Identifying oblivious arrays
//!
//! We maintain a set of non-oblivious arrays, initially empty. We traverse the whole SMT
//! constraint system, performing the following inferences:
//!
//!    * If `a[i]` for non-constant `i`, then `a` is not oblivious
//!    * If `a[i\v]` for non-constant `i`, then neither `a[i\v]` nor `a` are oblivious
//!    * If `a[i\v]`, then `a[i\v]` and `a` are equi-oblivious
//!    * If `ite(c,a,b)`, then `ite(c,a,b)`, `a`, and `b` are equi-oblivious
//!    * If `a=b`, then `a` and `b` are equi-oblivious
//!
//! This procedure is iterated to fixpoint.
//!
//! ## Pass 2: Replacing oblivious arrays with term lists.
//!
//! In this pass, the goal is to
//!
//!    * map array terms to haskell lists of value terms
//!    * map array selections to specific value terms
//!
//! The pass maintains:
//!
//!    * a map from array terms to tuple terms
//!
//! It then does a bottom-up formula traversal, performing the following
//! transformations:
//!
//!    * oblivious array variables are mapped to a list of (derivative) variables
//!    * oblivious constant arrays are mapped to a list that replicates the constant
//!    * accesses to oblivious arrays are mapped to the appropriate term from the
//!   value list of the array
//!    * stores to oblivious arrays are mapped to updated value lists
//!    * equalities between oblivious arrays are mapped to conjunctions of equalities

use super::visit::*;
use crate::ir::term::extras::as_uint_constant;
use crate::ir::term::*;

use log::debug;

use std::iter::repeat;

struct NonOblivComputer {
    not_obliv: TermSet,
}

impl NonOblivComputer {
    fn mark(&mut self, a: &Term) -> bool {
        if !self.not_obliv.insert(a.clone()) {
            debug!("Not obliv: {}", a);
            true
        } else {
            false
        }
    }

    fn bi_implicate(&mut self, a: &Term, b: &Term) -> bool {
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
    }
    fn new() -> Self {
        Self {
            not_obliv: TermSet::new(),
        }
    }
}

impl ProgressAnalysisPass for NonOblivComputer {
    fn visit(&mut self, term: &Term) -> bool {
        match &term.op {
            Op::Store => {
                let a = &term.cs[0];
                let i = &term.cs[1];
                let v = &term.cs[2];
                let mut progress = false;
                if let Sort::Array(..) = check(v) {
                    // Imprecisely, mark v as non-obliv iff the array is.
                    progress = progress || self.bi_implicate(term, v);
                }
                if let Op::Const(_) = i.op {
                    progress = progress || self.bi_implicate(term, a);
                } else {
                    progress = progress || self.mark(a);
                    progress = progress || self.mark(term);
                }
                if let Sort::Array(..) = check(v) {
                    // Imprecisely, mark v as non-obliv iff the array is.
                    progress = progress || self.bi_implicate(term, v);
                }
                progress
            }
            Op::Select => {
                let a = &term.cs[0];
                let i = &term.cs[1];
                if let Op::Const(_) = i.op {
                    self.mark(a)
                } else {
                    false
                }
            }
            Op::Ite => {
                let t = &term.cs[1];
                let f = &term.cs[2];
                if let Sort::Array(..) = check(t) {
                    let mut progress = self.bi_implicate(term, t);
                    progress = progress || self.bi_implicate(t, f);
                    progress = progress || self.bi_implicate(term, f);
                    progress
                } else {
                    false
                }
            }
            Op::Eq => {
                let t = &term.cs[0];
                let f = &term.cs[1];
                if let Sort::Array(..) = check(t) {
                    self.bi_implicate(t, f)
                } else {
                    false
                }
            }
            Op::Tuple => {
                panic!("Tuple in obliv")
            }
            _ => false
        }
    }
}

struct Replacer {
    /// A map from (original) replaced terms, to what they were replaced with.
    tuples: TermMap<Term>,
    /// The maximum size of arrays that will be replaced.
    not_obliv: TermSet,
}

impl Replacer {
    fn should_replace(&self, a: &Term) -> bool {
        !self.not_obliv.contains(a)
    }

}

impl MemVisitor for Replacer {
    fn visit_const_array(&mut self, orig: &Term, _key_sort: &Sort, val: &Term, size: usize) {
        if self.should_replace(orig) {
            debug!("Will replace constant: {}", orig);
            self.tuples.insert(
                orig.clone(),
                term(Op::Tuple, repeat(val).cloned().take(size).collect()),
            );
        }
    }
    fn visit_eq(&mut self, orig: &Term, _a: &Term, _b: &Term) -> Option<Term> {
        if let Some(a_tup) = self.tuples.get(&orig.cs[0]) {
            let b_tup = self.tuples.get(&orig.cs[1]).expect("inconsistent eq");
            Some(term![Op::Eq; a_tup.clone(), b_tup.clone()])
        } else {
            None
        }
    }
    fn visit_ite(&mut self, orig: &Term, c: &Term, _t: &Term, _f: &Term) {
        if self.should_replace(orig) {
            let a_tup = self.tuples.get(&orig.cs[1]).expect("inconsistent ite");
            let b_tup = self.tuples.get(&orig.cs[2]).expect("inconsistent ite");
            let ite = term![Op::Ite; c.clone(), a_tup.clone(), b_tup.clone()];
            self.tuples.insert(orig.clone(), ite);
        }
    }
    fn visit_store(&mut self, orig: &Term, _a: &Term, k: &Term, v: &Term) {
        if self.should_replace(orig) {
            let a_tup = self
                .tuples
                .get(&orig.cs[0])
                .unwrap_or_else(|| panic!("inconsistent store {}", orig.cs[0].clone()))
                .clone();
            let k_const = as_uint_constant(k)
                .expect("not obliv!")
                .to_usize()
                .expect("oversize index");
            debug!("store: {}", orig);
            self.tuples
                .insert(orig.clone(), term![Op::Update(k_const); a_tup, v.clone()]);
        }
    }
    fn visit_select(&mut self, orig: &Term, _a: &Term, k: &Term) -> Option<Term> {
        if let Some(a_tup) = self.tuples.get(&orig.cs[0]) {
            debug!("Will replace select: {}", orig);
            let k_const = as_uint_constant(k)
                .expect("not obliv!")
                .to_usize()
                .expect("oversize index");
            Some(term![Op::Field(k_const); a_tup.clone()])
        } else {
            debug!("Will not replace select: {}", orig);
            None
        }
    }
    fn visit_var(&mut self, orig: &Term, name: &String, s: &Sort) {
        if let Sort::Array(_k, v, size) = s {
            if self.should_replace(orig) {
                self.tuples.insert(
                    orig.clone(),
                    leaf_term(Op::Var(
                        name.clone(),
                        Sort::Tuple(repeat((**v).clone()).take(*size).collect()),
                    )),
                );
            }
        } else {
            unreachable!("should only visit array vars")
        }
    }
}
impl RewritePass for Replacer {
    fn visit<F: Fn() -> Vec<Term>>(&mut self, orig: &Term, rewritten_children: F) -> Option<Term> {
        todo!()
    }
}

/// Eliminate oblivious arrays. See module documentation.
pub fn elim_obliv(t: &mut Computation) {
    let mut prop_pass = NonOblivComputer::new();
    prop_pass.traverse(t);
    let mut replace_pass = Replacer {
        not_obliv: prop_pass.not_obliv,
        tuples: TermMap::new(),
    };
    <Replacer as RewritePass>::traverse(&mut replace_pass, t)
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
        let z = term![Op::ConstArray(Sort::BitVector(4), 6); bv_lit(0, 4)];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), bv_lit(3, 4), bv_lit(1, 4)],
              term![Op::Store; z.clone(), bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let tt = elim_obliv(&t);
        assert!(array_free(&tt));
    }

    #[test]
    fn not_obliv() {
        let z = term![Op::ConstArray(Sort::BitVector(4), 6); bv_lit(0, 4)];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), v_bv("a", 4), bv_lit(1, 4)],
              term![Op::Store; z.clone(), bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let tt = elim_obliv(&t);
        assert!(!array_free(&tt));
    }
}
