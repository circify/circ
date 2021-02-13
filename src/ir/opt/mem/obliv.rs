//! Oblivious Array Elimination
//!
//! This module attempts to identify *oblivious* arrays: those that are only accessed at constant
//! indices[1]. These arrays can be replaced with normal terms.
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
//!    * a map from array terms to lists of values
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
//!
//! [1]: Our use of "oblivious" is inspired by *oblivious turing
//! machines* <https://en.wikipedia.org/wiki/Turing_machine_equivalents#Oblivious_Turing_machines>
//! which access their tape in a data-indepedant way.

use super::visit::*;
use crate::ir::term::*;

use std::iter::repeat;

struct NonOblivComputer {
    not_obliv: TermSet,
    progress: bool,
}

impl NonOblivComputer {
    fn mark(&mut self, a: &Term) {
        if !self.not_obliv.contains(a) {
            self.not_obliv.insert(a.clone());
            self.progress = true;
        }
    }

    fn bi_implicate(&mut self, a: &Term, b: &Term) {
        match (self.not_obliv.contains(a), self.not_obliv.contains(b)) {
            (false, true) => {
                self.not_obliv.insert(a.clone());
                self.progress = true;
            }
            (true, false) => {
                self.not_obliv.insert(b.clone());
                self.progress = true;
            }
            _ => {}
        }
    }
    fn new() -> Self {
        Self {
            progress: true,
            not_obliv: TermSet::new(),
        }
    }
}

impl MemVisitor for NonOblivComputer {
    fn visit_eq(&mut self, _orig: &Term, a: &Term, b: &Term) -> Option<Term> {
        self.bi_implicate(a, b);
        None
    }
    fn visit_ite(&mut self, orig: &Term, _c: &Term, t: &Term, f: &Term) {
        self.bi_implicate(orig, t);
        self.bi_implicate(t, f);
        self.bi_implicate(orig, f);
    }
    fn visit_store(&mut self, orig: &Term, a: &Term, k: &Term, _v: &Term) {
        if let Op::Const(_) = k.op {
            self.bi_implicate(orig, a);
        } else {
            self.mark(a);
            self.mark(orig);
        }
    }
    fn visit_select(&mut self, _orig: &Term, a: &Term, k: &Term) -> Option<Term> {
        if let Op::Const(_) = k.op {
        } else {
            self.mark(a);
        }
        None
    }
}

impl ProgressVisitor for NonOblivComputer {
    fn check_progress(&self) -> bool {
        self.progress
    }
    fn reset_progress(&mut self) {
        self.progress = false;
    }
}

struct Replacer {
    /// A map from (original) replaced terms, to what they were replaced with.
    sequences: TermMap<Vec<Term>>,
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
            self.sequences
                .insert(orig.clone(), repeat(val).cloned().take(size).collect());
        }
    }
    fn visit_eq(&mut self, orig: &Term, _a: &Term, _b: &Term) -> Option<Term> {
        if let Some(a_seq) = self.sequences.get(&orig.cs[0]) {
            let b_seq = self.sequences.get(&orig.cs[1]).expect("inconsistent eq");
            let eqs: Vec<Term> = a_seq
                .iter()
                .zip(b_seq.iter())
                .map(|(a, b)| term![Op::Eq; a.clone(), b.clone()])
                .collect();
            Some(term(Op::BoolNaryOp(BoolNaryOp::And), eqs))
        } else {
            None
        }
    }
    fn visit_ite(&mut self, orig: &Term, c: &Term, _t: &Term, _f: &Term) {
        if self.should_replace(orig) {
            let a_seq = self.sequences.get(&orig.cs[1]).expect("inconsistent ite");
            let b_seq = self.sequences.get(&orig.cs[2]).expect("inconsistent ite");
            let ites: Vec<Term> = a_seq
                .iter()
                .zip(b_seq.iter())
                .map(|(a, b)| term![Op::Ite; c.clone(), a.clone(), b.clone()])
                .collect();
            self.sequences.insert(orig.clone(), ites);
        }
    }
    fn visit_store(&mut self, orig: &Term, _a: &Term, k: &Term, v: &Term) {
        if self.should_replace(orig) {
            let mut a_seq = self
                .sequences
                .get(&orig.cs[0])
                .expect("inconsistent store")
                .clone();
            let k_const = k
                .as_bv_opt()
                .expect("not obliv!")
                .uint()
                .to_usize()
                .expect("oversize index");
            a_seq[k_const] = v.clone();
            self.sequences.insert(orig.clone(), a_seq);
        }
    }
    fn visit_select(&mut self, orig: &Term, _a: &Term, k: &Term) -> Option<Term> {
        if let Some(a_seq) = self.sequences.get(&orig.cs[0]) {
            let k_const = k
                .as_bv_opt()
                .expect("not obliv!")
                .uint()
                .to_usize()
                .expect("oversize index");
            if k_const < a_seq.len() {
                Some(a_seq[k_const].clone())
            } else {
                panic!("Oversize index: {}", k_const)
            }
        } else {
            None
        }
    }
    fn visit_var(&mut self, orig: &Term, name: &String, s: &Sort) {
        if let Sort::Array(_k, v, size) = s {
            if self.should_replace(orig) {
                self.sequences.insert(
                    orig.clone(),
                    (0..*size)
                        .map(|i| leaf_term(Op::Var(format!("{}_{}", name, i), (**v).clone())))
                        .collect(),
                );
            }
        } else {
            unreachable!("should only visit array vars")
        }
    }
}

pub fn elim_obliv(t: &Term) -> Term {
    let mut prop_pass = NonOblivComputer::new();
    prop_pass.traverse_to_fixpoint(t);
    let mut replace_pass = Replacer {
        not_obliv: prop_pass.not_obliv,
        sequences: TermMap::new(),
    };
    replace_pass.traverse(t)
}

#[cfg(test)]
mod test {
    use super::*;

    fn v_bv(n: &str, w: usize) -> Term {
        leaf_term(Op::Var(n.to_owned(), Sort::BitVector(w)))
    }

    fn array_free(t: &Term) -> bool {
        for c in PostOrderIter::new(t.clone()) {
            if let Sort::Array(..) = check(c).unwrap() {
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
