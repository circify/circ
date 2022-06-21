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
//!
//! We maintain a set of non-oblivious arrays, initially empty. We traverse the whole computation
//! system, marking som arrays as non-oblivious. Only non-constant terms with a sort that contains
//! an array can be non-oblivious.
//!
//!
//! The following are *directly marked* as non-oblivious:
//!
//!    * Selects with non-constant indices
//!    * Stores with non-constant indices
//!    * Any term containing an array sort that is not a array of primitives
//!    * Variables, call arguments, call outputs, and the computation outputs
//!
//! All terms propagate non-obliviousness to their children and recieve it from their children.
//!
//! Propagation is repeated to fixpoint.
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
//! In both cases we look at the non-oblivious array set to see whether to do the replacement.

use super::super::visit::*;
use crate::ir::term::extras::as_uint_constant;
use crate::ir::term::*;

use log::trace;

fn is_prim_array(t: &Sort) -> bool {
    if let Sort::Array(k, v, _) = t {
        k.is_scalar() && v.is_scalar()
    } else {
        false
    }
}

fn is_markable(t: &Term, s: &Sort) -> bool {
    !t.is_const() && !s.is_scalar() && super::sort_contains_array(s)
}

#[derive(Default)]
struct NonOblivComputer {
    not_obliv: TermSet,
}

impl NonOblivComputer {
    fn mark(&mut self, a: &Term) -> bool {
        let s = check(a);
        if is_markable(a, &s) && self.not_obliv.insert(a.clone()) {
            trace!("Not obliv: {}", extras::Letified(a.clone()));
            true
        } else {
            false
        }
    }

    fn propagate(&mut self, a: &Term) -> bool {
        if self.not_obliv.contains(a) || a.cs.iter().any(|c| self.not_obliv.contains(c)) {
            let mut progress = false;
            progress |= self.mark(a);
            for c in &a.cs {
                progress |= self.mark(c);
            }
            progress
        } else {
            false
        }
    }
}

impl ProgressAnalysisPass for NonOblivComputer {
    fn visit(&mut self, term: &Term) -> bool {
        let sort = check(term);
        let mut progress = false;

        // First, we directly mark this term if
        // (a) its sort contains an array and is not an array of primitives.
        let do_mark = if !sort.is_scalar() && !is_prim_array(&sort) {
            true
        } else {
            // (b) it is a select or store with a non-constant index OR a call
            match &term.op {
                Op::Store if !term.cs[1].is_const() => true,
                Op::Select if !term.cs[1].is_const() => true,
                Op::Var(..) => true,
                Op::Call(..) => true,
                _ => false,
            }
        };

        if do_mark {
            progress |= self.mark(term);
        }

        // Now, we mark the children of calls
        if let Op::Call(..) = &term.op {
            for c in &term.cs {
                progress |= self.mark(c);
            }
        }

        // Finally, we propagate marks
        progress |= self.propagate(term);
        progress
    }
}

struct Replacer {
    /// The maximum size of arrays that will be replaced.
    not_obliv: TermSet,
}

impl Replacer {
    fn is_obliv(&self, a: &Term) -> bool {
        println!("is obliv?");
        !self.not_obliv.contains(a)
    }
}

#[track_caller]
fn get_const(t: &Term) -> usize {
    as_uint_constant(t)
        .unwrap_or_else(|| panic!("non-const: {}", t))
        .to_usize()
        .expect("oversize")
}

impl RewritePass for Replacer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        //debug!("Visit {}", extras::Letified(orig.clone()));
        let get_cs = || -> Vec<Term> {
            rewritten_children()
                .into_iter()
                .map(super::term_arr_val_to_tup)
                .collect()
        };
        trace!("rewriting {}", extras::Letified(orig.clone()));
        match &orig.op {
            Op::Select if self.is_obliv(&orig.cs[0]) => {
                trace!("  is oblivious");
                let mut cs = get_cs();
                debug_assert_eq!(cs.len(), 2);
                let k_const = get_const(&cs.pop().unwrap());
                Some(term(Op::Field(k_const), cs))
            }
            Op::Store if self.is_obliv(orig) => {
                trace!("  is oblivious");
                let mut cs = get_cs();
                debug_assert_eq!(cs.len(), 3);
                let k_const = get_const(&cs.remove(1));
                Some(term(Op::Update(k_const), cs))
            }
            Op::Ite if self.is_obliv(orig) => {
                trace!("  is oblivious");
                Some(term(Op::Ite, get_cs()))
            }
            Op::Eq if self.is_obliv(&orig.cs[0]) => {
                trace!("  is oblivious");
                Some(term(Op::Eq, get_cs()))
            }
            _ => None,
        }
    }
}

/// Eliminate oblivious arrays. See module documentation.
pub fn elim_obliv(t: &mut Computation) {
    let mut prop_pass = NonOblivComputer::default();
    for o in t.outputs() {
        prop_pass.mark(o);
    }
    prop_pass.traverse(t);
    let mut replace_pass = Replacer {
        not_obliv: prop_pass.not_obliv,
    };
    let initial_output_sorts: Vec<Sort> = t.outputs.iter().map(check).collect();
    <Replacer as RewritePass>::traverse(&mut replace_pass, t);
    for (o, s) in t.outputs.iter_mut().zip(initial_output_sorts) {
        if check(o) != s {
            *o = super::resort(o, &s)
        }
    }
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

    #[test]
    fn ignore_vars() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((a (bv 8)) (A (array (bv 8) (bv 8) 3))) ())
          (bvadd
            (select A #x00)
            (select (store (#a (bv 8) #x00 4 ()) #x00 a) #x00)
            (select (store (#a (bv 8) #x01 5 ()) #x00 a) #x01)
          )
        )",
        );
        let expected = text::parse_computation(
            b"
        (computation
          (metadata () ((a (bv 8)) (A (array (bv 8) (bv 8) 3))) ())
          (bvadd
            (select A #x00)
            ((field 0) ((update 0) (#t  #x00 #x00 #x00 #x00) a))
            ((field 1) ((update 0) (#t  #x01 #x01 #x01 #x01 #x01) a))
          )
        )",
        );
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn preserve_output_type() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((a (bv 8)) (A (array (bv 8) (bv 8) 3))) ())
          (store
            (store (#a (bv 8) #x00 3 ()) #x01 (select A #x00))
            #x00 #x05
          )
        )",
        );
        let expected = before.clone();
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn identity_fn() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () ((A (array (bv 8) (bv 8) 3))) ())
          A
        )",
        );
        let expected = before.clone();
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn ignore_call_inputs() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () () ())
          ((call foo (a) ((array (bv 8) (bv 8) 4)) (bool)) (store (#a (bv 8) #x00 4 ()) #x00 #x01))
        )",
        );
        let expected = before.clone();
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn ignore_call_outputs() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () () ())
          (select
           ((field 0) ((call foo () () ((array (bv 8) (bv 8) 4))) ))
           #x00)
        )",
        );
        let expected = before.clone();
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }

    #[test]
    fn ignore_outputs() {
        let _ = env_logger::builder().is_test(true).try_init();
        let before = text::parse_computation(
            b"
        (computation
          (metadata () () ())
          (store (#a (bv 8) #x00 4 ()) #x00 #x01)
        )",
        );
        let expected = before.clone();
        let mut after = before.clone();
        elim_obliv(&mut after);
        assert_eq!(after, expected);
    }
}
