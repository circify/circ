//! Linear Memory implementation.
//!
//! The idea is to replace each array with a term sequence and use ITEs to linearly scan the array
//! when needed. A SELECT produces an ITE reduce chain, a STORE produces an ITE map over the
//! sequence.
//!
//! E.g., for length-3 arrays.
//!
//! (select A k) => (ite (= k 2) A2 (ite (= k 1) A1 A0))
//! (store A k v) => (ite (= k 0) v A0), (ite (= k 1) v A1), (ite (= k 2))

use super::visit::MemVisitor;
use crate::ir::term::*;

use std::iter::repeat;

struct ArrayLinearizer {
    /// A map from (original) replaced terms, to what they were replaced with.
    sequences: TermMap<Vec<Term>>,
    /// The maximum size of arrays that will be replaced.
    size_thresh: usize,
}

impl MemVisitor for ArrayLinearizer {
    fn visit_const_array(&mut self, orig: &Term, _key_sort: &Sort, val: &Term, size: usize) {
        if size <= self.size_thresh {
            self.sequences
                .insert(orig.clone(), repeat(val).cloned().take(size).collect());
        }
    }
    fn visit_eq(&mut self, orig: &Term, _a: &Term, _b: &Term) -> Option<Term> {
        // don't map b/c self borrow lifetime & NLL
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
        if let Some(a_seq) = self.sequences.get(&orig.cs[1]) {
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
        if let Some(a_seq) = self.sequences.get(&orig.cs[0]) {
            let key_sort = check(k);
            let ites: Vec<Term> = a_seq
                .iter()
                .zip(key_sort.elems_iter())
                .map(|(a_i, key_i)| {
                    let eq_idx = term![Op::Eq; key_i, k.clone()];
                    term![Op::Ite; eq_idx, v.clone(), a_i.clone()]
                })
                .collect();
            self.sequences.insert(orig.clone(), ites);
        }
    }
    fn visit_select(&mut self, orig: &Term, _a: &Term, k: &Term) -> Option<Term> {
        if let Some(a_seq) = self.sequences.get(&orig.cs[0]) {
            let key_sort = check(k);
            let first = a_seq.first().expect("empty array in visit_select").clone();
            Some(a_seq.iter().zip(key_sort.elems_iter()).skip(1).fold(
                first,
                |acc, (a_i, key_i)| {
                    let eq_idx = term![Op::Eq; key_i, k.clone()];
                    term![Op::Ite; eq_idx, a_i.clone(), acc]
                },
            ))
        } else {
            None
        }
    }
    fn visit_var(&mut self, orig: &Term, name: &String, s: &Sort) {
        if let Sort::Array(_k, v, size) = s {
            if *size <= self.size_thresh {
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

/// Eliminate arrays using linear scans. See module documentation.
pub fn linearize(t: &Term, size_thresh: usize) -> Term {
    let mut pass = ArrayLinearizer {
        size_thresh,
        sequences: TermMap::new(),
    };
    pass.traverse(t)
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::field::TEST_FIELD;
    use rug::Integer;
    use std::sync::Arc;

    fn array_free(t: &Term) -> bool {
        for c in PostOrderIter::new(t.clone()) {
            if let Sort::Array(..) = check(&c) {
                return false;
            }
        }
        true
    }

    fn count_ites(t: &Term) -> usize {
        PostOrderIter::new(t.clone())
            .filter(|t| &t.op == &Op::Ite)
            .count()
    }

    fn field_lit(u: usize) -> Term {
        leaf_term(Op::Const(Value::Field(FieldElem::new(
            Integer::from(u),
            Arc::new(Integer::from(TEST_FIELD)),
        ))))
    }

    #[test]
    fn select_ite_stores() {
        let z = term![Op::ConstArray(Sort::BitVector(4), 6); bv_lit(0, 4)];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), bv_lit(3, 4), bv_lit(1, 4)],
              term![Op::Store; z.clone(), bv_lit(2, 4), bv_lit(1, 4)]
            ],
            bv_lit(3, 4)
        ];
        let tt = linearize(&t, 6);
        assert!(array_free(&tt));
        assert_eq!(6 + 6 + 6 + 5, count_ites(&tt));
    }

    #[test]
    fn select_ite_stores_field() {
        let z = term![Op::ConstArray(Sort::Field(Arc::new(Integer::from(TEST_FIELD))), 6); bv_lit(0, 4)];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), field_lit(3), bv_lit(1, 4)],
              term![Op::Store; z.clone(), field_lit(2), bv_lit(1, 4)]
            ],
            field_lit(3)
        ];
        let tt = linearize(&t, 6);
        assert!(array_free(&tt));
        assert_eq!(6 + 6 + 6 + 5, count_ites(&tt));
    }
}
