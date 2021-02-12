use super::visit::MemVisitor;
use crate::ir::term::*;

use std::iter::repeat;

use rug::Integer;

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
            // TODO: check for bv-indices better.  let w = check(k.clone()).unwrap().as_bv();
            let w = check(k.clone()).unwrap().as_bv();
            let ites: Vec<Term> = a_seq
                .iter()
                .enumerate()
                .map(|(i, a_i)| {
                    let idx = leaf_term(Op::Const(Value::BitVector(BitVector::new(
                        Integer::from(i),
                        w,
                    ))));
                    let eq_idx = term![Op::Eq; idx, k.clone()];
                    term![Op::Ite; eq_idx, v.clone(), a_i.clone()]
                })
                .collect();
            self.sequences.insert(orig.clone(), ites);
        }
    }
    fn visit_select(&mut self, orig: &Term, _a: &Term, k: &Term) -> Option<Term> {
        if let Some(a_seq) = self.sequences.get(&orig.cs[0]) {
            // TODO: check for bv-indices better.
            let w = check(k.clone()).unwrap().as_bv();
            let first = a_seq.first().expect("empty array in visit_select").clone();
            Some(
                a_seq
                    .iter()
                    .skip(1)
                    .enumerate()
                    .fold(first, |acc, (i, a_i)| {
                        let idx = leaf_term(Op::Const(Value::BitVector(BitVector::new(
                            Integer::from(i + 1),
                            w,
                        ))));
                        let eq_idx = term![Op::Eq; idx, k.clone()];
                        term![Op::Ite; eq_idx, a_i.clone(), acc]
                    }),
            )
        } else {
            None
        }
    }
    fn visit_var(&mut self, orig: &Term, name: &String, s: &Sort) {
        if let Sort::Array(_k, v, size) = s {
            self.sequences.insert(
                orig.clone(),
                (0..*size)
                    .map(|i| leaf_term(Op::Var(format!("{}_{}", name, i), (**v).clone())))
                    .collect(),
            );
        } else {
            unreachable!("should only visit array vars")
        }
    }
}

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

    fn v_bv(n: &str, w: usize) -> Term {
        leaf_term(Op::Var(n.to_owned(), Sort::BitVector(w)))
    }

    fn bv(u: usize, w: usize) -> Term {
        leaf_term(Op::Const(Value::BitVector(BitVector::new(
            Integer::from(u),
            w,
        ))))
    }

    fn array_free(t: &Term) -> bool {
        for c in PostOrderIter::new(t.clone()) {
            if let Sort::Array(..) = check(c).unwrap() {
                return false
            }
        }
        true
    }

    fn count_ites(t: &Term) -> usize {
        PostOrderIter::new(t.clone()).filter(|t| &t.op == &Op::Ite).count()
    }

    #[test]
    fn doesnt_crash() {
        let z = term![Op::ConstArray(Sort::BitVector(4), 6); bv(0, 4)];
        let t = term![Op::Select;
            term![Op::Ite;
              leaf_term(Op::Const(Value::Bool(true))),
              term![Op::Store; z.clone(), bv(3, 4), bv(1, 4)],
              term![Op::Store; z.clone(), bv(2, 4), bv(1, 4)]
            ],
            bv(3, 4)
        ];
        let tt = linearize(&t, 6);
        assert!(array_free(&tt));
        assert_eq!(6 + 6 + 6 + 5, count_ites(&tt));
    }
}
