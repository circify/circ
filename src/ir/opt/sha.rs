//! SHA-2 peephole optimizations

use crate::ir::term::*;
use log::debug;
use std::collections::HashSet;

/// Detects common C-language SHA patterns and rewrites them.
pub fn sha_rewrites(term_: &Term) -> Term {
    // what does a term rewrite to?
    let mut cache = TermMap::<Term>::new();
    for t in PostOrderIter::new(term_.clone()) {
        let c_get = |x: &Term| cache.get(x).unwrap();
        let get = |i: usize| c_get(&t.cs[i]);
        let new_t = match &t.op {
            // A pattern: (a & b) | (~a & c)
            // or: (a & b) ^ (~a & c)
            &BV_OR | &BV_XOR => {
                if t.cs.len() == 2 {
                    let a = get(0);
                    let b = get(1);
                    if &a.op == &b.op
                        && &a.op == &BV_AND
                        && b.cs[0].op == BV_NOT
                        && b.cs[0].cs[0] == a.cs[0]
                    {
                        if let Sort::BitVector(w) = check(&t) {
                            debug!("SHA CH");
                            Some(term(
                                BV_CONCAT,
                                (0..w)
                                    .map(|i| {
                                        term![BOOL_TO_BV; term![ITE; term![Op::BvBit(i); a.cs[0].clone()],
                                                   term![Op::BvBit(i); a.cs[1].clone()],
                                                   term![Op::BvBit(i); b.cs[1].clone()]]]
                                    })
                                    .rev()
                                    .collect(),
                            ))
                        } else {
                            unreachable!()
                        }
                    } else {
                        None
                    }
                } else if t.cs.len() == 3 {
                    let c0 = get(0);
                    let c1 = get(1);
                    let c2 = get(2);
                    if &c0.op == &c1.op
                        && &c1.op == &c2.op
                        && &c2.op == &BV_AND
                        && c0.cs.len() == 2
                        && c1.cs.len() == 2
                        && c2.cs.len() == 2
                    {
                        let s0 = c0.cs.iter().collect::<HashSet<_>>();
                        let s1 = c1.cs.iter().collect::<HashSet<_>>();
                        let s2 = c2.cs.iter().collect::<HashSet<_>>();
                        if s0.intersection(&s1).count() == 1
                            && s1.intersection(&s2).count() == 1
                            && s2.intersection(&s0).count() == 1
                        {
                            debug!("SHA MAJ");
                            let items = s0.union(&s1).collect::<Vec<_>>();
                            let w = check(&c0).as_bv();
                            Some(term(
                                BV_CONCAT,
                                (0..w)
                                    .map(|i| {
                                        term![BOOL_TO_BV; term![Op::BoolMaj;
                                               term![Op::BvBit(i); (*items[0]).clone()],
                                               term![Op::BvBit(i); (*items[1]).clone()],
                                               term![Op::BvBit(i); (*items[2]).clone()]]]
                                    })
                                    .rev()
                                    .collect(),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        };
        let new_t = new_t.unwrap_or_else(|| {
            term(
                t.op.clone(),
                t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect(),
            )
        });
        cache.insert(t, new_t);
    }
    cache.get(&term_).unwrap().clone()
}

/// Eliminate the SHA majority operator, replacing it with ands and ors.
pub fn sha_maj_elim(term_: &Term) -> Term {
    // what does a term rewrite to?
    let mut cache = TermMap::<Term>::new();
    for t in PostOrderIter::new(term_.clone()) {
        let c_get = |x: &Term| cache.get(x).unwrap();
        let get = |i: usize| c_get(&t.cs[i]);
        let new_t = match &t.op {
            // maj(a, b, c) = (a & b) | (b & c) | (c & a)
            &Op::BoolMaj => {
                let a = get(0);
                let b = get(1);
                let c = get(2);
                let ab = term![AND; a.clone(), b.clone()];
                let bc = term![AND; b.clone(), c.clone()];
                let ca = term![AND; c.clone(), a.clone()];
                Some(term![OR; ab, bc, ca])
            }
            _ => None,
        };
        let new_t = new_t.unwrap_or_else(|| {
            term(
                t.op.clone(),
                t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect(),
            )
        });
        cache.insert(t, new_t);
    }
    cache.get(&term_).unwrap().clone()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    #[test]
    fn with_or() {
        let a = bv_lit(0, 1);
        let b = bv_lit(0, 1);
        let c = bv_lit(0, 1);
        let t = term![BV_OR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![BV_CONCAT; term![BOOL_TO_BV; term![ITE; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[test]
    fn with_xor() {
        let a = bv_lit(0, 1);
        let b = bv_lit(0, 1);
        let c = bv_lit(0, 1);
        let t = term![BV_XOR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![BV_CONCAT; term![BOOL_TO_BV; term![ITE; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[test]
    fn length_2() {
        let a = bv_lit(0, 2);
        let b = bv_lit(0, 2);
        let c = bv_lit(0, 2);
        let t = term![BV_OR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![BV_CONCAT;
        term![BOOL_TO_BV; term![ITE; term![Op::BvBit(1); a.clone()], term![Op::BvBit(1); b.clone()], term![Op::BvBit(1); c.clone()]]],
        term![BOOL_TO_BV; term![ITE; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]
        ];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[test]
    fn undo() {
        let a = bool_lit(false);
        let b = bool_lit(false);
        let c = bool_lit(false);
        let t = term![Op::BoolMaj; a.clone(), b.clone(),c.clone()];
        let tt = term![OR; term![AND; a.clone(), b.clone()], term![AND; b.clone(), c.clone()], term![AND; c.clone(), a.clone()]];
        assert_eq!(tt, sha_maj_elim(&t));
    }

    #[quickcheck]
    fn semantic_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = sha_rewrites(&t);
        eval(&t, &vs) == eval(&tt, &vs)
    }
}
