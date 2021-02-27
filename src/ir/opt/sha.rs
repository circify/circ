use crate::ir::term::*;
use std::collections::HashSet;
use log::debug;

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
            Op::BvNaryOp(BvNaryOp::Or) | Op::BvNaryOp(BvNaryOp::Xor) => {
                if t.cs.len() == 2 {
                    let a = get(0);
                    let b = get(1);
                    if &a.op == &b.op
                        && &a.op == &Op::BvNaryOp(BvNaryOp::And)
                        && b.cs[0].op == Op::BvUnOp(BvUnOp::Not)
                        && b.cs[0].cs[0] == a.cs[0]
                    {
                        if let Sort::BitVector(w) = check(&t) {
                            debug!("SHA CH");
                            Some(term(
                                Op::BvConcat,
                                (0..w)
                                    .map(|i| {
                                        term![Op::BoolToBv; term![Op::Ite; term![Op::BvBit(i); a.cs[0].clone()],
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
                        && &c2.op == &Op::BvNaryOp(BvNaryOp::And)
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
                                Op::BvConcat,
                                (0..w)
                                    .map(|i| {
                                        term![Op::BoolToBv; term![Op::BoolMaj;
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    const BV_AND: Op = Op::BvNaryOp(BvNaryOp::And);
    const BV_OR: Op = Op::BvNaryOp(BvNaryOp::Or);
    const BV_XOR: Op = Op::BvNaryOp(BvNaryOp::Xor);
    const BV_NOT: Op = Op::BvUnOp(BvUnOp::Not);

    #[test]
    fn with_or() {
        let a = bv_lit(0, 1);
        let b = bv_lit(0, 1);
        let c = bv_lit(0, 1);
        let t = term![BV_OR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![Op::BvConcat; term![Op::BoolToBv; term![Op::Ite; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[test]
    fn with_xor() {
        let a = bv_lit(0, 1);
        let b = bv_lit(0, 1);
        let c = bv_lit(0, 1);
        let t = term![BV_XOR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![Op::BvConcat; term![Op::BoolToBv; term![Op::Ite; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[test]
    fn length_2() {
        let a = bv_lit(0, 2);
        let b = bv_lit(0, 2);
        let c = bv_lit(0, 2);
        let t = term![BV_OR; term![BV_AND; a.clone(), b.clone()], term![BV_AND; term![BV_NOT; a.clone()], c.clone()]];
        let tt = term![Op::BvConcat;
        term![Op::BoolToBv; term![Op::Ite; term![Op::BvBit(1); a.clone()], term![Op::BvBit(1); b.clone()], term![Op::BvBit(1); c.clone()]]],
        term![Op::BoolToBv; term![Op::Ite; term![Op::BvBit(0); a], term![Op::BvBit(0); b], term![Op::BvBit(0); c]]]
        ];
        assert_eq!(tt, sha_rewrites(&t));
    }

    #[quickcheck]
    fn semantic_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = sha_rewrites(&t);
        eval(&t, &vs) == eval(&tt, &vs)
    }
}
