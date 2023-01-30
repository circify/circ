//! SHA-2 peephole optimizations

use crate::ir::term::*;
use log::debug;
use std::collections::HashSet;

/// Detects common C-language SHA patterns and rewrites them.
pub fn sha_rewrites(term_: &Term) -> Term {
    // what does a term rewrite to?
    let mut cache = TermMap::<Term>::default();
    for t in PostOrderIter::new(term_.clone()) {
        let c_get = |x: &Term| cache.get(x).unwrap();
        let get = |i: usize| c_get(&t.cs()[i]);
        let new_t = match t.op() {
            // A pattern: (a & b) | (~a & c)
            // or: (a & b) ^ (~a & c)
            &BV_OR | &BV_XOR => {
                if t.cs().len() == 2 {
                    let l = get(0);
                    let r = get(1);
                    if l.op() == r.op()
                        && l.op() == &BV_AND
                        && l.cs().len() == 2
                        && r.cs().len() == 2
                    {
                        let opt_match = r
                            .cs()
                            .iter()
                            .position(|r_c| r_c == &term![BV_NOT; l.cs()[0].clone()])
                            .map(|r_i| (&l.cs()[0], &l.cs()[1], &r.cs()[1 - r_i]))
                            .or_else(|| {
                                r.cs()
                                    .iter()
                                    .position(|r_c| r_c == &term![BV_NOT; l.cs()[1].clone()])
                                    .map(|r_i| (&l.cs()[1], &l.cs()[0], &r.cs()[1 - r_i]))
                                    .or_else(|| {
                                        l.cs()
                                            .iter()
                                            .position(|l_c| {
                                                l_c == &term![BV_NOT; r.cs()[0].clone()]
                                            })
                                            .map(|l_i| (&r.cs()[0], &r.cs()[1], &l.cs()[1 - l_i]))
                                            .or_else(|| {
                                                l.cs()
                                                    .iter()
                                                    .position(|l_c| {
                                                        l_c == &term![BV_NOT; r.cs()[1].clone()]
                                                    })
                                                    .map(|l_i| {
                                                        (&r.cs()[1], &r.cs()[0], &l.cs()[1 - l_i])
                                                    })
                                            })
                                    })
                            });
                        if let Some((c, t, f)) = opt_match {
                            if let Sort::BitVector(w) = check(t) {
                                debug!("SHA CH");
                                Some(term(
                                BV_CONCAT,
                                (0..w)
                                    .map(|i| {
                                        term![BOOL_TO_BV; term![ITE; term![Op::BvBit(i); c.clone()],
                                                   term![Op::BvBit(i); t.clone()],
                                                   term![Op::BvBit(i); f.clone()]]]
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
                    } else {
                        None
                    }
                } else if t.cs().len() == 3 {
                    let c0 = get(0);
                    let c1 = get(1);
                    let c2 = get(2);
                    if c0.op() == c1.op()
                        && c1.op() == c2.op()
                        && c2.op() == &BV_AND
                        && c0.cs().len() == 2
                        && c1.cs().len() == 2
                        && c2.cs().len() == 2
                    {
                        let s0 = c0.cs().iter().collect::<HashSet<_>>();
                        let s1 = c1.cs().iter().collect::<HashSet<_>>();
                        let s2 = c2.cs().iter().collect::<HashSet<_>>();
                        if s0.intersection(&s1).count() == 1
                            && s1.intersection(&s2).count() == 1
                            && s2.intersection(&s0).count() == 1
                        {
                            debug!("SHA MAJ");
                            let items = s0.union(&s1).collect::<Vec<_>>();
                            let w = check(c0).as_bv();
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
                t.op().clone(),
                t.cs()
                    .iter()
                    .map(|c| cache.get(c).unwrap().clone())
                    .collect(),
            )
        });
        cache.insert(t, new_t);
    }
    cache.get(term_).unwrap().clone()
}

/// Eliminate the SHA majority operator, replacing it with ands and ors.
pub fn sha_maj_elim(term_: &Term) -> Term {
    // what does a term rewrite to?
    let mut cache = TermMap::<Term>::default();
    for t in PostOrderIter::new(term_.clone()) {
        let c_get = |x: &Term| cache.get(x).unwrap();
        let get = |i: usize| c_get(&t.cs()[i]);
        let new_t = match t.op() {
            // maj(a, b, c) = (a & b) | (b & c) | (c & a)
            Op::BoolMaj => {
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
                t.op().clone(),
                t.cs()
                    .iter()
                    .map(|c| cache.get(c).unwrap().clone())
                    .collect(),
            )
        });
        cache.insert(t, new_t);
    }
    cache.get(term_).unwrap().clone()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;
    use text::parse_term;

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
        let tt =
            term![OR; term![AND; a.clone(), b.clone()], term![AND; b, c.clone()], term![AND; c, a]];
        assert_eq!(tt, sha_maj_elim(&t));
    }

    fn contains_ite(t: &Term) -> bool {
        PostOrderIter::new(t.clone()).any(|c| c.op() == &ITE)
    }

    #[test]
    fn catch_all_case() {
        let abc_term_rewrites = |t: &str| -> bool {
            contains_ite(&sha_rewrites(&parse_term(
                format!("(declare ((a (bv 4))(b (bv 4))(c (bv 4))) {t})").as_bytes(),
            )))
        };
        assert!(abc_term_rewrites("(bvor (bvand a b) (bvand (bvnot a) c))"));
        assert!(abc_term_rewrites("(bvor (bvand b a) (bvand (bvnot a) c))"));
        assert!(abc_term_rewrites("(bvor (bvand a b) (bvand c (bvnot a)))"));
        assert!(abc_term_rewrites("(bvor (bvand b a) (bvand c (bvnot a)))"));
        assert!(abc_term_rewrites("(bvor (bvand (bvnot a) c) (bvand a b))"));
        assert!(abc_term_rewrites("(bvor (bvand (bvnot a) c) (bvand b a))"));
        assert!(abc_term_rewrites("(bvor (bvand c (bvnot a)) (bvand a b))"));
        assert!(abc_term_rewrites("(bvor (bvand c (bvnot a)) (bvand b a))"));
        assert!(abc_term_rewrites("(bvxor (bvand a b) (bvand (bvnot a) c))"));
        assert!(abc_term_rewrites("(bvxor (bvand b a) (bvand (bvnot a) c))"));
        assert!(abc_term_rewrites("(bvxor (bvand a b) (bvand c (bvnot a)))"));
        assert!(abc_term_rewrites("(bvxor (bvand b a) (bvand c (bvnot a)))"));
        assert!(abc_term_rewrites("(bvxor (bvand (bvnot a) c) (bvand a b))"));
        assert!(abc_term_rewrites("(bvxor (bvand (bvnot a) c) (bvand b a))"));
        assert!(abc_term_rewrites("(bvxor (bvand c (bvnot a)) (bvand a b))"));
        assert!(abc_term_rewrites("(bvxor (bvand c (bvnot a)) (bvand b a))"));
    }

    #[quickcheck]
    fn semantic_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = sha_rewrites(&t);
        eval(&t, &vs) == eval(&tt, &vs)
    }
}
