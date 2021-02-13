use crate::ir::term::*;
use rug::Integer;

/// Create a constant boolean
fn cbool(b: bool) -> Option<Term> {
    Some(leaf_term(Op::Const(Value::Bool(b))))
}

/// Create a constant bit-vector
fn cbv(b: BitVector) -> Option<Term> {
    Some(leaf_term(Op::Const(Value::BitVector(b))))
}

/// Fold away operators over constants.
pub fn fold(node: &Term) -> Term {
    // Maps terms to their rewritten versions.
    let mut cache = TermMap::<Term>::new();
    for t in PostOrderIter::new(node.clone()) {
        let c_get = |x: &Term| cache.get(x).unwrap();
        let get = |i: usize| c_get(&t.cs[i]);
        let new_t_opt = match &t.op {
            Op::Not => get(0).as_bool_opt().and_then(|c| cbool(!c)),
            Op::Implies => match get(0).as_bool_opt() {
                Some(true) => Some(get(1).clone()),
                Some(false) => cbool(true),
                None => match get(1).as_bool_opt() {
                    Some(true) => cbool(true),
                    Some(false) => Some(term![Op::Not; get(0).clone()]),
                    None => None,
                },
            },
            Op::BvBit(i) => match get(0).as_bv_opt() {
                Some(bv) => cbool(bv.bit(*i)),
                _ => None,
            },
            Op::BoolNaryOp(o) => Some(o.clone().flatten(t.cs.iter().map(|c| c_get(c).clone()))),
            Op::Eq => {
                let c0 = get(0);
                let c1 = get(1);
                match (&c0.op, &c1.op) {
                    (Op::Const(Value::Bool(b0)), Op::Const(Value::Bool(b1))) => cbool(*b0 == *b1),
                    (Op::Const(Value::BitVector(b0)), Op::Const(Value::BitVector(b1))) => {
                        cbool(*b0 == *b1)
                    }
                    (Op::Const(Value::Field(b0)), Op::Const(Value::Field(b1))) => cbool(*b0 == *b1),
                    _ => None,
                }
            }
            // TODO: Pf to Bv
            Op::BvBinOp(o) => {
                let c0 = get(0);
                let c1 = get(1);
                use BvBinOp::*;
                match (o, c0.as_bv_opt(), c1.as_bv_opt()) {
                    (Sub, Some(a), Some(b)) => cbv(a.clone() - b.clone()),
                    (Sub, _, Some(b)) if b.uint() == &Integer::from(0) => Some(c0.clone()),
                    (Udiv, Some(a), Some(b)) => cbv(a.clone() / b),
                    (Udiv, _, Some(b)) if b.uint() == &Integer::from(1) => Some(c0.clone()),
                    (Udiv, _, Some(b)) if b.uint() == &Integer::from(-1) => {
                        Some(term![Op::BvUnOp(BvUnOp::Neg); c0.clone()])
                    }
                    // TODO: Udiv by power of two?
                    (Urem, Some(a), Some(b)) => cbv(a.clone() % b),
                    // TODO: Urem by power of two?
                    (Shl, Some(a), Some(b)) => cbv(a.clone() << b.clone()),
                    (Shl, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![Op::BvConcat;
                          term![Op::BvExtract(b.width()-n-1, 0); c0.clone()],
                          leaf_term(Op::Const(Value::BitVector(BitVector::zeros(n))))
                        ])
                    }
                    (Ashr, Some(a), Some(b)) => cbv(a.clone().ashr(b)),
                    (Ashr, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![Op::BvSext(n);
                                   term![Op::BvExtract(b.width()-1, n); c0.clone()]])
                    }
                    (Lshr, Some(a), Some(b)) => cbv(a.clone().lshr(b)),
                    (Lshr, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![Op::BvUext(n);
                                   term![Op::BvExtract(b.width()-1, n); c0.clone()]])
                    }
                    _ => None,
                }
            }
            Op::BvNaryOp(o) => Some(o.clone().flatten(t.cs.iter().map(|c| c_get(c).clone()))),
            Op::BvBinPred(p) => {
                if let (Some(a), Some(b)) = (get(0).as_bv_opt(), get(1).as_bv_opt()) {
                    Some(leaf_term(Op::Const(Value::Bool(match p {
                        BvBinPred::Uge => a.uint() >= b.uint(),
                        BvBinPred::Ugt => a.uint() > b.uint(),
                        BvBinPred::Ule => a.uint() <= b.uint(),
                        BvBinPred::Ult => a.uint() < b.uint(),
                        BvBinPred::Sge => a.as_sint() >= b.as_sint(),
                        BvBinPred::Sgt => a.as_sint() > b.as_sint(),
                        BvBinPred::Sle => a.as_sint() <= b.as_sint(),
                        BvBinPred::Slt => a.as_sint() < b.as_sint(),
                    }))))
                } else {
                    None
                }
            }
            Op::BvUnOp(o) => get(0).as_bv_opt().map(|bv| {
                leaf_term(Op::Const(Value::BitVector(match o {
                    BvUnOp::Not => !bv.clone(),
                    BvUnOp::Neg => -bv.clone(),
                })))
            }),
            Op::Ite => {
                let c = get(0);
                let t = get(1);
                let f = get(2);
                match c.as_bool_opt() {
                    Some(true) => Some(t.clone()),
                    Some(false) => Some(f.clone()),
                    None => match t.as_bool_opt() {
                        Some(true) => Some(fold(
                            &term![Op::BoolNaryOp(BoolNaryOp::Or); c.clone(), f.clone()],
                        )),
                        Some(false) => Some(fold(
                            &term![Op::BoolNaryOp(BoolNaryOp::And); neg_bool(c.clone()), f.clone()],
                        )),
                        _ => match f.as_bool_opt() {
                            Some(true) => Some(fold(
                                &term![Op::BoolNaryOp(BoolNaryOp::Or); neg_bool(c.clone()), t.clone()],
                            )),
                            Some(false) => Some(fold(
                                &term![Op::BoolNaryOp(BoolNaryOp::And); c.clone(), t.clone()],
                            )),
                            _ => None,
                        },
                    },
                }
            }
            Op::PfNaryOp(o) => Some(o.clone().flatten(t.cs.iter().map(|c| c_get(c).clone()))),
            Op::PfUnOp(o) => get(0).as_pf_opt().map(|pf| {
                leaf_term(Op::Const(Value::Field(match o {
                    PfUnOp::Recip => pf.clone().recip(),
                    PfUnOp::Neg => -pf.clone(),
                })))
            }),
            _ => None,
        };
        let new_t = new_t_opt.unwrap_or_else(|| {
            term(
                t.op.clone(),
                t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect(),
            )
        });
        cache.insert(t.clone(), new_t);
    }
    cache.get(&node).unwrap().clone()
}

fn neg_bool(t: Term) -> Term {
    match &t.op {
        Op::Not => t.cs[0].clone(),
        _ => term![Op::Not; t],
    }
}

trait NaryFlat<T: Clone>: Sized {
    fn as_const(t: Term) -> Result<T, Term>;
    fn combine(self, children: Vec<Term>, consts: Vec<T>) -> Term;
    fn flatten<I: IntoIterator<Item = Term>>(self, children: I) -> Term {
        let mut real_children = Vec::new();
        let mut consts = Vec::new();
        for c in children {
            match Self::as_const(c) {
                Ok(t) => consts.push(t),
                Err(t) => real_children.push(t),
            }
        }
        self.combine(real_children, consts)
    }
}

impl NaryFlat<bool> for BoolNaryOp {
    fn as_const(t: Term) -> Result<bool, Term> {
        match t.op {
            Op::Const(Value::Bool(b)) => Ok(b),
            _ => Err(t),
        }
    }
    fn combine(self, children: Vec<Term>, consts: Vec<bool>) -> Term {
        match self {
            BoolNaryOp::Or => {
                if consts.iter().any(|b| *b) {
                    leaf_term(Op::Const(Value::Bool(true)))
                } else if children.len() == 0 {
                    leaf_term(Op::Const(Value::Bool(false)))
                } else {
                    term(Op::BoolNaryOp(BoolNaryOp::Or), children)
                }
            }
            BoolNaryOp::And => {
                if consts.iter().any(|b| !*b) {
                    leaf_term(Op::Const(Value::Bool(false)))
                } else if children.len() == 0 {
                    leaf_term(Op::Const(Value::Bool(true)))
                } else {
                    term(Op::BoolNaryOp(BoolNaryOp::And), children)
                }
            }
            BoolNaryOp::Xor => {
                let odd_trues = consts.into_iter().filter(|b| *b).count() % 2 == 1;
                if children.len() == 0 {
                    leaf_term(Op::Const(Value::Bool(odd_trues)))
                } else {
                    let t = term(Op::BoolNaryOp(BoolNaryOp::Xor), children);
                    if odd_trues {
                        term![Op::Not; t]
                    } else {
                        t
                    }
                }
            }
        }
    }
}

impl NaryFlat<BitVector> for BvNaryOp {
    fn as_const(t: Term) -> Result<BitVector, Term> {
        match &t.op {
            Op::Const(Value::BitVector(b)) => Ok(b.clone()),
            _ => Err(t),
        }
    }
    fn combine(self, mut children: Vec<Term>, mut consts: Vec<BitVector>) -> Term {
        match self {
            BvNaryOp::Or => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitOr::bitor);
                    if children.len() == 0 {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else if c.uint() == &Integer::from(0) {
                        term(Op::BvNaryOp(BvNaryOp::Or), children)
                    } else {
                        term(
                            Op::BvConcat,
                            (0..c.width())
                                .map(|i| {
                                    term![Op::BoolToBv; if c.bit(i) {
                                        leaf_term(Op::Const(Value::Bool(true)))
                                    } else {
                                        term(
                                            Op::BoolNaryOp(BoolNaryOp::Or),
                                            children
                                                .iter()
                                                .cloned()
                                                .map(|t| term![Op::BvBit(i); t])
                                                .collect(),
                                        )
                                    }]
                                })
                                .rev()
                                .collect(),
                        )
                    }
                } else {
                    term(Op::BvNaryOp(BvNaryOp::Or), children)
                }
            }
            BvNaryOp::And => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitAnd::bitand);
                    if children.len() == 0 {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else {
                        term(
                            Op::BvConcat,
                            (0..c.width())
                                .map(|i| {
                                    term![Op::BoolToBv; if c.bit(i) {
                                        term(
                                            Op::BoolNaryOp(BoolNaryOp::And),
                                            children
                                                .iter()
                                                .cloned()
                                                .map(|t| term![Op::BvBit(i); t])
                                                .collect(),
                                        )
                                    } else {
                                        leaf_term(Op::Const(Value::Bool(false)))
                                    }]
                                })
                                .rev()
                                .collect(),
                        )
                    }
                } else {
                    term(Op::BvNaryOp(BvNaryOp::And), children)
                }
            }
            BvNaryOp::Xor => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitXor::bitxor);
                    if children.len() == 0 {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else {
                        term(
                            Op::BvConcat,
                            (0..c.width())
                                .map(|i| {
                                    let t = term(
                                        Op::BoolNaryOp(BoolNaryOp::Xor),
                                        children
                                            .iter()
                                            .cloned()
                                            .map(|t| term![Op::BvBit(i); t])
                                            .collect(),
                                    );
                                    term![Op::BoolToBv; if c.bit(i) {
                                        term![Op::Not; t]
                                    } else {
                                        t
                                    }]
                                })
                                .rev()
                                .collect(),
                        )
                    }
                } else {
                    term(Op::BvNaryOp(BvNaryOp::Xor), children)
                }
            }
            BvNaryOp::Add => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Add::add);
                    if c.uint() != &Integer::from(0) || children.len() == 0 {
                        children.push(leaf_term(Op::Const(Value::BitVector(c))));
                    }
                }
                term(Op::BvNaryOp(BvNaryOp::Add), children)
            }
            BvNaryOp::Mul => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Mul::mul);
                    if c.uint() == &Integer::from(0) {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else {
                        if c.uint() != &Integer::from(1) || children.len() == 0 {
                            children.push(leaf_term(Op::Const(Value::BitVector(c))));
                        }
                        term(Op::BvNaryOp(BvNaryOp::Mul), children)
                    }
                } else {
                    term(Op::BvNaryOp(BvNaryOp::Mul), children)
                }
            }
        }
    }
}

impl NaryFlat<FieldElem> for PfNaryOp {
    fn as_const(t: Term) -> Result<FieldElem, Term> {
        match &t.op {
            Op::Const(Value::Field(b)) => Ok(b.clone()),
            _ => Err(t),
        }
    }
    fn combine(self, mut children: Vec<Term>, mut consts: Vec<FieldElem>) -> Term {
        match self {
            PfNaryOp::Add => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Add::add);
                    if c.i() != &Integer::from(0) || children.len() == 0 {
                        children.push(leaf_term(Op::Const(Value::Field(c))));
                    }
                }
                term(Op::PfNaryOp(PfNaryOp::Add), children)
            }
            PfNaryOp::Mul => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Mul::mul);
                    if c.i() == &Integer::from(0) || children.len() == 0 {
                        leaf_term(Op::Const(Value::Field(c)))
                    } else {
                        if c.i() != &Integer::from(1) {
                            children.push(leaf_term(Op::Const(Value::Field(c))));
                        }
                        term(Op::PfNaryOp(PfNaryOp::Mul), children)
                    }
                } else {
                    term(Op::PfNaryOp(PfNaryOp::Mul), children)
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    fn v_bv(n: &str, w: usize) -> Term {
        leaf_term(Op::Var(n.to_owned(), Sort::BitVector(w)))
    }

    fn bool(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    const B_AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
    const B_OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
    const B_XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);
    const BV_SHL: Op = Op::BvBinOp(BvBinOp::Shl);
    const BV_ASHR: Op = Op::BvBinOp(BvBinOp::Ashr);
    const BV_LSHR: Op = Op::BvBinOp(BvBinOp::Lshr);

    #[quickcheck]
    fn semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) {
        let tt = fold(&t);
        let orig = eval(&t, &vs);
        let new = eval(&tt, &vs);
        assert!(orig == new, "{} ({}) vs {} ({})", t, orig, tt, new);
    }

    #[test]
    fn b_xor() {
        assert_eq!(fold(&term![B_XOR; bool(false), bool(true)]), bool(true),);
    }

    #[test]
    fn b_or() {
        assert_eq!(fold(&term![B_OR; bool(false), bool(true)]), bool(true),);
    }

    #[test]
    fn b_and() {
        assert_eq!(fold(&term![B_AND; bool(false), bool(true)]), bool(false),);
    }

    #[test]
    fn shl() {
        assert_eq!(
            fold(&term![BV_SHL; v_bv("a", 8), bv_lit(2, 8)]),
            term![Op::BvConcat; term![Op::BvExtract(5, 0); v_bv("a", 8)], bv_lit(0, 2)],
        );
    }

    #[test]
    fn ashr() {
        assert_eq!(
            fold(&term![BV_ASHR; v_bv("a", 8), bv_lit(2, 8)]),
            term![Op::BvSext(2); term![Op::BvExtract(7, 2); v_bv("a", 8)]],
        );
    }

    #[test]
    fn lshr() {
        assert_eq!(
            fold(&term![BV_LSHR; v_bv("a", 8), bv_lit(2, 8)]),
            term![Op::BvUext(2); term![Op::BvExtract(7, 2); v_bv("a", 8)]],
        );
    }
}
