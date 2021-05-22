//! Constant folding

use crate::ir::term::*;
use lazy_static::lazy_static;
use rug::Integer;
use std::ops::DerefMut;
use std::sync::RwLock;

lazy_static! {
    // TODO: use weak pointers to allow GC
    static ref FOLDS: RwLock<TermMap<Term>> = RwLock::new(TermMap::new());
}

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
    let mut cache = FOLDS.write().unwrap();
    fold_cache(node, cache.deref_mut())
}

/// Do constant-folding backed by a cache.
pub fn fold_cache(node: &Term, cache: &mut TermMap<Term>) -> Term {
    // (node, children pushed)
    let mut stack = vec![(node.clone(), false)];

    // Maps terms to their rewritten versions.
    while let Some((t, children_pushed)) = stack.pop() {
        if cache.contains_key(&t) {
            continue;
        }
        if !children_pushed {
            stack.push((t.clone(), true));
            stack.extend(t.cs.iter().map(|c| (c.clone(), false)));
            continue;
        }
        let c_get = |x: &Term| -> Term { cache.get(&x).expect("postorder cache").clone() };
        let get = |i: usize| c_get(&t.cs[i]);
        let new_t_opt = match &t.op {
            &NOT => get(0).as_bool_opt().and_then(|c| cbool(!c)),
            &IMPLIES => match get(0).as_bool_opt() {
                Some(true) => Some(get(1).clone()),
                Some(false) => cbool(true),
                None => match get(1).as_bool_opt() {
                    Some(true) => cbool(true),
                    Some(false) => Some(term![NOT; get(0).clone()]),
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
            Op::PfToBv(w) => {
                let child = get(0);
                child
                    .as_pf_opt()
                    .map(|c| bv_lit(c.i() % (Integer::from(1) << *w as u32), *w))
            }
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
                        Some(term![BV_CONCAT;
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
                        Some(true) => Some(fold_cache(&term![OR; c.clone(), f.clone()], cache)),
                        Some(false) => Some(fold_cache(
                            &term![AND; neg_bool(c.clone()), f.clone()],
                            cache,
                        )),
                        _ => match f.as_bool_opt() {
                            Some(true) => Some(fold_cache(
                                &term![OR; neg_bool(c.clone()), t.clone()],
                                cache,
                            )),
                            Some(false) => {
                                Some(fold_cache(&term![AND; c.clone(), t.clone()], cache))
                            }
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
        let c_get = |x: &Term| -> Term { cache.get(&x).expect("postorder cache").clone() };
        let new_t = new_t_opt
            .unwrap_or_else(|| term(t.op.clone(), t.cs.iter().map(|c| c_get(c)).collect()));
        cache.insert(t, new_t);
    }
    cache.get(&node).expect("postorder cache").clone()
}

fn neg_bool(t: Term) -> Term {
    match &t.op {
        &NOT => t.cs[0].clone(),
        _ => term![NOT; t],
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
                    safe_nary(OR, children)
                }
            }
            BoolNaryOp::And => {
                if consts.iter().any(|b| !*b) {
                    leaf_term(Op::Const(Value::Bool(false)))
                } else if children.len() == 0 {
                    leaf_term(Op::Const(Value::Bool(true)))
                } else {
                    safe_nary(AND, children)
                }
            }
            BoolNaryOp::Xor => {
                let odd_trues = consts.into_iter().filter(|b| *b).count() % 2 == 1;
                if children.len() == 0 {
                    leaf_term(Op::Const(Value::Bool(odd_trues)))
                } else {
                    let t = safe_nary(XOR, children);
                    if odd_trues {
                        term![NOT; t]
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
                        safe_nary(BV_OR, children)
                    } else {
                        safe_nary(
                            BV_CONCAT,
                            (0..c.width())
                                .map(|i| {
                                    term![Op::BoolToBv; if c.bit(i) {
                                        leaf_term(Op::Const(Value::Bool(true)))
                                    } else {
                                        safe_nary(
                                            OR,
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
                    safe_nary(BV_OR, children)
                }
            }
            BvNaryOp::And => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitAnd::bitand);
                    if children.len() == 0 {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else {
                        safe_nary(
                            BV_CONCAT,
                            (0..c.width())
                                .map(|i| {
                                    term![Op::BoolToBv; if c.bit(i) {
                                        safe_nary(
                                            AND,
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
                    safe_nary(BV_AND, children)
                }
            }
            BvNaryOp::Xor => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitXor::bitxor);
                    if children.len() == 0 {
                        leaf_term(Op::Const(Value::BitVector(c)))
                    } else {
                        safe_nary(
                            BV_CONCAT,
                            (0..c.width())
                                .map(|i| {
                                    let t = safe_nary(
                                        XOR,
                                        children
                                            .iter()
                                            .cloned()
                                            .map(|t| term![Op::BvBit(i); t])
                                            .collect(),
                                    );
                                    term![Op::BoolToBv; if c.bit(i) {
                                        term![NOT; t]
                                    } else {
                                        t
                                    }]
                                })
                                .rev()
                                .collect(),
                        )
                    }
                } else {
                    safe_nary(BV_XOR, children)
                }
            }
            BvNaryOp::Add => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Add::add);
                    if c.uint() != &Integer::from(0) || children.len() == 0 {
                        children.push(leaf_term(Op::Const(Value::BitVector(c))));
                    }
                }
                safe_nary(BV_ADD, children)
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
                        safe_nary(BV_MUL, children)
                    }
                } else {
                    safe_nary(BV_MUL, children)
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
                safe_nary(PF_ADD, children)
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
                        safe_nary(PF_MUL, children)
                    }
                } else {
                    safe_nary(PF_MUL, children)
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

    #[quickcheck]
    fn semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) {
        let tt = fold(&t);
        let orig = eval(&t, &vs);
        let new = eval(&tt, &vs);
        assert!(orig == new, "{} ({}) vs {} ({})", t, orig, tt, new);
    }

    #[test]
    fn b_xor() {
        assert_eq!(fold(&term![XOR; bool(false), bool(true)]), bool(true),);
    }

    #[test]
    fn b_or() {
        assert_eq!(fold(&term![OR; bool(false), bool(true)]), bool(true),);
    }

    #[test]
    fn b_and() {
        assert_eq!(fold(&term![AND; bool(false), bool(true)]), bool(false),);
    }

    #[test]
    fn shl() {
        assert_eq!(
            fold(&term![BV_SHL; v_bv("a", 8), bv_lit(2, 8)]),
            term![BV_CONCAT; term![Op::BvExtract(5, 0); v_bv("a", 8)], bv_lit(0, 2)],
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

fn safe_nary(op: Op, mut children: Vec<Term>) -> Term {
    match children.len() {
        0 => panic!("Empty {}", op),
        1 => children.pop().unwrap(),
        _ => term(op, children),
    }
}
