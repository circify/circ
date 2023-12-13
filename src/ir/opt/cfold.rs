//! Constant folding

use crate::cfg::cfg_or_default as cfg;
use crate::ir::term::*;

use circ_fields::FieldV;
use circ_opt::FieldToBv;
use itertools::Itertools;
use rug::Integer;
use std::cell::RefCell;
use std::cmp::Ordering;

thread_local! {
    static FOLDS: RefCell<TermCache<TTerm>> = RefCell::new(TermCache::with_capacity(TERM_CACHE_LIMIT));
}

pub(in super::super) fn collect() {
    FOLDS.with(|cache_handle| {
        let mut cache = cache_handle.borrow_mut();
        let mut to_pop = Vec::new();
        for (k, v) in cache.iter() {
            if !k.live() || !v.live() {
                to_pop.push(k.clone());
            }
        }
        for k in to_pop.into_iter() {
            cache.pop(&k);
        }
    })
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
pub fn fold(node: &Term, ignore: &[Op]) -> Term {
    FOLDS.with(|cache_handle| {
        let mut cache = cache_handle.borrow_mut();

        // make the cache unbounded during the fold_cache call
        let old_capacity = cache.cap();
        cache.resize(std::usize::MAX);

        let ret = fold_cache(node, &mut cache, ignore);
        // shrink cache to its max size
        cache.resize(old_capacity);
        ret
    })
}

/// Do constant-folding backed by a cache.
pub fn fold_cache(node: &Term, cache: &mut TermCache<TTerm>, ignore: &[Op]) -> Term {
    // (node, children pushed)
    let mut stack = vec![(node.clone(), false)];

    // Maps terms to their rewritten versions.
    while let Some((t, children_pushed)) = stack.pop() {
        if cache.contains(&t.downgrade()) {
            continue;
        }
        if !children_pushed {
            stack.push((t.clone(), true));
            stack.extend(t.cs().iter().map(|c| (c.clone(), false)));
            continue;
        }

        let mut c_get = |x: &Term| -> Term {
            cache
                .get(&x.downgrade())
                .and_then(|x| x.upgrade())
                .expect("postorder cache")
        };

        if ignore.contains(t.op()) {
            let new_t = term(t.op().clone(), t.cs().iter().map(c_get).collect());
            cache.put(t.downgrade(), new_t.downgrade());
            continue;
        }

        let mut get = |i: usize| c_get(&t.cs()[i]);
        let new_t_opt = match &t.op() {
            Op::Not => get(0).as_bool_opt().and_then(|c| cbool(!c)),
            Op::Implies => match get(0).as_bool_opt() {
                Some(true) => Some(get(1)),
                Some(false) => cbool(true),
                None => match get(1).as_bool_opt() {
                    Some(true) => cbool(true),
                    Some(false) => Some(term![NOT; get(0)]),
                    None => None,
                },
            },
            Op::BvBit(i) => match get(0).as_bv_opt() {
                Some(bv) => cbool(bv.bit(*i)),
                _ => None,
            },
            Op::BoolNaryOp(o) => match o {
                BoolNaryOp::Xor => Some((*o).flatten(t.cs().iter().map(c_get))),
                BoolNaryOp::Or => {
                    // (a || a) = a
                    // (a || !a) = true
                    let flattened = (*o).flatten(t.cs().iter().map(c_get));
                    Some(if *flattened.op() == OR {
                        let mut dedup_children = TermSet::default();
                        for t in flattened.cs().iter() {
                            if dedup_children.contains(&term![Op::Not; t.clone()]) {
                                dedup_children.remove(&term![Op::Not; t.clone()]);
                            } else {
                                dedup_children.insert(t.clone());
                            }
                        }

                        match dedup_children.len().cmp(&1) {
                            Ordering::Less => flattened,
                            Ordering::Equal => dedup_children.into_iter().collect_vec()[0].clone(),
                            Ordering::Greater => term(OR, dedup_children.into_iter().collect_vec()),
                        }
                    } else {
                        flattened
                    })
                }
                BoolNaryOp::And => {
                    // (a && a) = a
                    // (a && !a) = false
                    let flattened = (*o).flatten(t.cs().iter().map(c_get));
                    let mut dedup_children = TermSet::default();
                    Some(if *flattened.op() == AND {
                        for t in flattened.cs().iter() {
                            if dedup_children.contains(&term![Op::Not; t.clone()]) {
                                return bool_lit(false);
                            }
                            dedup_children.insert(t.clone());
                        }
                        match dedup_children.len().cmp(&1) {
                            Ordering::Less => flattened,
                            Ordering::Equal => dedup_children.iter().collect_vec()[0].clone(),
                            Ordering::Greater => {
                                term(AND, dedup_children.into_iter().collect_vec())
                            }
                        }
                    } else {
                        flattened
                    })
                }
            },
            Op::Eq => {
                let c0 = get(0);
                let c1 = get(1);
                match (c0.as_value_opt(), c1.as_value_opt()) {
                    (Some(Value::BitVector(b0)), Some(Value::BitVector(b1))) => cbool(*b0 == *b1),
                    (Some(Value::F32(b0)), Some(Value::F32(b1))) => cbool(*b0 == *b1),
                    (Some(Value::F64(b0)), Some(Value::F64(b1))) => cbool(*b0 == *b1),
                    (Some(Value::Int(b0)), Some(Value::Int(b1))) => cbool(*b0 == *b1),
                    (Some(Value::Field(b0)), Some(Value::Field(b1))) => cbool(*b0 == *b1),
                    (Some(Value::Bool(b0)), Some(Value::Bool(b1))) => cbool(*b0 == *b1),
                    (Some(Value::Tuple(t0)), Some(Value::Tuple(t1))) => cbool(*t0 == *t1),
                    (Some(Value::Array(a0)), Some(Value::Array(a1))) => {
                        cbool(a0.size == a1.size && a0.map == a1.map)
                    }
                    _ => None,
                }
            }
            Op::PfToBv(w) => {
                let child = get(0);
                child.as_pf_opt().map(|c| {
                    let i = c.i();
                    if let FieldToBv::Panic = cfg().ir.field_to_bv {
                        assert!(
                            (i.significant_bits() as usize) <= *w,
                            "{}",
                            "oversized input to Op::PfToBv({w})",
                        );
                    }
                    bv_lit(i % (Integer::from(1) << *w), *w)
                })
            }
            Op::BvBinOp(o) => {
                let c0 = get(0);
                let c1 = get(1);
                use BvBinOp::*;
                match (o, c0.as_bv_opt(), c1.as_bv_opt()) {
                    (Sub, Some(a), Some(b)) => cbv(a.clone() - b.clone()),
                    (Sub, _, Some(b)) if b.uint() == &Integer::from(0) => Some(c0),
                    (Udiv, _, Some(b)) if b.uint() == &Integer::from(0) => Some(bv_lit(
                        (Integer::from(1) << b.width() as u32) - 1,
                        b.width(),
                    )),
                    (Udiv, Some(a), Some(b)) => cbv(a.clone() / b),
                    (Udiv, _, Some(b)) if b.uint() == &Integer::from(1) => Some(c0),
                    (Udiv, _, Some(b)) if b.uint() == &Integer::from(-1) => {
                        Some(term![Op::BvUnOp(BvUnOp::Neg); c0])
                    }
                    // TODO: Udiv by power of two?
                    (Urem, Some(a), Some(b)) => cbv(a.clone() % b),
                    // TODO: Urem by power of two?
                    (Shl, Some(a), Some(b)) => cbv(a.clone() << b),
                    (Shl, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![BV_CONCAT;
                          term![Op::BvExtract(b.width()-n-1, 0); c0],
                          leaf_term(Op::Const(Value::BitVector(BitVector::zeros(n))))
                        ])
                    }
                    (Ashr, Some(a), Some(b)) => cbv(a.clone().ashr(b)),
                    (Ashr, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![Op::BvSext(n);
                                   term![Op::BvExtract(b.width()-1, n); c0]])
                    }
                    (Lshr, Some(a), Some(b)) => cbv(a.clone().lshr(b)),
                    (Lshr, _, Some(b)) => {
                        assert!(b.uint() < &Integer::from(b.width()));
                        let n = b.uint().to_usize().unwrap();
                        Some(term![Op::BvUext(n);
                                   term![Op::BvExtract(b.width()-1, n); c0]])
                    }
                    _ => None,
                }
            }
            Op::BvNaryOp(o) => Some(o.flatten(t.cs().iter().map(c_get))),
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
                if t == f {
                    Some(t)
                } else {
                    match c.as_bool_opt() {
                        Some(true) => Some(t),
                        Some(false) => Some(f),
                        None => match t.as_bool_opt() {
                            Some(true) => Some(fold_cache(&term![OR; c, f], cache, ignore)),
                            Some(false) => {
                                Some(fold_cache(&term![AND; neg_bool(c), f], cache, ignore))
                            }
                            _ => match f.as_bool_opt() {
                                Some(true) => {
                                    Some(fold_cache(&term![OR; neg_bool(c), t], cache, ignore))
                                }
                                Some(false) => Some(fold_cache(&term![AND; c, t], cache, ignore)),
                                _ => None,
                            },
                        },
                    }
                }
            }
            Op::PfNaryOp(o) => Some(o.flatten(t.cs().iter().map(c_get))),
            Op::PfUnOp(o) => get(0).as_pf_opt().map(|pf| {
                leaf_term(Op::Const(Value::Field(match o {
                    PfUnOp::Recip => pf.clone().recip(),
                    PfUnOp::Neg => -pf.clone(),
                })))
            }),
            Op::IntNaryOp(o) => Some(o.flatten(t.cs().iter().map(c_get))),
            Op::IntBinPred(p) => {
                if let (Some(a), Some(b)) = (get(0).as_bv_opt(), get(1).as_bv_opt()) {
                    Some(leaf_term(Op::Const(Value::Bool(match p {
                        IntBinPred::Ge => a >= b,
                        IntBinPred::Gt => a > b,
                        IntBinPred::Le => a <= b,
                        IntBinPred::Lt => a < b,
                    }))))
                } else {
                    None
                }
            }
            Op::UbvToPf(fty) => get(0)
                .as_bv_opt()
                .map(|bv| leaf_term(Op::Const(Value::Field(fty.new_v(bv.uint()))))),
            Op::Store => {
                match (
                    get(0).as_array_opt(),
                    get(1).as_value_opt(),
                    get(2).as_value_opt(),
                ) {
                    (Some(arr), Some(idx), Some(val)) => {
                        let new_arr = arr.clone().store(idx.clone(), val.clone());
                        Some(leaf_term(Op::Const(Value::Array(new_arr))))
                    }
                    _ => None,
                }
            }
            Op::Array(k, v) => t
                .cs()
                .iter()
                .map(|c| c_get(c).as_value_opt().cloned())
                .collect::<Option<_>>()
                .map(|cs| {
                    leaf_term(Op::Const(Value::Array(Array::from_vec(
                        k.clone(),
                        v.clone(),
                        cs,
                    ))))
                }),
            Op::Fill(k, s) => c_get(&t.cs()[0]).as_value_opt().map(|v| {
                leaf_term(Op::Const(Value::Array(Array::new(
                    k.clone(),
                    Box::new(v.clone()),
                    Default::default(),
                    *s,
                ))))
            }),
            Op::Select => match (get(0).as_array_opt(), get(1).as_value_opt()) {
                (Some(arr), Some(idx)) => Some(leaf_term(Op::Const(arr.select(idx)))),
                _ => None,
            },
            Op::Tuple => t
                .cs()
                .iter()
                .map(|c| c_get(c).as_value_opt().cloned())
                .collect::<Option<_>>()
                .map(|v| leaf_term(Op::Const(Value::Tuple(v)))),
            Op::Field(n) => get(0)
                .as_tuple_opt()
                .map(|t| leaf_term(Op::Const(t[*n].clone()))),
            Op::Update(n) => match (get(0).as_tuple_opt(), get(1).as_value_opt()) {
                (Some(t), Some(v)) => {
                    let mut new_vec = Vec::from(t).into_boxed_slice();
                    assert_eq!(new_vec[*n].sort(), v.sort());
                    new_vec[*n] = v.clone();
                    Some(leaf_term(Op::Const(Value::Tuple(new_vec))))
                }
                _ => None,
            },
            Op::BvConcat => t
                .cs()
                .iter()
                .map(|c| c_get(c).as_bv_opt().cloned())
                .collect::<Option<Vec<_>>>()
                .and_then(|v| v.into_iter().reduce(BitVector::concat))
                .map(|bv| leaf_term(Op::Const(Value::BitVector(bv)))),
            Op::BoolToBv => get(0).as_bool_opt().map(|b| {
                leaf_term(Op::Const(Value::BitVector(BitVector::new(
                    Integer::from(b),
                    1,
                ))))
            }),
            Op::BvUext(w) => get(0).as_bv_opt().map(|b| {
                leaf_term(Op::Const(Value::BitVector(BitVector::new(
                    b.uint().clone(),
                    b.width() + w,
                ))))
            }),
            _ => None,
        };
        let new_t = {
            let cc_get = |x: &Term| -> Term {
                cache
                    .get(&x.downgrade())
                    .and_then(|x| x.upgrade())
                    .expect("postorder cache")
            };
            new_t_opt.unwrap_or_else(|| term(t.op().clone(), t.cs().iter().map(cc_get).collect()))
        };
        cache.put(t.downgrade(), new_t.downgrade());
    }
    cache
        .get(&node.downgrade())
        .and_then(|x| x.upgrade())
        .expect("postorder cache")
}

fn neg_bool(t: Term) -> Term {
    match t.op() {
        &NOT => t.cs()[0].clone(),
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
        match t.op() {
            Op::Const(Value::Bool(b)) => Ok(*b),
            _ => Err(t),
        }
    }
    fn combine(self, children: Vec<Term>, consts: Vec<bool>) -> Term {
        match self {
            BoolNaryOp::Or => {
                if consts.iter().any(|b| *b) {
                    leaf_term(Op::Const(Value::Bool(true)))
                } else if children.is_empty() {
                    leaf_term(Op::Const(Value::Bool(false)))
                } else {
                    safe_nary(OR, children)
                }
            }
            BoolNaryOp::And => {
                if consts.iter().any(|b| !*b) {
                    leaf_term(Op::Const(Value::Bool(false)))
                } else if children.is_empty() {
                    leaf_term(Op::Const(Value::Bool(true)))
                } else {
                    safe_nary(AND, children)
                }
            }
            BoolNaryOp::Xor => {
                let odd_trues = consts.into_iter().filter(|b| *b).count() % 2 == 1;
                if children.is_empty() {
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
        match &t.op() {
            Op::Const(Value::BitVector(b)) => Ok(b.clone()),
            _ => Err(t),
        }
    }
    fn combine(self, mut children: Vec<Term>, mut consts: Vec<BitVector>) -> Term {
        match self {
            BvNaryOp::Or => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::BitOr::bitor);
                    if children.is_empty() {
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
                    if children.is_empty() {
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
                    if children.is_empty() {
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
                    if c.uint() != &Integer::from(0) || children.is_empty() {
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
                        if c.uint() != &Integer::from(1) || children.is_empty() {
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

impl NaryFlat<FieldV> for PfNaryOp {
    fn as_const(t: Term) -> Result<FieldV, Term> {
        match &t.op() {
            Op::Const(Value::Field(b)) => Ok(b.clone()),
            _ => Err(t),
        }
    }
    fn combine(self, mut children: Vec<Term>, mut consts: Vec<FieldV>) -> Term {
        match self {
            PfNaryOp::Add => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Add::add);
                    if !c.is_zero() || children.is_empty() {
                        children.push(leaf_term(Op::Const(Value::Field(c))));
                    }
                }
                safe_nary(PF_ADD, children)
            }
            PfNaryOp::Mul => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Mul::mul);
                    if c.is_zero() || children.is_empty() {
                        leaf_term(Op::Const(Value::Field(c)))
                    } else {
                        if !c.is_one() {
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

impl NaryFlat<Integer> for IntNaryOp {
    fn as_const(t: Term) -> Result<Integer, Term> {
        match &t.op() {
            Op::Const(Value::Int(b)) => Ok(b.clone()),
            _ => Err(t),
        }
    }
    fn combine(self, mut children: Vec<Term>, mut consts: Vec<Integer>) -> Term {
        match self {
            IntNaryOp::Add => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Add::add);
                    if c != 0u8 || children.is_empty() {
                        children.push(leaf_term(Op::Const(Value::Int(c))));
                    }
                }
                safe_nary(INT_ADD, children)
            }
            IntNaryOp::Mul => {
                if let Some(c) = consts.pop() {
                    let c = consts.into_iter().fold(c, std::ops::Mul::mul);
                    if c == 0u8 || children.is_empty() {
                        leaf_term(Op::Const(Value::Int(c)))
                    } else {
                        if c != 1u8 {
                            children.push(leaf_term(Op::Const(Value::Int(c))));
                        }
                        safe_nary(INT_MUL, children)
                    }
                } else {
                    safe_nary(INT_MUL, children)
                }
            }
        }
    }
}

fn safe_nary(op: Op, mut children: Vec<Term>) -> Term {
    match children.len() {
        0 => panic!("Empty {}", op),
        1 => children.pop().unwrap(),
        _ => term(op, children),
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
        let tt = fold(&t, &[]);
        let orig = eval(&t, &vs);
        let new = eval(&tt, &vs);
        assert!(orig == new, "{}", "{t} ({orig}) vs {tt} ({new})");
    }

    #[test]
    fn b_xor() {
        assert_eq!(fold(&term![XOR; bool(false), bool(true)], &[]), bool(true),);
    }

    #[test]
    fn b_or() {
        assert_eq!(fold(&term![OR; bool(false), bool(true)], &[]), bool(true),);
    }

    #[test]
    fn b_and() {
        assert_eq!(fold(&term![AND; bool(false), bool(true)], &[]), bool(false),);
    }

    #[test]
    fn shl() {
        assert_eq!(
            fold(&term![BV_SHL; v_bv("a", 8), bv_lit(2, 8)], &[]),
            term![BV_CONCAT; term![Op::BvExtract(5, 0); v_bv("a", 8)], bv_lit(0, 2)],
        );
    }

    #[test]
    fn ashr() {
        assert_eq!(
            fold(&term![BV_ASHR; v_bv("a", 8), bv_lit(2, 8)], &[]),
            term![Op::BvSext(2); term![Op::BvExtract(7, 2); v_bv("a", 8)]],
        );
    }

    #[test]
    fn lshr() {
        assert_eq!(
            fold(&term![BV_LSHR; v_bv("a", 8), bv_lit(2, 8)], &[]),
            term![Op::BvUext(2); term![Op::BvExtract(7, 2); v_bv("a", 8)]],
        );
    }

    #[test]
    fn int_add_constants() {
        let before = text::parse_term(b"(intadd 5 6 10 -4)");
        let ex_after = text::parse_term(b"17");
        assert_eq!(fold(&before, &[]), ex_after);
    }

    #[test]
    fn int_add_vars() {
        let before = text::parse_term(b"(declare ((a int)) (intadd a 5 6 10 -4))");
        let ex_after = text::parse_term(b"(declare ((a int)) (intadd a 17))");
        assert_eq!(fold(&before, &[]), ex_after);
    }

    #[test]
    fn int_add_vars_zero() {
        let before = text::parse_term(b"(declare ((a int)) (intadd a -5 -6 10 1))");
        let ex_after = text::parse_term(b"(declare ((a int)) a)");
        assert_eq!(fold(&before, &[]), ex_after);
    }

    #[test]
    fn int_mul_vars() {
        let before = text::parse_term(b"(declare ((a int)) (intmul a 1 2 4))");
        let ex_after = text::parse_term(b"(declare ((a int)) (intmul a 8))");
        assert_eq!(fold(&before, &[]), ex_after);
    }

    #[test]
    fn int_mul_vars_one() {
        let before = text::parse_term(b"(declare ((a int)) (intmul a 1 1))");
        let ex_after = text::parse_term(b"(declare ((a int)) a)");
        assert_eq!(fold(&before, &[]), ex_after);
    }

    #[test]
    fn int_mul_vars_zero() {
        let before = text::parse_term(b"(declare ((a int)) (intmul a 1 1 0))");
        let ex_after = text::parse_term(b"(declare ((a int)) 0)");
        assert_eq!(fold(&before, &[]), ex_after);
    }
}
