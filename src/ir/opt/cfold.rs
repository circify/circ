use crate::ir::term::*;

pub fn cbool(b: bool) -> Option<Term> {
    Some(leaf_term(Op::Const(Value::Bool(b))))
}

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
            Op::BoolNaryOp(BoolNaryOp::Or) => {
                let mut cs = Vec::new();
                let mut always_true = false;
                for c in &t.cs {
                    let c = c_get(c);
                    match c.as_bool_opt() {
                        Some(true) => {
                            always_true = true;
                            break;
                        }
                        Some(false) => {}
                        None => {
                            cs.push(c.clone());
                        }
                    }
                }
                if always_true {
                    cbool(true)
                } else if cs.len() == 0 {
                    cbool(false)
                } else {
                    Some(term(t.op.clone(), cs))
                }
            }
            Op::BoolNaryOp(BoolNaryOp::And) => {
                let mut cs = Vec::new();
                let mut always_false = false;
                for c in &t.cs {
                    let c = c_get(c);
                    match c.as_bool_opt() {
                        Some(false) => {
                            always_false = true;
                            break;
                        }
                        Some(true) => {}
                        None => {
                            cs.push(c.clone());
                        }
                    }
                }
                if always_false {
                    cbool(false)
                } else if cs.len() == 0 {
                    cbool(true)
                } else {
                    Some(term(t.op.clone(), cs))
                }
            }
            Op::BoolNaryOp(BoolNaryOp::Xor) => {
                let mut cs = Vec::new();
                let mut wrap_not = false;
                for c in &t.cs {
                    let c = c_get(c);
                    match c.as_bool_opt() {
                        Some(false) => {}
                        Some(true) => wrap_not = !wrap_not,
                        None => {
                            cs.push(c.clone());
                        }
                    }
                }
                if cs.len() == 0 {
                    cbool(false)
                } else {
                    let new_t = term(t.op.clone(), cs);
                    if wrap_not {
                        Some(term![Op::Not; new_t])
                    } else {
                        Some(new_t)
                    }
                }
            }
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;
    //    use rug::Integer;

    //    fn bv(u: usize, w: usize) -> Term {
    //        leaf_term(Op::Const(Value::BitVector(BitVector::new(
    //            Integer::from(u),
    //            w,
    //        ))))
    //    }
    //
    //    fn bool(b: bool) -> Term {
    //        leaf_term(Op::Const(Value::Bool(b)))
    //    }
    //
    //    const B_AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
    //    const B_OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
    //    const B_XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);
    //    const BV_AND: Op = Op::BvNaryOp(BvNaryOp::And);
    //    const BV_OR: Op = Op::BvNaryOp(BvNaryOp::Or);
    //    const BV_XOR: Op = Op::BvNaryOp(BvNaryOp::Xor);
    //    const BV_ADD: Op = Op::BvNaryOp(BvNaryOp::Add);
    //    const BV_MUL: Op = Op::BvNaryOp(BvNaryOp::Mul);

    #[quickcheck]
    fn semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = fold(&t);
        eval(&t, &vs) == eval(&tt, &vs)
    }
}
