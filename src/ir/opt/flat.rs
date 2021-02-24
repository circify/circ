use crate::ir::term::*;

/// Traverse `term`, flattening n-ary operators.
pub fn flatten_nary_ops(term_: Term) -> Term {
    // what does a term rewrite to?
    let mut rewritten = TermMap::<Term>::new();
    for t in PostOrderIter::new(term_.clone()) {
        let new_t = match &t.op {
            // Don't flatten field*, since it does not help us.
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(PfNaryOp::Add) => {
                let mut children = Vec::new();
                for c in &t.cs {
                    let new_c = rewritten.get(c).unwrap();
                    if &new_c.op == &t.op {
                        children.extend(new_c.cs.iter().cloned())
                    } else {
                        children.push(new_c.clone());
                    }
                }
                term(t.op.clone(), children)
            }
            _ => term(
                t.op.clone(),
                t.cs.iter()
                    .map(|c| rewritten.get(c).unwrap().clone())
                    .collect(),
            ),
        };
        rewritten.insert(t, new_t);
    }
    rewritten.get(&term_).unwrap().clone()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    fn bool(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    const B_AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
    const B_OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
    const B_XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);
    const BV_AND: Op = Op::BvNaryOp(BvNaryOp::And);
    const BV_OR: Op = Op::BvNaryOp(BvNaryOp::Or);
    const BV_XOR: Op = Op::BvNaryOp(BvNaryOp::Xor);
    const BV_ADD: Op = Op::BvNaryOp(BvNaryOp::Add);
    const BV_MUL: Op = Op::BvNaryOp(BvNaryOp::Mul);

    fn is_flat(t: Term) -> bool {
        PostOrderIter::new(t)
            .all(|c| c.op == Op::PfNaryOp(PfNaryOp::Mul) || c.op.arity().is_some() || !c.cs.iter().any(|cc| c.op == cc.op))
    }

    #[quickcheck]
    fn flatten_random(ArbitraryTerm(t): ArbitraryTerm) -> bool {
        is_flat(flatten_nary_ops(t))
    }

    #[quickcheck]
    fn flatten_semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = flatten_nary_ops(t.clone());
        eval(&t, &vs) == eval(&tt, &vs)
    }

    #[test]
    fn simple_bool() {
        for o in vec![B_AND, B_OR, B_XOR] {
            let t = term![o.clone(); term![o.clone(); bool(true), bool(false)], bool(true)];
            let tt = term![o.clone(); bool(true), bool(false), bool(true)];
            assert_eq!(flatten_nary_ops(t), tt);
        }
    }

    #[test]
    fn simple_bv() {
        for o in vec![BV_AND, BV_OR, BV_XOR, BV_ADD, BV_MUL] {
            let t = term![o.clone(); term![o.clone(); bv_lit(3,5), bv_lit(3,5)], bv_lit(3,5)];
            let tt = term![o.clone(); bv_lit(3, 5), bv_lit(3, 5), bv_lit(3, 5)];
            assert_eq!(flatten_nary_ops(t), tt);
        }
    }
}
