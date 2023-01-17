//! Binarize terms

use crate::ir::term::*;

/// Binarize cache.
#[derive(Default)]
pub struct Cache(TermMap<Term>);

impl Cache {
    /// Empty cache.
    pub fn new() -> Self {
        Cache(TermMap::default())
    }
}

fn binarize(op: &Op, children: &[Term]) -> Term {
    if children.is_empty() || children.len() == 1 {
        term(op.clone(), children.to_vec())
    } else {
        children[2..].to_vec().iter().fold(
            term![op.clone(); children[1].clone(), children[0].clone()],
            |acc, x| term![op.clone(); x.clone(), acc],
        )
    }
}

/// Traverse `term`, binarize n-ary operators.
pub fn binarize_nary_ops(term_: Term) -> Term {
    let mut c = Cache::new();
    binarize_nary_ops_cached(term_, &mut c)
}
/// Traverse `term`, binarize n-ary operators.
pub fn binarize_nary_ops_cached(term_: Term, Cache(ref mut rewritten): &mut Cache) -> Term {
    for t in PostOrderIter::new(term_.clone()) {
        let mut children = Vec::new();
        for c in t.cs() {
            if let Some(rewritten_c) = rewritten.get(c) {
                children.push(rewritten_c.clone());
            } else {
                children.push(c.clone());
            }
        }
        let entry = match t.op() {
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => binarize(t.op(), &children),
            _ => term(t.op().clone(), children.clone()),
        };
        rewritten.insert(t, entry);
    }

    if let Some(t) = rewritten.get(&term_) {
        t.clone()
    } else {
        panic!("Couldn't find rewritten binarized term: {}", term_);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    fn bool(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    fn is_binary(t: Term) -> bool {
        PostOrderIter::new(t).all(|c| match c.op() {
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => c.cs().len() <= 2,
            _ => true,
        })
    }

    #[quickcheck]
    fn binarize_random(ArbitraryTerm(t): ArbitraryTerm) -> bool {
        is_binary(binarize_nary_ops(t))
    }

    #[quickcheck]
    fn binarize_semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let tt = binarize_nary_ops(t.clone());
        eval(&t, &vs) == eval(&tt, &vs)
    }

    #[test]
    fn simple_bool() {
        for o in vec![AND, OR, XOR] {
            let t = term![o.clone(); bool(true), term![o.clone(); bool(false), bool(true)]];
            let tt = term![o.clone(); bool(true), bool(false), bool(true)];
            assert_eq!(t, binarize_nary_ops(tt));
        }
    }

    #[test]
    fn simple_bv() {
        for o in vec![BV_AND, BV_OR, BV_XOR, BV_ADD, BV_MUL] {
            let t = term![o.clone(); bv_lit(3,5), term![o.clone(); bv_lit(3,5), bv_lit(3,5)]];
            let tt = term![o.clone(); bv_lit(3, 5), bv_lit(3, 5), bv_lit(3, 5)];
            assert_eq!(t, binarize_nary_ops(tt));
        }
    }
}
