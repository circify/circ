//! Binarize terms

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// Binarize cache.
#[derive(Default)]
struct Binarizer;

impl RewritePass for Binarizer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        let cs = rewritten_children();
        match &orig.op {
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => {
                if cs.is_empty() || cs.len() == 1 {
                    Some(term(orig.op.clone().clone(), cs.to_vec()))
                } else {
                    Some(cs[2..].to_vec().iter().fold(
                        term![orig.op.clone(); cs[1].clone(), cs[0].clone()],
                        |acc, x| term![orig.op.clone(); x.clone(), acc],
                    ))
                }
            }
            _ => None,
        }
    }
}

/// Binarize (expand) n-ary terms.
pub fn binarize(c: &mut Computation) {
    let mut pass = Binarizer;
    pass.traverse(c);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

    fn bool(b: bool) -> Term {
        leaf_term(Op::Const(Value::Bool(b)))
    }

    fn is_binary(t: &Term) -> bool {
        PostOrderIter::new(t.clone()).all(|c| match c.op {
            Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => c.cs.len() <= 2,
            _ => true,
        })
    }

    #[quickcheck]
    fn binarize_random(ArbitraryTerm(t): ArbitraryTerm) -> bool {
        let mut c = Computation::default();
        c.outputs.push(t);
        binarize(&mut c);
        is_binary(&c.outputs[0])
    }

    #[quickcheck]
    fn binarize_semantics_random(ArbitraryTermEnv(t, vs): ArbitraryTermEnv) -> bool {
        let mut c = Computation::default();
        c.outputs.push(t.clone());
        binarize(&mut c);
        eval(&t, &vs) == eval(&c.outputs[0], &vs)
    }

    #[test]
    fn simple_bool() {
        for o in vec![AND, OR, XOR] {
            let t = term![o.clone(); bool(true), term![o.clone(); bool(false), bool(true)]];
            let tt = term![o.clone(); bool(true), bool(false), bool(true)];
            let mut c = Computation::default();
            c.outputs.push(tt);
            binarize(&mut c);
            assert_eq!(t, c.outputs[0]);
        }
    }

    #[test]
    fn simple_bv() {
        for o in vec![BV_AND, BV_OR, BV_XOR, BV_ADD, BV_MUL] {
            let t = term![o.clone(); bv_lit(3,5), term![o.clone(); bv_lit(3,5), bv_lit(3,5)]];
            let tt = term![o.clone(); bv_lit(3, 5), bv_lit(3, 5), bv_lit(3, 5)];
            let mut c = Computation::default();
            c.outputs.push(tt);
            binarize(&mut c);
            assert_eq!(t, c.outputs[0]);
        }
    }
}
