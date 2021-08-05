//! Translation from IR to MILP
//!
//!

use crate::ir::term::extras::Letified;
use crate::ir::term::*;
use crate::target::ilp::Ilp;
use crate::target::r1cs::trans::bitsize;

use good_lp::{variable, Expression};
use log::debug;

use std::fmt::Display;

#[derive(Clone)]
enum EmbeddedTerm {
    /// Constrained to be zero or one
    Bool(Expression),
}

struct ToMilp {
    ilp: Ilp,
    cache: TermMap<EmbeddedTerm>,
    next_idx: usize,
}

impl ToMilp {
    fn new() -> Self {
        Self {
            ilp: Ilp::new(),
            cache: TermMap::new(),
            next_idx: 0,
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bit<D: Display + ?Sized>(&mut self, ctx: &D) -> Expression {
        let n = format!("{}_v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.ilp.new_variable(variable().binary(), n).into()
    }

    /// Get a new variable, named `name`.
    fn bit(&mut self, name: String) -> Expression {
        self.ilp.new_variable(variable().binary(), name).into()
    }

    fn embed(&mut self, t: Term) {
        debug!("Embed: {}", Letified(t.clone()));
        for c in PostOrderIter::new(t) {
            debug!("Embed op: {}", c.op);
            match check(&c) {
                Sort::Bool => {
                    self.embed_bool(c);
                }
                s => panic!("Unsupported sort in embed: {:?}", s),
            }
        }
    }

    fn bit_not(&self, x: &Expression) -> Expression {
        Expression::from(1) - x
    }

    fn bit_and<'a>(&mut self, xs: impl IntoIterator<Item = &'a Expression>) -> Expression {
        let r = self.fresh_bit("and");
        let mut n = 0;
        // going to be x1 + ... + xn - r
        let mut sum = -r.clone();
        // each is r - x1 <= 0
        let mut bounds = Vec::new();
        for x in xs {
            n += 1;
            sum = sum + x;
            bounds.push(r.clone() - x << 0);
        }
        assert!(n >= 1);
        self.ilp.new_constraint(sum << (n as i32 - 1));
        self.ilp.new_constraints(bounds);
        r
    }

    fn bit_or<'a>(&mut self, xs: impl IntoIterator<Item = &'a Expression>) -> Expression {
        let nots: Vec<Expression> = xs.into_iter().map(|x| self.bit_not(x)).collect();
        let not_or = self.bit_and(&nots);
        self.bit_not(&not_or)
    }
    fn bit_xor<'a>(&mut self, xs: impl IntoIterator<Item = &'a Expression>) -> Expression {
        let (sum, ct) = xs
            .into_iter()
            .fold((Expression::from(0), 0), |(acc, n), x| (acc + x, n + 1));
        self.bit_decomp(&sum, bitsize(ct))
            .into_iter()
            .next()
            .unwrap()
    }

    /// Returns a bit decomposition of e, with the ones place in index 0.
    fn bit_decomp(&mut self, e: &Expression, n_bits: usize) -> Vec<Expression> {
        let bits: Vec<_> = (0..n_bits)
            .map(|i| self.fresh_bit(&format!("bit{}", i)))
            .collect();
        let sum = bits
            .iter()
            .enumerate()
            .fold(Expression::from(0), |acc, (i, b)| {
                acc + (2.0_f64).powi(i as i32) * b.clone()
            });
        self.ilp.new_constraint(sum.eq(e));
        bits
    }

    /// Return a bit indicating whether wires `x` and `y` are equal.
    fn bits_are_equal(&mut self, x: &Expression, y: &Expression) -> Expression {
        let sum_ones_place = self
            .bit_decomp(&(x.clone() + y), 2)
            .into_iter()
            .next()
            .unwrap();
        self.bit_not(&sum_ones_place)
    }

    fn embed_eq(&mut self, a: &Term, b: &Term) -> Expression {
        match check(a) {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let b = self.get_bool(b).clone();
                self.bits_are_equal(&a, &b)
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn embed_bool(&mut self, c: Term) -> &Expression {
        debug_assert!(check(&c) == Sort::Bool);
        if !self.cache.contains_key(&c) {
            let lc = match &c.op {
                Op::Var(name, Sort::Bool) => self.bit(name.to_string()),
                Op::Const(Value::Bool(b)) => Expression::from(*b as i32),
                Op::Eq => self.embed_eq(&c.cs[0], &c.cs[1]),
                Op::Ite => {
                    let a = self.get_bool(&c.cs[0]).clone();
                    let not_a = self.bit_not(&a);
                    let b = self.get_bool(&c.cs[1]).clone();
                    let c = self.get_bool(&c.cs[2]).clone();
                    let a_and_b = self.bit_and(&[a, b]);
                    let not_a_and_c = self.bit_and(&[not_a, c]);
                    self.bit_or(&[a_and_b, not_a_and_c])
                }
                Op::Not => {
                    let a = self.get_bool(&c.cs[0]);
                    self.bit_not(a)
                }
                Op::Implies => {
                    let a = self.get_bool(&c.cs[0]).clone();
                    let b = self.get_bool(&c.cs[1]).clone();
                    let not_a = self.bit_not(&a);
                    self.bit_or(&[not_a, b])
                }
                Op::BoolNaryOp(o) => {
                    let args =
                        c.cs.iter()
                            .map(|c| self.get_bool(c).clone())
                            .collect::<Vec<_>>();
                    match o {
                        BoolNaryOp::Or => self.bit_or(args.iter()),
                        BoolNaryOp::And => self.bit_and(args.iter()),
                        BoolNaryOp::Xor => self.bit_xor(args.iter()),
                    }
                }
                _ => panic!("Non-boolean in embed_bool: {}", c),
            };
            self.cache.insert(c.clone(), EmbeddedTerm::Bool(lc));
        }
        self.get_bool(&c)
    }

    fn get_bool(&self, t: &Term) -> &Expression {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bool(b) => &b,
        }
    }

    fn assert(&mut self, t: Term) {
        debug!("Assert: {}", Letified(t.clone()));
        self.embed(t.clone());
        let lc = self.get_bool(&t).clone();
        self.ilp.new_constraint(lc.eq(1));
    }
}

/// Convert this (IR) constraint system `cs` to an MILP.
/// The last output is the maximization objective.
/// All others are constraints.
pub fn to_ilp(cs: Computation) -> Ilp {
    let Computation { mut outputs, .. } = cs;
    let opt = outputs.pop().unwrap();
    let mut converter = ToMilp::new();
    for c in outputs {
        converter.assert(c);
    }
    converter.embed(opt.clone());
    match check(&opt) {
        Sort::Bool => {
            converter.ilp.maximize(converter.get_bool(&opt).clone());
        }
        s => panic!("Cannot optimize term of sort {}", s),
    };
    converter.ilp
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::Constraints;
    use crate::target::r1cs::trans::test::PureBool;
    use ahash::AHashSet;
    use good_lp::default_solver;
    use quickcheck_macros::quickcheck;

    #[test]
    fn bool() {
        let cs = Computation {
            outputs: vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
                // max this
                term![AND;
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            metadata: ComputationMetadata::default(),
            values: None,
        };
        let ilp = to_ilp(cs);
        let r = ilp.solve(default_solver).unwrap();
        println!("{:#?}", r);
        assert_eq!(r.get("a").unwrap(), &1.0);
        assert_eq!(r.get("b").unwrap(), &0.0);
    }

    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(
            vec![t, leaf_term(Op::Const(Value::Bool(true)))],
            AHashSet::new(),
            Some(values.clone()),
        );
        let mut ilp = to_ilp(cs);
        for (v, val) in &values {
            match val {
                Value::Bool(true) => {
                    if let Some(var) = ilp.var_names.get(v) {
                        let e = Expression::from(var.clone());
                        ilp.new_constraint(e.eq(1.0));
                    }
                }
                Value::Bool(false) => {
                    if let Some(var) = ilp.var_names.get(v) {
                        let e = Expression::from(var.clone());
                        ilp.new_constraint(e.eq(0.0));
                    }
                }
                _ => unreachable!(),
            }
        }
        let r = ilp.solve(default_solver);
        let solution = r.unwrap();
        for (v, val) in &values {
            match val {
                Value::Bool(true) => {
                    if let Some(sol) = solution.get(v) {
                        assert!((sol - 1.0).abs() < 0.01);
                    }
                }
                Value::Bool(false) => {
                    if let Some(sol) = solution.get(v) {
                        assert!((sol - 0.0).abs() < 0.01);
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
