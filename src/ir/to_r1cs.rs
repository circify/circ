use super::term::*;
use crate::target::r1cs::*;

use rug::ops::Pow;
use rug::Integer;

use std::collections::HashMap;
use std::fmt::Display;
use std::iter::ExactSizeIterator;

struct ToR1cs {
    r1cs: R1cs<String>,
    bools: TermMap<Lc>,
    values: Option<HashMap<String, Value>>,
    next_idx: usize,
}

impl ToR1cs {
    fn new(modulus: Integer, values: Option<HashMap<String, Value>>) -> Self {
        Self {
            r1cs: R1cs::new(modulus, values.is_some()),
            bools: TermMap::new(),
            values,
            next_idx: 0,
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_var<D: Display>(&mut self, ctx: &D, value: Option<Integer>) -> Lc {
        let n = format!("{}_v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.r1cs.add_signal(n.clone(), value);
        self.r1cs.signal_lc(&n)
    }

    /// Enforce `x` to be bit-valued
    fn enforce_bit(&mut self, b: Lc) {
        self.r1cs.constraint(b.clone(), b - 1, self.r1cs.zero());
    }

    /// Get a new bit-valued variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bit<D: Display>(&mut self, ctx: &D, value: Option<Integer>) -> Lc {
        let v = self.fresh_var(ctx, value);
        self.enforce_bit(v.clone());
        v
    }

    /// Enforce `x` to be non-zero.
    fn enforce_nonzero(&mut self, x: Lc) {
        let i = self.fresh_var(
            &"inv",
            self.r1cs
                .eval(&x)
                .map(|x| x.invert(&self.r1cs.modulus()).expect("Is zero")),
        );
        self.r1cs.constraint(x.clone(), i, self.r1cs.zero() + 1);
    }

    /// Return a bit indicating whether wire `x` is zero.
    fn is_zero(&mut self, x: Lc) -> Lc {
        let is_zero = self.fresh_bit(
            &"is_zero",
            self.r1cs.eval(&x).map(|x| Integer::from(x == 0)),
        );
        self.enforce_nonzero(x.clone() + &is_zero);
        self.r1cs.constraint(x, is_zero.clone(), self.r1cs.zero());
        is_zero
    }

    /// Return a bit indicating whether wires `x` and `y` are equal.
    fn are_equal(&mut self, x: Lc, y: &Lc) -> Lc {
        self.is_zero(x - y)
    }

    /// Return a bit indicating whether wires `x` and `y` are equal.
    fn bits_are_equal(&mut self, x: Lc, y: &Lc) -> Lc {
        let eq = self.fresh_bit(
            &"is_zero",
            self.r1cs
                .eval(&x)
                .and_then(|x| self.r1cs.eval(y).map(|y| Integer::from(x == y))),
        );
        let ones = self.bool_not(&eq);
        let twos = x + y - &ones;
        self.r1cs
            .constraint(twos.clone(), twos - 2, self.r1cs.zero());
        eq
    }

    /// Evaluate `var`'s value as an (integer-casted) boolean.
    /// Returns `None` if values are not stored.
    fn eval_bool(&self, var: &str) -> Option<Integer> {
        self.values
            .as_ref()
            .map(|vs| match vs.get(var).expect("missing value") {
                Value::Bool(b) => Integer::from(*b),
                v => panic!("{} should be a bool, but is {:?}", var, v),
            })
    }

    /// Given wire `x`, returns a vector of `n` wires which are the bits of `x`.
    /// Constrains `x` to fit in `n` (unsigned) bits.
    /// The LSB is at index 0.
    fn bitify<D: Display>(&mut self, d: &D, x: &Lc, n: usize) -> Vec<Lc> {
        let x_val = self.r1cs.eval(x);
        let bits = (0..n)
            .map(|i| {
                self.fresh_bit(
                    &format!("{}_b{}", d, i),
                    x_val.as_ref().map(|x| Integer::from(x.get_bit(i as u32))),
                )
            })
            .collect::<Vec<_>>();
        let sum = bits.iter().enumerate().fold(self.r1cs.zero(), |s, (i, b)| {
            s + &(b.clone() * &Integer::from(2).pow(i as u32))
        });
        self.r1cs
            .constraint(self.r1cs.zero(), self.r1cs.zero(), sum - x);
        bits
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the XOR of all of them.
    fn nary_xor<I: IntoIterator<Item = Lc>>(&mut self, xs: I) -> Lc {
        let (sum, n) = xs
            .into_iter()
            .fold((self.r1cs.zero(), 0), |(s, n), i| (s + &i, n + 1));
        let sum_bits = self.bitify(&"sum", &sum, bitsize(n));
        assert!(n > 0);
        assert!(self.r1cs.modulus() > &n);
        sum_bits.into_iter().next().unwrap() // safe b/c assert
    }

    /// Return the product of `a` and `b`.
    fn mul(&mut self, a: Lc, b: Lc) -> Lc {
        let c = self.fresh_var(
            &"mul",
            self.r1cs
                .eval(&a)
                .and_then(|a| self.r1cs.eval(&b).map(|b| a * b)),
        );
        self.r1cs.constraint(a, b, c.clone());
        c
    }

    /// Given a bit-values `a`, returns its (boolean) not.
    fn bool_not(&mut self, a: &Lc) -> Lc {
        self.r1cs.zero() + 1 - a
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the AND of all of them.
    fn nary_and<I: ExactSizeIterator<Item = Lc>>(&mut self, mut xs: I) -> Lc {
        let n = xs.len();
        if n <= 3 {
            let first = xs.next().expect("empty AND").clone();
            xs.fold(first, |a, x| self.mul(a, x))
        } else {
            let negs: Vec<Lc> = xs.map(|x| self.bool_not(&x)).collect();
            let a = self.nary_or(negs.into_iter());
            self.bool_not(&a)
        }
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the OR of all of them.
    fn nary_or<I: ExactSizeIterator<Item = Lc>>(&mut self, mut xs: I) -> Lc {
        let n = xs.len();
        if n <= 3 {
            let negs: Vec<Lc> = xs.map(|x| self.bool_not(&x)).collect();
            let a = self.nary_and(negs.into_iter());
            self.bool_not(&a)
        } else {
            let sum = xs.fold(self.r1cs.zero(), |s, x| s + &x);
            let z = self.is_zero(sum);
            self.bool_not(&z)
        }
    }

    /// Given a bit-valued `c`, and branches `t` and `f`, returns a wire which is `t` iff `c`, else
    /// `f`.
    fn ite(&mut self, c: Lc, t: Lc, f: &Lc) -> Lc {
        self.mul(c, t - f) + f
    }

    fn embed(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
            match check(c.clone()).expect("type-check error in embed") {
                Sort::Bool => {
                    self.embed_bool(c);
                }
                s => panic!("Unsupported sort in embed: {:?}", s),
            }
        }
    }

    fn embed_eq(&mut self, a: &Term, b: &Term) -> Lc {
        match check(a.clone()).expect("type error in embed_eq") {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let b = self.get_bool(b).clone();
                self.are_equal(a, &b)
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn embed_bool(&mut self, c: Term) -> &Lc {
        debug_assert!(check(c.clone()) == Ok(Sort::Bool));
        // TODO: skip if already embedded
        if !self.bools.contains_key(&c) {
            let lc = match &c.op {
                Op::Var(name, Sort::Bool) => {
                    let v = self.fresh_var(name, self.eval_bool(name));
                    self.enforce_bit(v.clone());
                    v
                }
                Op::Const(Value::Bool(b)) => self.r1cs.zero() + *b as isize,
                Op::Eq => self.embed_eq(&c.children[0], &c.children[1]),
                Op::Ite => {
                    let a = self.get_bool(&c.children[0]).clone();
                    let b = self.get_bool(&c.children[1]).clone();
                    let c = self.get_bool(&c.children[2]).clone();
                    self.ite(a, b, &c)
                }
                Op::BoolUnOp(BoolUnOp::Not) => {
                    let a = self.get_bool(&c.children[0]).clone();
                    self.bool_not(&a)
                }
                Op::BoolBinOp(BoolBinOp::Implies) => {
                    let a = self.get_bool(&c.children[0]).clone();
                    let b = self.get_bool(&c.children[1]).clone();
                    let not_a = self.bool_not(&a);
                    self.nary_or(vec![not_a, b].into_iter())
                }
                Op::BoolNaryOp(o) => {
                    let args = c
                        .children
                        .iter()
                        .map(|c| self.get_bool(c).clone())
                        .collect::<Vec<_>>();
                    match o {
                        BoolNaryOp::Or => self.nary_or(args.into_iter()),
                        BoolNaryOp::And => self.nary_and(args.into_iter()),
                        BoolNaryOp::Xor => self.nary_xor(args.into_iter()),
                    }
                }
                _ => panic!("Non-boolean in embed_bool: {:?}", c),
            };
            self.bools.insert(c.clone(), lc);
        }
        self.bools.get(&c).unwrap()
    }

    fn get_bool(&self, t: &Term) -> &Lc {
        self.bools
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
    }
}

// Returns the number of bits needed to hold n.
fn bitsize(mut n: usize) -> usize {
    let mut acc = 0;
    while n > 0 {
        n >>= 1;
        acc += 1;
    }
    acc
}
