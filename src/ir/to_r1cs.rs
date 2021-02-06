use super::term::*;
use crate::target::r1cs::*;

use rug::ops::Pow;
use rug::Integer;

use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::iter::ExactSizeIterator;

struct BvEntry {
    width: usize,
    uint: Lc,
    bits: Vec<Lc>,
}

struct ToR1cs {
    r1cs: R1cs<String>,
    bools: TermMap<Lc>,
    bvs: TermMap<BvEntry>,
    values: Option<HashMap<String, Value>>,
    public_inputs: HashSet<String>,
    next_idx: usize,
}

impl ToR1cs {
    fn new(
        modulus: Integer,
        values: Option<HashMap<String, Value>>,
        public_inputs: HashSet<String>,
    ) -> Self {
        Self {
            r1cs: R1cs::new(modulus, values.is_some()),
            bools: TermMap::new(),
            bvs: TermMap::new(),
            values,
            public_inputs,
            next_idx: 0,
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_var<D: Display + ?Sized>(&mut self, ctx: &D, value: Option<Integer>) -> Lc {
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
    fn fresh_bit<D: Display + ?Sized>(&mut self, ctx: &D, value: Option<Integer>) -> Lc {
        let v = self.fresh_var(ctx, value);
        self.enforce_bit(v.clone());
        v
    }

    /// Enforce `x` to be non-zero.
    fn enforce_nonzero(&mut self, x: Lc) {
        let i = self.fresh_var(
            "inv",
            self.r1cs
                .eval(&x)
                .map(|x| x.invert(&self.r1cs.modulus()).expect("Is zero")),
        );
        self.r1cs.constraint(x.clone(), i, self.r1cs.zero() + 1);
    }

    /// Return a bit indicating whether wire `x` is zero.
    fn is_zero(&mut self, x: Lc) -> Lc {
        let is_zero = self.fresh_bit("is_zero", self.r1cs.eval(&x).map(|x| Integer::from(x == 0)));
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
            "is_zero",
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

    /// Evaluate `var`'s value as an (integer-casted) bit-vector.
    /// Returns `None` if values are not stored.
    fn eval_bv(&self, var: &str) -> Option<Integer> {
        self.values
            .as_ref()
            .map(|vs| match vs.get(var).expect("missing value") {
                Value::BitVector(BitVector { uint, .. }) => uint.clone(),
                v => panic!("{} should be a bool, but is {:?}", var, v),
            })
    }

    /// Given wire `x`, returns a vector of `n` wires which are the bits of `x`.
    /// Constrains `x` to fit in `n` (unsigned) bits.
    /// The LSB is at index 0.
    fn bitify<D: Display + ?Sized>(&mut self, d: &D, x: &Lc, n: usize) -> Vec<Lc> {
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

    /// Given a sequence of `bits`, returns a wire which represents their sum,
    /// `\sum_{i>0} b_i2^i`.
    ///
    /// If `signed` is set, then the MSB is negated; i.e., the two's-complement sum is returned.
    fn debitify<I: ExactSizeIterator<Item = Lc>>(&self, bits: I, signed: bool) -> Lc {
        let n = bits.len();
        bits.enumerate().fold(self.r1cs.zero(), |sum, (i, bit)| {
            let summand = bit * &Integer::from(2).pow(i as u32);
            if signed && i + 1 == n {
                sum - &summand
            } else {
                sum + &summand
            }
        })
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the XOR of all of them.
    fn nary_xor<I: ExactSizeIterator<Item = Lc>>(&mut self, xs: I) -> Lc {
        let n = xs.len();
        let sum = xs.into_iter().fold(self.r1cs.zero(), |s, i| s + &i);
        let sum_bits = self.bitify("sum", &sum, bitsize(n));
        assert!(n > 0);
        assert!(self.r1cs.modulus() > &n);
        sum_bits.into_iter().next().unwrap() // safe b/c assert
    }

    /// Return the product of `a` and `b`.
    fn mul(&mut self, a: Lc, b: Lc) -> Lc {
        let c = self.fresh_var(
            "mul",
            self.r1cs
                .eval(&a)
                .and_then(|a| self.r1cs.eval(&b).map(|b| a * b)),
        );
        self.r1cs.constraint(a, b, c.clone());
        c
    }

    /// Given a bit-values `a`, returns its (boolean) not.
    fn bool_not(&self, a: &Lc) -> Lc {
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
    fn nary_or<I: ExactSizeIterator<Item = Lc>>(&mut self, xs: I) -> Lc {
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
                Sort::BitVector(_) => {
                    self.embed_bv(c);
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
                self.bits_are_equal(a, &b)
            }
            Sort::BitVector(_) => {
                let a = self.get_bv_uint(a).clone();
                let b = self.get_bv_uint(b).clone();
                self.are_equal(a, &b)
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn embed_bool(&mut self, c: Term) -> &Lc {
        //println!("Embed: {}", c);
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
                Op::Not => {
                    let a = self.get_bool(&c.children[0]);
                    self.bool_not(a)
                }
                Op::Implies => {
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
//        self.r1cs.eval(self.bools.get(&c).unwrap()).map(|v| {
//            println!("-> {}", v);
//        });
        self.bools.get(&c).unwrap()
    }

    fn embed_bv(&mut self, bv: Term) {
        if let Sort::BitVector(n) = check(bv.clone()).unwrap() {
            if !self.bvs.contains_key(&bv) {
                match &bv.op {
                    Op::Var(name, Sort::BitVector(_)) => {
                        let val = self.eval_bv(name);
                        let var = self.fresh_var(name, val);
                        self.set_bv_uint(bv.clone(), var, n);
                        if !self.public_inputs.contains(name) {
                            self.get_bv_bits(&bv);
                        }
                    }
                    Op::Const(Value::BitVector(BitVector { uint, width })) => {
                        let bit_lcs = (0..*width)
                            .map(|i| self.r1cs.zero() + uint.get_bit(i as u32) as isize)
                            .collect();
                        self.set_bv_bits(bv, bit_lcs);
                    }
                    Op::Ite => {
                        let c = self.get_bool(&bv.children[0]).clone();
                        let t = self.get_bv_uint(&bv.children[1]).clone();
                        let f = self.get_bv_uint(&bv.children[2]).clone();
                        let ite = self.ite(c, t, &f);
                        self.set_bv_uint(bv, ite, n);
                    }
                    Op::BvUnOp(BvUnOp::Not) => {
                        let bits = self.get_bv_bits(&bv.children[0]).clone();
                        let not_bits = bits.iter().map(|bit| self.bool_not(bit)).collect();
                        self.set_bv_bits(bv, not_bits);
                    }
                    Op::BvUnOp(BvUnOp::Neg) => {
                        let x = self.r1cs.zero() + &Integer::from(2).pow(n as u32)
                            - self.get_bv_uint(&bv.children[0]);
                        self.set_bv_uint(bv, x, n);
                    }
                    Op::BvUext(extra_n) => {
                        // TODO: carry over bits if possible.
                        let x = self.get_bv_uint(&bv.children[0]).clone();
                        let new_n = n + extra_n;
                        self.set_bv_uint(bv, x, new_n);
                    }
                    Op::BvSext(extra_n) => {
                        let mut bits = self.get_bv_bits(&bv.children[0]).clone().into_iter();
                        let ext_bits =
                            std::iter::repeat(bits.next().expect("sign ext empty").clone())
                                .take(extra_n + 1);

                        self.set_bv_bits(bv, ext_bits.chain(bits).collect());
                    }
                    Op::BvNaryOp(o) => match o {
                        BvNaryOp::Xor | BvNaryOp::Or | BvNaryOp::And => {
                            let mut bits_by_bv = bv
                                .children
                                .iter()
                                .map(|c| self.get_bv_bits(c).clone())
                                .collect::<Vec<_>>();
                            let mut bits_bv_idx: Vec<Vec<Lc>> = Vec::new();
                            while bits_by_bv[0].len() > 0 {
                                bits_bv_idx.push(
                                    bits_by_bv.iter_mut().map(|bv| bv.pop().unwrap()).collect(),
                                );
                            }
                            let f = |v: Vec<Lc>| match o {
                                BvNaryOp::And => self.nary_and(v.into_iter()),
                                BvNaryOp::Or => self.nary_or(v.into_iter()),
                                BvNaryOp::Xor => self.nary_xor(v.into_iter()),
                                _ => unreachable!(),
                            };
                            let res = bits_bv_idx.into_iter().map(f).collect();
                            self.set_bv_bits(bv, res);
                        }
                        BvNaryOp::Add | BvNaryOp::Mul => {
                            let f_width = self.r1cs.modulus().significant_bits() as usize - 1;
                            let values = bv
                                .children
                                .iter()
                                .map(|c| self.get_bv_uint(c).clone())
                                .collect::<Vec<_>>();
                            let (res, width) = match o {
                                BvNaryOp::Add => {
                                    let sum =
                                        values.into_iter().fold(self.r1cs.zero(), |s, v| s + &v);
                                    let extra_width = bitsize(bv.children.len()) - 1;
                                    (sum, n + extra_width)
                                }
                                BvNaryOp::Mul => {
                                    if bv.children.len() * n < f_width {
                                        let z = self.r1cs.zero() + 1;
                                        (
                                            values.into_iter().fold(z, |acc, v| self.mul(acc, v)),
                                            bv.children.len() * n,
                                        )
                                    } else {
                                        let z = self.r1cs.zero() + 1;
                                        let p = values.into_iter().fold(z, |acc, v| {
                                            let p = self.mul(acc, v);
                                            let mut bits = self.bitify("binMul", &p, 2 * n);
                                            bits.truncate(n);
                                            self.debitify(bits.into_iter(), false)
                                        });
                                        (p, n)
                                    }
                                }
                                _ => unreachable!(),
                            };
                            let mut bits = self.bitify("arith", &res, width);
                            bits.truncate(n);
                            self.set_bv_bits(bv, bits);
                        }
                    },
                    Op::BvBinOp(o) => unimplemented!(),
                    _ => panic!("Non-boolean in embed_bool: {:?}", bv),
                }
            }
        } else {
            panic!("{:?} is not a bit-vector in embed_bv", bv);
        }
    }

    fn get_bool(&self, t: &Term) -> &Lc {
        self.bools
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
    }

    fn set_bv_bits(&mut self, t: Term, bits: Vec<Lc>) {
        let sum = self.debitify(bits.iter().cloned(), false);
        assert!(!self.bvs.contains_key(&t));
        self.bvs.insert(
            t,
            BvEntry {
                uint: sum,
                width: bits.len(),
                bits,
            },
        );
    }

    fn set_bv_uint(&mut self, t: Term, uint: Lc, width: usize) {
        assert!(!self.bvs.contains_key(&t));
        self.bvs.insert(
            t,
            BvEntry {
                uint,
                width,
                bits: Vec::new(),
            },
        );
    }

    fn get_bv_uint(&self, t: &Term) -> &Lc {
        &self.bvs.get(t).expect("Missing term").uint
    }

    fn get_bv_bits(&mut self, t: &Term) -> &Vec<Lc> {
        let mut bvs = std::mem::take(&mut self.bvs);
        let entry = bvs.get_mut(t).expect("Missing bit-vec");
        if entry.bits.len() == 0 {
            entry.bits = self.bitify("getbits", &entry.uint, entry.width);
        }
        self.bvs = bvs;
        &self.bvs.get(t).unwrap().bits
    }

    fn assert(&mut self, t: Term) {
        self.embed(t.clone());
        let lc = self.get_bool(&t).clone();
        self.r1cs
            .constraint(self.r1cs.zero(), self.r1cs.zero(), lc - 1);
    }
}

pub fn to_r1cs(cs: Constraints, modulus: Integer) -> R1cs<String> {
    let mut converter = ToR1cs::new(modulus, cs.values, cs.public_inputs);
    for c in cs.assertions {
        converter.assert(c);
    }
    converter.r1cs
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

#[cfg(test)]
mod test {
    use super::*;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    #[test]
    fn bool() {
        let cs = Constraints {
            public_inputs: vec!["a", "b"].into_iter().map(|a| a.to_owned()).collect(),
            values: Some(
                vec![
                    ("a".to_owned(), Value::Bool(true)),
                    ("b".to_owned(), Value::Bool(false)),
                ]
                .into_iter()
                .collect(),
            ),
            assertions: vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
        };
        let r1cs = to_r1cs(cs, Integer::from(17));
        r1cs.check_all();
    }

    #[derive(Clone, Debug)]
    struct PureBool(Term, HashMap<String, Value>);

    impl Arbitrary for PureBool {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let t = BoolDist(g.size()).sample(&mut rng);
            let values: HashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| {
                    if let Op::Var(n, _) = &c.op {
                        Some((n.clone(), Value::Bool(bool::arbitrary(g))))
                    } else {
                        None
                    }
                })
                .collect();
            PureBool(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let vs = self.1.clone();
            let ts = PostOrderIter::new(self.0.clone()).collect::<Vec<_>>();

            Box::new(
                ts.into_iter()
                    .rev()
                    .skip(1)
                    .map(move |t| PureBool(t, vs.clone())),
            )
        }
    }

    #[quickcheck]
    fn random_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Constraints {
            public_inputs: HashSet::new(),
            values: Some(values),
            assertions: vec![t],
        };
        let r1cs = to_r1cs(cs, Integer::from(1014088787));
        r1cs.check_all();
    }
}
