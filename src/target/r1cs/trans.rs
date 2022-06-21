//! Lowering IR to R1CS
//!
//! [Ben Braun's
//! thesis](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.683.6940&rep=rep1&type=pdf)
//! is a good intro to how this process works.
use crate::ir::term::extras::Letified;
use crate::ir::term::precomp::PreComp;
use crate::ir::term::*;
use crate::target::bitsize;
use crate::target::r1cs::*;

use circ_fields::FieldT;
use fxhash::FxHashSet;
use log::debug;
use rug::ops::Pow;
use rug::Integer;

use std::cell::RefCell;
use std::fmt::Display;
use std::iter::ExactSizeIterator;
use std::rc::Rc;

struct BvEntry {
    width: usize,
    uint: TermLc,
    bits: Vec<TermLc>,
}

#[derive(Clone)]
enum EmbeddedTerm {
    Bv(Rc<RefCell<BvEntry>>),
    Bool(TermLc),
    Field(TermLc),
    #[allow(dead_code)]
    Tuple(Vec<EmbeddedTerm>),
}

struct ToR1cs {
    r1cs: R1cs<String>,
    cache: TermMap<EmbeddedTerm>,
    wit_ext: PreComp,
    public_inputs: FxHashSet<String>,
    next_idx: usize,
    zero: TermLc,
    one: TermLc,
    field: FieldT,
}

impl ToR1cs {
    fn new(field: FieldT, public_inputs: FxHashSet<String>) -> Self {
        debug!("Starting R1CS back-end, field: {}", field);
        let r1cs = R1cs::new(field.clone());
        let zero = TermLc(pf_lit(field.new_v(0u8)), r1cs.zero());
        let one = zero.clone() + 1;
        Self {
            r1cs,
            cache: TermMap::new(),
            wit_ext: precomp::PreComp::new(),
            public_inputs,
            next_idx: 0,
            zero,
            one,
            field,
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    ///
    /// `comp` is a term that computes the value.
    fn fresh_var<D: Display + ?Sized>(&mut self, ctx: &D, comp: Term, public: bool) -> TermLc {
        let n = format!("{}_n{}", ctx, self.next_idx);
        self.next_idx += 1;
        debug_assert!(matches!(check(&comp), Sort::Field(_)));
        self.r1cs.add_signal(n.clone(), comp.clone());
        self.wit_ext.add_output(n.clone(), comp.clone());
        if public {
            self.r1cs.publicize(&n);
        }
        debug!("fresh: {}", n);
        TermLc(comp, self.r1cs.signal_lc(&n))
    }

    /// Enforce `x` to be bit-valued
    fn enforce_bit(&mut self, b: TermLc) {
        self.r1cs
            .constraint(b.1.clone(), (b - 1).1, self.r1cs.zero());
    }

    /// Get a new bit-valued variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bit<D: Display + ?Sized>(&mut self, ctx: &D, comp: Term) -> TermLc {
        debug_assert!(matches!(check(&comp), Sort::Bool));
        let comp = term![Op::Ite; comp, self.one.0.clone(), self.zero.0.clone()];
        let v = self.fresh_var(ctx, comp, false);
        //debug!("Fresh bit: {}", self.r1cs.format_lc(&v));
        self.enforce_bit(v.clone());
        v
    }

    /// Return a bit indicating whether wire `x` is non-zero.
    #[allow(clippy::wrong_self_convention)]
    fn is_zero(&mut self, x: TermLc) -> TermLc {
        let eqz = term![Op::Eq; x.0.clone(), self.zero.0.clone()];
        // m * x - 1 + is_zero == 0
        // is_zero * x == 0
        let m = self.fresh_var(
            "is_zero_inv",
            term![Op::Ite; eqz.clone(), self.zero.0.clone(), term![PF_RECIP; x.0.clone()]],
            false,
        );
        let is_zero = self.fresh_var(
            "is_zero",
            term![Op::Ite; eqz, self.one.0.clone(), self.zero.0.clone()],
            false,
        );
        self.r1cs
            .constraint(m.1, x.1.clone(), -is_zero.1.clone() + 1);
        self.r1cs
            .constraint(is_zero.1.clone(), x.1, self.r1cs.zero());
        is_zero
    }

    /// Return a bit indicating whether wires `x` and `y` are equal.
    fn are_equal(&mut self, x: TermLc, y: &TermLc) -> TermLc {
        self.is_zero(x - y)
    }

    /// Return a bit indicating whether wires `x` and `y` are equal.
    fn bits_are_equal(&mut self, x: &TermLc, y: &TermLc) -> TermLc {
        self.mul(x.clone() * 2, y.clone()) - x - y + 1
    }

    /// Given wire `x`, returns a vector of `n` wires which are the bits of `x`.
    /// They *have not* been constrained to sum to `x`.
    /// They have values according the the (infinite) two's complement representation of `x`.
    /// The LSB is at index 0.
    fn decomp<D: Display + ?Sized>(&mut self, d: &D, x: &TermLc, n: usize) -> Vec<TermLc> {
        (0..n)
            .map(|i| {
                self.fresh_bit(
                    // We get the right repr here because of infinite two's complement.
                    &format!("{}_b{}", d, i),
                    term![Op::BvBit(i); term![Op::PfToBv(n); x.0.clone()]],
                )
            })
            .collect::<Vec<_>>()
    }

    /// Given wire `x`, returns a vector of `n` wires which are the bits of `x`.
    /// Constrains `x` to fit in `n` (`signed`) bits.
    /// The LSB is at index 0.
    fn bitify<D: Display + ?Sized>(
        &mut self,
        d: &D,
        x: &TermLc,
        n: usize,
        signed: bool,
    ) -> Vec<TermLc> {
        debug!("Bitify({}): {}", n, self.r1cs.format_lc(&x.1));
        let bits = self.decomp(d, x, n);
        let sum = self.debitify(bits.iter().cloned(), signed);
        self.assert_zero(sum - x);
        bits
    }

    /// Given wire `x`, returns whether `x` fits in `n` `signed` bits.
    fn fits_in_bits<D: Display + ?Sized>(
        &mut self,
        d: &D,
        x: &TermLc,
        n: usize,
        signed: bool,
    ) -> TermLc {
        let bits = self.decomp(d, x, n);
        let sum = self.debitify(bits.iter().cloned(), signed);
        self.are_equal(sum, x)
    }

    /// Given a sequence of `bits`, returns a wire which represents their sum,
    /// `\sum_{i>0} b_i2^i`.
    ///
    /// If `signed` is set, then the MSB is negated; i.e., the two's-complement sum is returned.
    fn debitify<I: ExactSizeIterator<Item = TermLc>>(&self, bits: I, signed: bool) -> TermLc {
        let n = bits.len();
        let two = self.r1cs.modulus.new_v(2u8);
        let mut acc = self.r1cs.modulus.new_v(1u8);
        bits.enumerate().fold(self.zero.clone(), |sum, (i, bit)| {
            let summand = bit * &acc;
            acc *= &two;

            if signed && i + 1 == n {
                sum - &summand
            } else {
                sum + &summand
            }
        })
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the XOR of all of them.
    fn nary_xor<I: ExactSizeIterator<Item = TermLc>>(&mut self, mut xs: I) -> TermLc {
        let n = xs.len();
        if n > 3 {
            let sum = xs.into_iter().fold(self.zero.clone(), |s, i| s + &i);
            let sum_bits = self.bitify("sum", &sum, bitsize(n), false);
            assert!(n > 0);
            assert!(self.r1cs.modulus() > &n);
            sum_bits.into_iter().next().unwrap() // safe b/c assert
        } else {
            let first = xs.next().expect("empty XOR");
            xs.fold(first, |a, b| a.clone() + &b - &(self.mul(a, b) * 2))
        }
    }

    /// Return the product of `a` and `b`.
    fn mul(&mut self, a: TermLc, b: TermLc) -> TermLc {
        let mul_val = term![PF_MUL; a.0, b.0];
        let c = self.fresh_var("mul", mul_val, false);
        self.r1cs.constraint(a.1, b.1, c.1.clone());
        c
    }

    /// Given a bit-values `a`, returns its (boolean) not.
    fn bool_not(&self, a: &TermLc) -> TermLc {
        self.zero.clone() + 1 - a
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the AND of all of them.
    fn nary_and<I: ExactSizeIterator<Item = TermLc>>(&mut self, mut xs: I) -> TermLc {
        let n = xs.len();
        if n <= 3 {
            let first = xs.next().expect("empty AND");
            xs.fold(first, |a, x| self.mul(a, x))
        } else {
            // Needed to end the closures borrow of self, before the next line.
            #[allow(clippy::needless_collect)]
            let negs: Vec<TermLc> = xs.map(|x| self.bool_not(&x)).collect();
            let a = self.nary_or(negs.into_iter());
            self.bool_not(&a)
        }
    }

    /// Given `xs`, an iterator of bit-valued wires, returns the OR of all of them.
    fn nary_or<I: ExactSizeIterator<Item = TermLc>>(&mut self, xs: I) -> TermLc {
        let n = xs.len();
        if n <= 3 {
            // Needed to end the closures borrow of self, before the next line.
            #[allow(clippy::needless_collect)]
            let negs: Vec<TermLc> = xs.map(|x| self.bool_not(&x)).collect();
            let a = self.nary_and(negs.into_iter());
            self.bool_not(&a)
        } else {
            let sum = xs.fold(self.zero.clone(), |s, x| s + &x);
            let z = self.is_zero(sum);
            self.bool_not(&z)
        }
    }

    /// Given a bit-valued `c`, and branches `t` and `f`, returns a wire which is `t` iff `c`, else
    /// `f`.
    fn ite(&mut self, c: TermLc, t: TermLc, f: &TermLc) -> TermLc {
        self.mul(c, t - f) + f
    }

    fn embed(&mut self, t: Term) {
        debug!("Embed: {}", Letified(t.clone()));
        for c in PostOrderIter::new(t) {
            debug!("Embed op: {}", c.op);
            // Handle field access once and for all
            if let Op::Field(i) = &c.op {
                // Need to borrow self in between search and insert. Could refactor.
                #[allow(clippy::map_entry)]
                if !self.cache.contains_key(&c) {
                    let t = self.get_field(&c.cs[0], *i);
                    self.cache.insert(c, t);
                }
            } else {
                match check(&c) {
                    Sort::Bool => {
                        self.embed_bool(c);
                    }
                    Sort::BitVector(_) => {
                        self.embed_bv(c);
                    }
                    Sort::Field(_) => {
                        self.embed_pf(c);
                    }
                    Sort::Tuple(_) => {
                        // custom ops?
                        panic!("Cannot embed tuple term: {}", c)
                    }
                    s => panic!("Unsupported sort in embed: {:?}", s),
                }
            }
        }
    }

    fn get_field(&self, tuple_term: &Term, field: usize) -> EmbeddedTerm {
        match self.cache.get(tuple_term) {
            Some(EmbeddedTerm::Tuple(v)) => v[field].clone(),
            _ => panic!("No tuple for {}", tuple_term),
        }
    }

    fn embed_eq(&mut self, a: &Term, b: &Term) -> TermLc {
        match check(a) {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let b = self.get_bool(b).clone();
                self.bits_are_equal(&a, &b)
            }
            Sort::BitVector(_) => {
                let a = self.get_bv_uint(a);
                let b = self.get_bv_uint(b);
                self.are_equal(a, &b)
            }
            Sort::Field(_) => {
                let a = self.get_pf(a).clone();
                let b = self.get_pf(b).clone();
                self.are_equal(a, &b)
            }
            Sort::Tuple(sorts) => {
                let n = sorts.len();
                let eqs: Vec<Term> = (0..n).map(|i| {
                    term![Op::Eq; term![Op::Field(i); a.clone()], term![Op::Field(i); b.clone()]]
                }).collect();
                let conj = term(Op::BoolNaryOp(BoolNaryOp::And), eqs);
                self.embed(conj.clone());
                self.get_bool(&conj).clone()
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn assert_eq(&mut self, a: &Term, b: &Term) {
        match check(a) {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let diff = a - self.get_bool(b);
                self.assert_zero(diff);
            }
            Sort::BitVector(_) => {
                let a = self.get_bv_uint(a);
                let diff = a - &self.get_bv_uint(b);
                self.assert_zero(diff);
            }
            Sort::Field(_) => {
                let a = self.get_pf(a).clone();
                let diff = a - self.get_pf(b);
                self.assert_zero(diff);
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn embed_bool(&mut self, c: Term) -> &TermLc {
        //println!("Embed: {}", c);
        debug_assert!(check(&c) == Sort::Bool);
        // TODO: skip if already embedded
        if !self.cache.contains_key(&c) {
            let lc = match &c.op {
                Op::Var(name, Sort::Bool) => {
                    let public = self.public_inputs.contains(name);
                    let comp = term![Op::Ite; c.clone(), self.one.0.clone(), self.zero.0.clone()];
                    let v = self.fresh_var(name, comp, public);
                    if !public {
                        self.enforce_bit(v.clone());
                    }
                    v
                }
                Op::Const(Value::Bool(b)) => self.zero.clone() + *b as isize,
                Op::Eq => self.embed_eq(&c.cs[0], &c.cs[1]),
                Op::Ite => {
                    let a = self.get_bool(&c.cs[0]).clone();
                    let b = self.get_bool(&c.cs[1]).clone();
                    let c = self.get_bool(&c.cs[2]).clone();
                    self.ite(a, b, &c)
                }
                Op::BoolMaj => {
                    let a = self.get_bool(&c.cs[0]).clone();
                    let b = self.get_bool(&c.cs[1]).clone();
                    let c = self.get_bool(&c.cs[2]).clone();
                    // m = ab + bc + ca - 2abc
                    // m = ab + c(b + a - 2ab)
                    //   where i = ab
                    // m = i + c(b + a - 2i)
                    let i = self.mul(a.clone(), b.clone());
                    self.mul(c, b + &a - &(i.clone() * 2)) - &i
                }
                Op::Not => {
                    let a = self.get_bool(&c.cs[0]);
                    self.bool_not(a)
                }
                Op::Implies => {
                    let a = self.get_bool(&c.cs[0]).clone();
                    let b = self.get_bool(&c.cs[1]).clone();
                    let not_a = self.bool_not(&a);
                    self.nary_or(vec![not_a, b].into_iter())
                }
                Op::BoolNaryOp(o) => {
                    let args =
                        c.cs.iter()
                            .map(|c| self.get_bool(c).clone())
                            .collect::<Vec<_>>();
                    match o {
                        BoolNaryOp::Or => self.nary_or(args.into_iter()),
                        BoolNaryOp::And => self.nary_and(args.into_iter()),
                        BoolNaryOp::Xor => self.nary_xor(args.into_iter()),
                    }
                }
                Op::BvBit(i) => {
                    let a = self.get_bv_bits(&c.cs[0]);
                    a[*i].clone()
                }
                Op::BvBinPred(o) => {
                    let n = check(&c.cs[0]).as_bv();
                    use BvBinPred::*;
                    match o {
                        Sge => self.bv_cmp(n, true, false, &c.cs[0], &c.cs[1]),
                        Sgt => self.bv_cmp(n, true, true, &c.cs[0], &c.cs[1]),
                        Uge => self.bv_cmp(n, false, false, &c.cs[0], &c.cs[1]),
                        Ugt => self.bv_cmp(n, false, true, &c.cs[0], &c.cs[1]),
                        Sle => self.bv_cmp(n, true, false, &c.cs[1], &c.cs[0]),
                        Slt => self.bv_cmp(n, true, true, &c.cs[1], &c.cs[0]),
                        Ule => self.bv_cmp(n, false, false, &c.cs[1], &c.cs[0]),
                        Ult => self.bv_cmp(n, false, true, &c.cs[1], &c.cs[0]),
                    }
                }
                _ => panic!("Non-boolean in embed_bool: {}", c),
            };
            self.cache.insert(c.clone(), EmbeddedTerm::Bool(lc));
        }
        debug!("=> {}", self.r1cs.format_lc(&self.get_bool(&c).1));

        //        self.r1cs.eval(self.bools.get(&c).unwrap()).map(|v| {
        //            println!("-> {}", v);
        //        });
        self.get_bool(&c)
    }

    fn assert_bool(&mut self, t: &Term) {
        //println!("Embed: {}", c);
        // TODO: skip if already embedded
        if t.op == Op::Eq {
            t.cs.iter().for_each(|c| self.embed(c.clone()));
            self.assert_eq(&t.cs[0], &t.cs[1]);
        } else if t.op == AND {
            for c in &t.cs {
                self.assert_bool(c);
            }
        } else {
            self.embed(t.clone());
            let lc = self.get_bool(t).clone();
            self.assert_zero(lc - 1);
        }
    }

    /// Returns whether `a - b` fits in `size` non-negative bits.
    /// i.e. is in `{0, 1, ..., 2^n-1}`.
    fn bv_ge(&mut self, a: TermLc, b: &TermLc, size: usize) -> TermLc {
        self.fits_in_bits("ge", &(a - b), size, false)
    }

    /// Returns whether `a` is (`strict`ly) (`signed`ly) greater than `b`.
    /// Assumes they are each `w`-bit bit-vectors.
    fn bv_cmp(&mut self, w: usize, signed: bool, strict: bool, a: &Term, b: &Term) -> TermLc {
        let a = if signed {
            self.get_bv_signed_int(a)
        } else {
            self.get_bv_uint(a)
        };
        let b = if signed {
            self.get_bv_signed_int(b)
        } else {
            self.get_bv_uint(b)
        };
        // Use the fact: a > b <=> a - 1 >= b
        self.bv_ge(if strict { a - 1 } else { a }, &b, w)
    }

    /// Shift `x` left by `2^y`, if bit-valued `c` is true.
    fn const_pow_shift_bv(&mut self, x: &TermLc, y: usize, c: TermLc) -> TermLc {
        self.ite(c, x.clone() * (1 << (1 << y)), x)
    }

    /// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
    /// Returns an *oversized* number
    fn shift_bv(&mut self, x: TermLc, y: Vec<TermLc>, ext_bit: Option<TermLc>) -> TermLc {
        if let Some(b) = ext_bit {
            let left = self.shift_bv(x, y.clone(), None);
            let right = self.shift_bv(b.clone(), y, None) - 1;
            left + &self.mul(b, right)
        } else {
            y.into_iter()
                .enumerate()
                .fold(x, |x, (i, yi)| self.const_pow_shift_bv(&x, i, yi))
        }
    }

    /// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
    /// Returns a bit sequence.
    fn shift_bv_bits(
        &mut self,
        x: TermLc,
        y: Vec<TermLc>,
        ext_bit: Option<TermLc>,
        n: usize,
    ) -> Vec<TermLc> {
        let s = self.shift_bv(x, y, ext_bit);
        let mut bits = self.bitify("shift", &s, 2 * n - 1, false);
        bits.truncate(n);
        bits
    }

    fn embed_bv(&mut self, bv: Term) {
        //println!("Embed: {}", bv);
        //let bv2=  bv.clone();
        if let Sort::BitVector(n) = check(&bv) {
            if !self.cache.contains_key(&bv) {
                match &bv.op {
                    Op::Var(name, Sort::BitVector(_)) => {
                        let public = self.public_inputs.contains(name);
                        let var = self.fresh_var(
                            name,
                            term![Op::UbvToPf(self.field.clone()); bv.clone()],
                            public,
                        );
                        self.set_bv_uint(bv.clone(), var, n);
                        if !public {
                            self.get_bv_bits(&bv);
                        }
                    }
                    Op::Const(Value::BitVector(b)) => {
                        let bit_lcs = (0..b.width())
                            .map(|i| self.zero.clone() + b.uint().get_bit(i as u32) as isize)
                            .collect();
                        self.set_bv_bits(bv, bit_lcs);
                    }
                    Op::Ite => {
                        let c = self.get_bool(&bv.cs[0]).clone();
                        let t = self.get_bv_uint(&bv.cs[1]);
                        let f = self.get_bv_uint(&bv.cs[2]);
                        let ite = self.ite(c, t, &f);
                        self.set_bv_uint(bv, ite, n);
                    }
                    Op::BvUnOp(BvUnOp::Not) => {
                        let bits = self.get_bv_bits(&bv.cs[0]);
                        let not_bits = bits.iter().map(|bit| self.bool_not(bit)).collect();
                        self.set_bv_bits(bv, not_bits);
                    }
                    Op::BvUnOp(BvUnOp::Neg) => {
                        let x = self.get_bv_uint(&bv.cs[0]);
                        // Wrong for x == 0
                        let almost_neg_x = self.zero.clone()
                            + &self.r1cs.modulus.new_v(Integer::from(2).pow(n as u32))
                            - &x;
                        let is_zero = self.is_zero(x);
                        let neg_x = self.ite(is_zero, self.zero.clone(), &almost_neg_x);
                        self.set_bv_uint(bv, neg_x, n);
                    }
                    Op::BvUext(extra_n) => {
                        if self.bv_has_bits(&bv.cs[0]) {
                            let bits = self.get_bv_bits(&bv.cs[0]);
                            let ext_bits = std::iter::repeat(self.zero.clone()).take(*extra_n);
                            self.set_bv_bits(bv, bits.into_iter().chain(ext_bits).collect());
                        } else {
                            let x = self.get_bv_uint(&bv.cs[0]);
                            self.set_bv_uint(bv, x, n);
                        }
                    }
                    Op::BvSext(extra_n) => {
                        let mut bits = self.get_bv_bits(&bv.cs[0]).into_iter().rev();
                        let ext_bits = std::iter::repeat(bits.next().expect("sign ext empty"))
                            .take(extra_n + 1);

                        self.set_bv_bits(bv, bits.rev().chain(ext_bits).collect());
                    }
                    Op::PfToBv(nbits) => {
                        let lc = self.get_pf(&bv.cs[0]).clone();
                        let bits = self.bitify("pf2bv", &lc, *nbits, false);
                        self.set_bv_bits(bv.clone(), bits);
                    }
                    Op::BoolToBv => {
                        let b = self.get_bool(&bv.cs[0]).clone();
                        self.set_bv_bits(bv, vec![b]);
                    }
                    Op::BvNaryOp(o) => match o {
                        BvNaryOp::Xor | BvNaryOp::Or | BvNaryOp::And => {
                            let mut bits_by_bv = bv
                                .cs
                                .iter()
                                .map(|c| self.get_bv_bits(c))
                                .collect::<Vec<_>>();
                            let mut bits_bv_idx: Vec<Vec<TermLc>> = Vec::new();
                            while !bits_by_bv[0].is_empty() {
                                bits_bv_idx.push(
                                    bits_by_bv.iter_mut().map(|bv| bv.pop().unwrap()).collect(),
                                );
                            }
                            bits_bv_idx.reverse();
                            let f = |v: Vec<TermLc>| match o {
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
                                .cs
                                .iter()
                                .map(|c| self.get_bv_uint(c))
                                .collect::<Vec<_>>();
                            let (res, width) = match o {
                                BvNaryOp::Add => {
                                    let sum =
                                        values.into_iter().fold(self.zero.clone(), |s, v| s + &v);
                                    let extra_width = bitsize(bv.cs.len().saturating_sub(1));
                                    (sum, n + extra_width)
                                }
                                BvNaryOp::Mul => {
                                    if bv.cs.len() * n < f_width {
                                        let z = self.zero.clone() + 1;
                                        (
                                            values.into_iter().fold(z, |acc, v| self.mul(acc, v)),
                                            bv.cs.len() * n,
                                        )
                                    } else {
                                        let z = self.zero.clone() + 1;
                                        let p = values.into_iter().fold(z, |acc, v| {
                                            let p = self.mul(acc, v);
                                            let mut bits = self.bitify("binMul", &p, 2 * n, false);
                                            bits.truncate(n);
                                            self.debitify(bits.into_iter(), false)
                                        });
                                        (p, n)
                                    }
                                }
                                _ => unreachable!(),
                            };
                            let mut bits = self.bitify("arith", &res, width, false);
                            bits.truncate(n);
                            self.set_bv_bits(bv, bits);
                        }
                    },
                    Op::BvBinOp(o) => {
                        let a = self.get_bv_uint(&bv.cs[0]);
                        let b = self.get_bv_uint(&bv.cs[1]);
                        match o {
                            BvBinOp::Sub => {
                                let sum =
                                    a + &self.r1cs.modulus.new_v(Integer::from(2).pow(n as u32))
                                        - &b;
                                let mut bits = self.bitify("sub", &sum, n + 1, false);
                                bits.truncate(n);
                                self.set_bv_bits(bv, bits);
                            }
                            BvBinOp::Udiv | BvBinOp::Urem => {
                                let is_zero = self.is_zero(b.clone());
                                let a_bv_term = term![Op::PfToBv(n); a.0.clone()];
                                let b_bv_term = term![Op::PfToBv(n); b.0.clone()];
                                let q_term = term![Op::UbvToPf(self.field.clone()); term![BV_UDIV; a_bv_term.clone(), b_bv_term.clone()]];
                                let r_term = term![Op::UbvToPf(self.field.clone()); term![BV_UREM; a_bv_term, b_bv_term]];
                                let q = self.fresh_var("div_q", q_term, false);
                                let r = self.fresh_var("div_r", r_term, false);
                                let qb = self.bitify("div_q", &q, n, false);
                                let rb = self.bitify("div_r", &r, n, false);
                                self.r1cs.constraint(q.1.clone(), b.1.clone(), (a - &r).1);
                                let is_gt = self.bv_ge(b - 1, &r, n);
                                let is_not_ge = self.bool_not(&is_gt);
                                let is_not_zero = self.bool_not(&is_zero);
                                self.r1cs
                                    .constraint(is_not_ge.1, is_not_zero.1, self.r1cs.zero());
                                let bits = match o {
                                    BvBinOp::Udiv => qb,
                                    BvBinOp::Urem => rb,
                                    _ => unreachable!(),
                                };
                                self.set_bv_bits(bv, bits);
                            }
                            // Shift cases
                            _ => {
                                let r = b;
                                let b = bitsize(n - 1);
                                assert!(1 << b == n);
                                let mut rb = self.get_bv_bits(&bv.cs[1]);
                                rb.truncate(b);
                                let sum = self.debitify(rb.clone().into_iter(), false);
                                self.assert_zero(sum - &r);
                                let bits = match o {
                                    BvBinOp::Shl => self.shift_bv_bits(a, rb, None, n),
                                    BvBinOp::Lshr | BvBinOp::Ashr => {
                                        let mut lb = self.get_bv_bits(&bv.cs[0]);
                                        lb.reverse();
                                        let ext_bit = match o {
                                            BvBinOp::Ashr => Some(lb.first().unwrap().clone()),
                                            _ => None,
                                        };
                                        let l = self.debitify(lb.into_iter(), false);
                                        let mut bits = self.shift_bv_bits(l, rb, ext_bit, n);
                                        bits.reverse();
                                        bits
                                    }
                                    _ => unreachable!(),
                                };
                                self.set_bv_bits(bv, bits);
                            }
                        }
                    }
                    Op::BvConcat => {
                        let mut bits = Vec::new();
                        for c in bv.cs.iter().rev() {
                            bits.extend(self.get_bv_bits(c));
                        }
                        self.set_bv_bits(bv, bits);
                    }
                    // inclusive!
                    Op::BvExtract(high, low) => {
                        let bits = self
                            .get_bv_bits(&bv.cs[0])
                            .into_iter()
                            .skip(*low)
                            .take(*high - *low + 1)
                            .collect();
                        self.set_bv_bits(bv, bits);
                    }
                    _ => panic!("Non-bv in embed_bv: {}", Letified(bv)),
                }
            }
        //self.r1cs.eval(self.get_bv_uint(&bv2)).map(|v| {
        //    println!("-> {:b}", v);
        //});
        } else {
            panic!("{} is not a bit-vector in embed_bv", bv);
        }
    }

    #[allow(dead_code)]
    fn debug_lc<D: Display + ?Sized>(&self, tag: &D, lc: &TermLc) {
        println!("{}: {}", tag, self.r1cs.format_lc(&lc.1));
    }

    fn get_bool(&self, t: &Term) -> &TermLc {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bool(b) => b,
            _ => panic!("Non-boolean for {:?}", t),
        }
    }

    fn set_bv_bits(&mut self, t: Term, bits: Vec<TermLc>) {
        let sum = self.debitify(bits.iter().cloned(), false);
        assert!(!self.cache.contains_key(&t));
        self.cache.insert(
            t,
            EmbeddedTerm::Bv(Rc::new(RefCell::new(BvEntry {
                uint: sum,
                width: bits.len(),
                bits,
            }))),
        );
    }

    fn set_bv_uint(&mut self, t: Term, uint: TermLc, width: usize) {
        assert!(!self.cache.contains_key(&t));
        self.cache.insert(
            t,
            EmbeddedTerm::Bv(Rc::new(RefCell::new(BvEntry {
                uint,
                width,
                bits: Vec::new(),
            }))),
        );
    }

    fn get_bv(&self, t: &Term) -> Rc<RefCell<BvEntry>> {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bv(b) => b.clone(),
            _ => panic!("Non-bv for {:?}", t),
        }
    }

    fn bv_has_bits(&self, t: &Term) -> bool {
        !(*self.get_bv(t)).borrow().bits.is_empty()
    }

    fn get_bv_uint(&self, t: &Term) -> TermLc {
        (*self.get_bv(t)).borrow().uint.clone()
    }

    fn get_bv_signed_int(&mut self, t: &Term) -> TermLc {
        let bits = self.get_bv_bits(t);
        self.debitify(bits.into_iter(), true)
    }

    fn get_bv_bits(&mut self, t: &Term) -> Vec<TermLc> {
        let entry_rc = self.get_bv(t);
        let mut entry = entry_rc.borrow_mut();
        if entry.bits.is_empty() {
            entry.bits = self.bitify("getbits", &entry.uint, entry.width, false);
        }
        entry.bits.clone()
    }

    fn get_pf(&self, t: &Term) -> &TermLc {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Field(b) => b,
            _ => panic!("Non-field for {:?}", t),
        }
    }

    fn embed_pf(&mut self, c: Term) -> &TermLc {
        debug!("embed_pf {}", extras::Letified(c.clone()));
        //println!("Embed: {}", c);
        // TODO: skip if already embedded
        if !self.cache.contains_key(&c) {
            let lc = match &c.op {
                Op::Var(name, Sort::Field(_)) => {
                    let public = self.public_inputs.contains(name);
                    self.fresh_var(name, c.clone(), public)
                }
                Op::Const(Value::Field(r)) => TermLc(
                    c.clone(),
                    self.r1cs.constant(r.as_ty_ref(&self.r1cs.modulus)),
                ),
                Op::Ite => {
                    let cond = self.get_bool(&c.cs[0]).clone();
                    let t = self.get_pf(&c.cs[1]).clone();
                    let f = self.get_pf(&c.cs[2]).clone();
                    self.ite(cond, t, &f)
                }
                Op::PfNaryOp(o) => {
                    let args = c.cs.iter().map(|c| self.get_pf(c));
                    match o {
                        PfNaryOp::Add => args.fold(self.zero.clone(), std::ops::Add::add),
                        PfNaryOp::Mul => {
                            // Needed to end the above closures borrow of self, before the mul call
                            #[allow(clippy::needless_collect)]
                            let args = args.cloned().collect::<Vec<_>>();
                            let mut args_iter = args.into_iter();
                            let first = args_iter.next().unwrap();
                            args_iter.fold(first, |a, b| self.mul(a, b))
                        }
                    }
                }
                Op::UbvToPf(_) => self.get_bv_uint(&c.cs[0]),
                Op::PfUnOp(PfUnOp::Neg) => -self.get_pf(&c.cs[0]).clone(),
                Op::PfUnOp(PfUnOp::Recip) => {
                    let x = self.get_pf(&c.cs[0]).clone();
                    let inv_x = self.fresh_var("recip", term![PF_RECIP; x.0.clone()], false);
                    self.r1cs
                        .constraint(x.1, inv_x.1.clone(), self.r1cs.zero() + 1);
                    inv_x
                }
                _ => panic!("Non-field in embed_pf: {}", c),
            };
            self.cache.insert(c.clone(), EmbeddedTerm::Field(lc));
        }
        self.get_pf(&c)
    }

    fn assert_zero(&mut self, x: TermLc) {
        self.r1cs
            .constraint(self.r1cs.zero(), self.r1cs.zero(), x.1);
    }
    fn assert(&mut self, t: Term) {
        debug!("Assert: {}", Letified(t.clone()));
        debug_assert!(check(&t) == Sort::Bool, "Non bool in assert");
        self.assert_bool(&t);
    }
}

/// Convert this (IR) constraint system `cs` to R1CS, over a prime field defined by `modulus`.
///
/// ## Returns
///
/// * The R1CS instance
pub fn to_r1cs(mut cs: Computation, modulus: FieldT) -> (R1cs<String>, ProverData, VerifierData) {
    let assertions = cs.outputs.clone();
    let metadata = cs.metadata.clone();
    let public_inputs = metadata
        .public_input_names()
        .map(ToOwned::to_owned)
        .collect();
    debug!("public inputs: {:?}", public_inputs);
    let mut converter = ToR1cs::new(modulus, public_inputs);
    debug!(
        "Term count: {}",
        assertions
            .iter()
            .map(|c| PostOrderIter::new(c.clone()).count())
            .sum::<usize>()
    );
    debug!("declaring inputs");
    for i in metadata.public_inputs() {
        debug!("input {}", i);
        converter.embed(i);
    }
    debug!("Printing assertions");
    for c in assertions {
        converter.assert(c);
    }
    debug!("r1cs public inputs: {:?}", converter.r1cs.public_idxs,);
    cs.precomputes = cs.precomputes.sequential_compose(&converter.wit_ext);
    let r1cs = converter.r1cs;
    let prover_data = r1cs.prover_data(&cs);
    let verifier_data = r1cs.verifier_data(&cs);
    (r1cs, prover_data, verifier_data)
}

#[cfg(test)]
pub mod test {
    use super::*;
    use crate::util::field::DFL_T;

    use crate::ir::proof::Constraints;
    use crate::ir::term::dist::test::*;
    use crate::ir::term::dist::*;
    use crate::target::r1cs::opt::reduce_linearities;

    use circ_fields::FieldT;
    use fxhash::FxHashMap;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    fn init() {
        let _ = env_logger::builder().is_test(true).try_init();
    }

    #[test]
    fn bool() {
        init();
        let values: FxHashMap<String, Value> = vec![
            ("a".to_owned(), Value::Bool(true)),
            ("b".to_owned(), Value::Bool(false)),
        ]
        .into_iter()
        .collect();
        let cs = Computation::from_constraint_system_parts(
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool)),
            ],
        );
        let (r1cs, pd, _) = to_r1cs(cs, FieldT::from(Integer::from(17)));
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[derive(Clone, Debug)]
    pub struct PureBool(pub Term, pub FxHashMap<String, Value>);

    impl Arbitrary for PureBool {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let t = PureBoolDist(g.size()).sample(&mut rng);
            let values: FxHashMap<String, Value> = PostOrderIter::new(t.clone())
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
            let ts = PostOrderIter::new(self.0.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .rev();

            Box::new(ts.skip(1).map(move |t| PureBool(t, vs.clone())))
        }
    }

    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_bool(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_pure_bool_opt(ArbitraryBoolEnv(t, values): ArbitraryBoolEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    #[quickcheck]
    fn random_bool_opt(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    #[test]
    fn eq_test() {
        let values = vec![(
            "b".to_owned(),
            Value::BitVector(BitVector::new(Integer::from(152), 8)),
        )]
        .into_iter()
        .collect();

        let cs = Computation::from_constraint_system_parts(
            vec![term![Op::Not; term![Op::Eq; bv(0b10110, 8),
                              term![Op::BvUnOp(BvUnOp::Neg); leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))]]]],
            vec![leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))],
        );
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }

    #[test]
    fn not_opt_test() {
        init();
        let t = term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))];
        let values: FxHashMap<String, Value> = vec![("b".to_owned(), Value::Bool(true))]
            .into_iter()
            .collect();
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let cs = Computation::from_constraint_system_parts(vec![t], vec![]);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
        let r1cs2 = reduce_linearities(r1cs, None);
        r1cs2.check_all(&extended_values);
    }

    /// A bit-vector literal with value `u` and size `w`
    pub fn bv(u: usize, w: usize) -> Term {
        leaf_term(Op::Const(Value::BitVector(BitVector::new(
            Integer::from(u),
            w,
        ))))
    }

    fn pf(i: isize) -> Term {
        leaf_term(Op::Const(Value::Field(DFL_T.new_v(i))))
    }

    fn const_test(term: Term) {
        let mut cs = Computation::new();
        cs.assert(term);
        let (r1cs, pd, _) = to_r1cs(cs, DFL_T.clone());
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&Default::default());
        r1cs.check_all(&extended_values);
    }

    #[test]
    fn div_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b1111,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b0001,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b0111,4), bv(0b0000,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv(0b1111,4), bv(0b0010,4)],
            bv(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b1111,4)],
            bv(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b0001,4)],
            bv(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b0111,4), bv(0b0000,4)],
            bv(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv(0b1111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
    }

    #[test]
    fn sh_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv(0b1111,4), bv(0b0011,4)],
            bv(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv(0b1101,4), bv(0b0010,4)],
            bv(0b0100, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv(0b1111,4), bv(0b0011,4)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv(0b0111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv(0b0111,4), bv(0b0010,4)],
            bv(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv(0b1111,4), bv(0b0011,4)],
            bv(0b0001, 4)
        ]);
    }

    #[test]
    fn pf2bv() {
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf(8)],
            bv(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf(15)],
            bv(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(8); pf(15)],
            bv(0b1111, 8)
        ]);
    }

    #[test]
    fn tuple() {
        let values = vec![
            ("a".to_owned(), Value::Bool(true)),
            ("b".to_owned(), Value::Bool(false)),
        ]
        .into_iter()
        .collect();
        let mut cs = Computation::from_constraint_system_parts(
            vec![
                term![Op::Field(0); term![Op::Tuple; leaf_term(Op::Var("a".to_owned(), Sort::Bool)), leaf_term(Op::Const(Value::Bool(false)))]],
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool)),
            ],
        );
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let (r1cs, pd, _) = to_r1cs(cs, FieldT::from(Integer::from(17)));
        let precomp = pd.precompute;
        let extended_values = precomp.eval(&values);
        r1cs.check_all(&extended_values);
    }
}
