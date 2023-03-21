//! Translation from IR to MILP
//!
//!

// Needed until https://github.com/rust-lang/rust-clippy/pull/8183 is resolved.
#![allow(clippy::identity_op)]

use crate::ir::term::*;
use crate::target::bitsize;
use crate::target::ilp::Ilp;

use good_lp::{variable, Expression};
use log::debug;

use std::cell::RefCell;
use std::convert::TryInto;
use std::fmt::Display;
use std::rc::Rc;

#[derive(Clone)]
enum EmbeddedTerm {
    /// Constrained to be zero or one
    Bool(Expression),
    Bv(Rc<RefCell<BvEntry>>),
}

struct BvEntry {
    width: usize,
    uint: Expression,
    /// LSB in index 0
    bits: Vec<Expression>,
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
            cache: TermMap::default(),
            next_idx: 0,
        }
    }

    /// Take the converted ILP instance and garbage collect
    fn take_ilp(mut self) -> Ilp {
        self.cache.clear();
        garbage_collect();
        self.ilp
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bit<D: Display + ?Sized>(&mut self, ctx: &D) -> Expression {
        let n = format!("{}_v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.ilp.new_variable(variable().binary(), n).into()
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bv<D: Display + ?Sized>(&mut self, ctx: &D, bits: usize) -> Expression {
        let n = format!("{}_v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.bv_lit(n, bits)
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_int<D: Display + ?Sized>(&mut self, ctx: &D) -> Expression {
        let n = format!("{}_v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.ilp.new_variable(variable().integer(), n).into()
    }

    /// Get a new variable, named `name`.
    fn bit(&mut self, name: String) -> Expression {
        self.ilp.new_variable(variable().binary(), name).into()
    }

    /// Get a new BV variable, named `name`.
    fn bv_lit(&mut self, name: String, bits: usize) -> Expression {
        self.ilp
            .new_variable(
                variable()
                    .integer()
                    .min(0)
                    .max(2.0f64.powi(bits as i32) - 1.0),
                name,
            )
            .into()
    }

    fn embed(&mut self, t: Term) {
        debug!("Embed: {}", t);
        for c in PostOrderIter::new(t) {
            debug!("Embed op: {}", c.op());
            match check(&c) {
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
            sum += x;
            bounds.push((r.clone() - x) << 0);
        }
        assert!(n >= 1);
        self.ilp.new_constraint(sum << (n - 1));
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
            .map(|i| self.fresh_bit(&format!("bit{i}")))
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
            Sort::BitVector(n) => {
                let a = self.get_bv_uint(a);
                let b = self.get_bv_uint(b);
                self.bv_cmp_eq(&a, &b, n)
            }
            s => panic!("Unimplemented sort for Eq: {:?}", s),
        }
    }

    fn embed_bool(&mut self, c: Term) -> &Expression {
        debug_assert!(check(&c) == Sort::Bool);
        if !self.cache.contains_key(&c) {
            let lc = match &c.op() {
                Op::Var(name, Sort::Bool) => self.bit(name.to_string()),
                Op::Const(Value::Bool(b)) => Expression::from(*b as i32),
                Op::Eq => self.embed_eq(&c.cs()[0], &c.cs()[1]),
                Op::Ite => {
                    let a = self.get_bool(&c.cs()[0]).clone();
                    let not_a = self.bit_not(&a);
                    let b = self.get_bool(&c.cs()[1]).clone();
                    let c = self.get_bool(&c.cs()[2]).clone();
                    let a_and_b = self.bit_and(&[a, b]);
                    let not_a_and_c = self.bit_and(&[not_a, c]);
                    self.bit_or(&[a_and_b, not_a_and_c])
                }
                Op::Not => {
                    let a = self.get_bool(&c.cs()[0]);
                    self.bit_not(a)
                }
                Op::Implies => {
                    let a = self.get_bool(&c.cs()[0]).clone();
                    let b = self.get_bool(&c.cs()[1]).clone();
                    let not_a = self.bit_not(&a);
                    self.bit_or(&[not_a, b])
                }
                Op::BoolNaryOp(o) => {
                    let args = c
                        .cs()
                        .iter()
                        .map(|c| self.get_bool(c).clone())
                        .collect::<Vec<_>>();
                    match o {
                        BoolNaryOp::Or => self.bit_or(args.iter()),
                        BoolNaryOp::And => self.bit_and(args.iter()),
                        BoolNaryOp::Xor => self.bit_xor(args.iter()),
                    }
                }
                Op::BvBinPred(o) => {
                    let n = check(&c.cs()[0]).as_bv();
                    use BvBinPred::*;
                    match o {
                        Sge => self.bv_cmp(n, true, false, &c.cs()[0], &c.cs()[1]),
                        Sgt => self.bv_cmp(n, true, true, &c.cs()[0], &c.cs()[1]),
                        Uge => self.bv_cmp(n, false, false, &c.cs()[0], &c.cs()[1]),
                        Ugt => self.bv_cmp(n, false, true, &c.cs()[0], &c.cs()[1]),
                        Sle => self.bv_cmp(n, true, false, &c.cs()[1], &c.cs()[0]),
                        Slt => self.bv_cmp(n, true, true, &c.cs()[1], &c.cs()[0]),
                        Ule => self.bv_cmp(n, false, false, &c.cs()[1], &c.cs()[0]),
                        Ult => self.bv_cmp(n, false, true, &c.cs()[1], &c.cs()[0]),
                    }
                }
                _ => panic!("Non-boolean in embed_bool: {}", c),
            };
            self.cache.insert(c.clone(), EmbeddedTerm::Bool(lc));
        }
        self.get_bool(&c)
    }

    // Largely based on "RTL-Datapath Verification using Integer Linear Programming"
    // and "LPSAT: A Unified Approach to RTL Satisfiability"
    //
    // https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=995022
    // https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055
    fn embed_bv(&mut self, bv: Term) {
        if let Sort::BitVector(n) = check(&bv) {
            if !self.cache.contains_key(&bv) {
                match &bv.op() {
                    Op::Var(name, Sort::BitVector(n_bits)) => {
                        let var = self.bv_lit(name.clone(), *n_bits);
                        self.set_bv_uint(bv.clone(), var, n);
                    }
                    Op::Const(Value::BitVector(b)) => {
                        let bit_lcs = (0..b.width())
                            .map(|i| Expression::from(b.uint().get_bit(i as u32) as i32))
                            .collect();
                        self.set_bv_bits(bv, bit_lcs);
                    }
                    Op::Ite => {
                        let c = self.get_bool(&bv.cs()[0]).clone();
                        let t = self.get_bv_uint(&bv.cs()[1]);
                        let f = self.get_bv_uint(&bv.cs()[2]);
                        let ite = self.bv_ite(&c, &t, &f, n);
                        self.set_bv_uint(bv, ite, n);
                    }
                    Op::BvUnOp(BvUnOp::Not) => {
                        let bits = self.get_bv_bits(&bv.cs()[0]);
                        let not_bits = bits.iter().map(|bit| self.bit_not(bit)).collect();
                        self.set_bv_bits(bv, not_bits);
                    }
                    Op::BvUnOp(BvUnOp::Neg) => {
                        let x = self.get_bv_uint(&bv.cs()[0]);
                        // Wrong for x == 0
                        let almost_neg_x = 2f64.powi(n as i32) - x.clone();
                        let is_zero = self.bv_cmp_eq(&x, &0.into(), n);
                        let neg_x = self.bv_ite(&is_zero, &Expression::from(0), &almost_neg_x, n);
                        self.set_bv_uint(bv, neg_x, n);
                    }
                    Op::BvUext(extra_n) => {
                        if self.bv_has_bits(&bv.cs()[0]) {
                            let bits = self.get_bv_bits(&bv.cs()[0]);
                            let ext_bits = std::iter::repeat(Expression::from(0)).take(*extra_n);
                            self.set_bv_bits(bv, bits.into_iter().chain(ext_bits).collect());
                        } else {
                            let x = self.get_bv_uint(&bv.cs()[0]);
                            self.set_bv_uint(bv, x, n);
                        }
                    }
                    Op::BvSext(extra_n) => {
                        let mut bits = self.get_bv_bits(&bv.cs()[0]).into_iter().rev();
                        let ext_bits = std::iter::repeat(bits.next().expect("sign ext empty"))
                            .take(extra_n + 1);

                        self.set_bv_bits(bv, bits.rev().chain(ext_bits).collect());
                    }
                    Op::BoolToBv => {
                        let b = self.get_bool(&bv.cs()[0]).clone();
                        self.set_bv_bits(bv, vec![b]);
                    }
                    Op::BvNaryOp(o) => match o {
                        BvNaryOp::Xor | BvNaryOp::Or | BvNaryOp::And => {
                            let mut bits_by_bv = bv
                                .cs()
                                .iter()
                                .map(|c| self.get_bv_bits(c))
                                .collect::<Vec<_>>();
                            let mut bits_bv_idx: Vec<Vec<Expression>> = Vec::new();
                            while !bits_by_bv[0].is_empty() {
                                bits_bv_idx.push(
                                    bits_by_bv.iter_mut().map(|bv| bv.pop().unwrap()).collect(),
                                );
                            }
                            bits_bv_idx.reverse();
                            let f = |v: Vec<Expression>| match o {
                                BvNaryOp::And => self.bit_and(&v),
                                BvNaryOp::Or => self.bit_or(&v),
                                BvNaryOp::Xor => self.bit_xor(&v),
                                _ => unreachable!(),
                            };
                            let res = bits_bv_idx.into_iter().map(f).collect();
                            self.set_bv_bits(bv, res);
                        }
                        BvNaryOp::Add | BvNaryOp::Mul => {
                            //let f_width = self.ilp.modulus().significant_bits() as usize - 1;
                            let values = bv
                                .cs()
                                .iter()
                                .map(|c| self.get_bv_uint(c))
                                .collect::<Vec<_>>();
                            let r = match o {
                                BvNaryOp::Add => self.bv_add(&values, n),
                                BvNaryOp::Mul => self.bv_mul(&values, n),
                                _ => unreachable!(),
                            };
                            self.set_bv_uint(bv, r, n);
                        }
                    },
                    Op::BvBinOp(o) => {
                        let a = self.get_bv_uint(&bv.cs()[0]);
                        let b = self.get_bv_uint(&bv.cs()[1]);
                        match o {
                            BvBinOp::Sub => {
                                let sum = a - b;
                                let r = self.fresh_bv("sub_r", n);
                                let q = self.fresh_int("sub_q");
                                self.ilp
                                    .new_constraint(sum.eq(r.clone() + bv_modulus(n) * q));
                                self.set_bv_uint(bv, r, n);
                            }
                            //BvBinOp::Udiv | BvBinOp::Urem => {
                            //    let b = b.clone();
                            //    let a = a.clone();
                            //    let is_zero = self.is_zero(b.clone());
                            //    let (q_v, r_v) = self
                            //        .r1cs
                            //        .eval(&a)
                            //        .and_then(|a| {
                            //            self.r1cs.eval(&b).map(|b| {
                            //                if b == 0 {
                            //                    ((Integer::from(1) << n as u32) - 1, a)
                            //                } else {
                            //                    (a.clone() / &b, a % b)
                            //                }
                            //            })
                            //        })
                            //        .map(|(a, b)| (Some(a), Some(b)))
                            //        .unwrap_or((None, None));
                            //    let q = self.fresh_var("div_q", q_v);
                            //    let r = self.fresh_var("div_q", r_v);
                            //    let qb = self.bitify("div_q", &q, n, false);
                            //    let rb = self.bitify("div_r", &r, n, false);
                            //    self.r1cs.constraint(q.clone(), b.clone(), a - &r);
                            //    let is_gt = self.bv_ge(b - 1, &r, n);
                            //    let is_not_ge = self.bool_not(&is_gt);
                            //    let is_not_zero = self.bool_not(&is_zero);
                            //    self.r1cs
                            //        .constraint(is_not_ge, is_not_zero, self.r1cs.zero());
                            //    let bits = match o {
                            //        BvBinOp::Udiv => qb,
                            //        BvBinOp::Urem => rb,
                            //        _ => unreachable!(),
                            //    };
                            //    self.set_bv_bits(bv, bits);
                            //}
                            // Shift cases
                            //_ => {
                            //    let r = b.clone();
                            //    let a = a.clone();
                            //    let b = bitsize(n - 1);
                            //    assert!(1 << b == n);
                            //    let mut rb = self.get_bv_bits(&bv.cs()[1]);
                            //    rb.truncate(b);
                            //    let sum = self.debitify(rb.clone().into_iter(), false);
                            //    self.assert_zero(sum - &r);
                            //    let bits = match o {
                            //        BvBinOp::Shl => self.shift_bv_bits(a, rb, None, n),
                            //        BvBinOp::Lshr | BvBinOp::Ashr => {
                            //            let mut lb = self.get_bv_bits(&bv.cs()[0]);
                            //            lb.reverse();
                            //            let ext_bit = match o {
                            //                BvBinOp::Ashr => Some(lb.first().unwrap().clone()),
                            //                _ => None,
                            //            };
                            //            let l = self.debitify(lb.into_iter(), false);
                            //            let mut bits = self.shift_bv_bits(l, rb, ext_bit, n);
                            //            bits.reverse();
                            //            bits
                            //        }
                            //        _ => unreachable!(),
                            //    };
                            //    self.set_bv_bits(bv, bits);
                            //}
                            _ => todo!(),
                        }
                    }
                    Op::BvConcat => {
                        let mut bits = Vec::new();
                        for c in bv.cs().iter().rev() {
                            bits.extend(self.get_bv_bits(c));
                        }
                        self.set_bv_bits(bv, bits);
                    }
                    //// inclusive!
                    Op::BvExtract(high, low) => {
                        let bits = self
                            .get_bv_bits(&bv.cs()[0])
                            .into_iter()
                            .skip(*low)
                            .take(*high - *low + 1)
                            .collect();
                        self.set_bv_bits(bv, bits);
                    }
                    _ => panic!("Non-bv in embed_bv: {}", bv),
                }
            }
        } else {
            panic!("{} is not a bit-vector in embed_bv", bv);
        }
    }

    fn bv_add<'a>(
        &mut self,
        xs: impl IntoIterator<Item = &'a Expression>,
        n_bits: usize,
    ) -> Expression {
        let sum = xs.into_iter().fold(Expression::from(0), |acc, x| acc + x);
        let r = self.fresh_bv("add_r", n_bits);
        let q = self.fresh_bv("add_q", n_bits);
        self.ilp
            .new_constraint(sum.eq(r.clone() + bv_modulus(n_bits) * q));
        r
    }
    /// [Equations 3 through 6](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055).
    fn bv_ite(
        &mut self,
        s: &Expression,
        a: &Expression,
        b: &Expression,
        n_bits: usize,
    ) -> Expression {
        let r = self.fresh_bv("bv_ite", n_bits);
        let m = bv_modulus(n_bits);
        self.ilp
            .new_constraint((r.clone() - a.clone() - m * (1 - s.clone())) << 0);
        self.ilp
            .new_constraint((a.clone() - r.clone() - m * (1 - s.clone())) << 0);
        self.ilp
            .new_constraint((r.clone() - b.clone() - m * s.clone()) << 0);
        self.ilp
            .new_constraint((b.clone() - r.clone() - m * s.clone()) << 0);
        r
    }

    /// [Equations 7](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055).
    fn bv_bin_mul(&mut self, a: &Expression, b: &Expression, n_bits: usize) -> Expression {
        debug!("({:?}) * ({:?})", a, b);
        let a_bits = self.bit_decomp(a, n_bits);
        let bit_prods: Vec<_> = a_bits
            .into_iter()
            .enumerate()
            .map(|(i, a_bit)| {
                2.0f64.powi(i as i32) * self.bv_ite(&a_bit, b, &Expression::from(0), n_bits)
            })
            .collect();
        for (i, p) in bit_prods.iter().enumerate() {
            debug!("bit {}: {:?}", i, p);
        }
        self.bv_add(&bit_prods, n_bits)
    }

    fn bv_mul<'a>(
        &mut self,
        xs: impl IntoIterator<Item = &'a Expression>,
        n_bits: usize,
    ) -> Expression {
        xs.into_iter().fold(Expression::from(1), |acc, x| {
            self.bv_bin_mul(&acc, x, n_bits)
        })
    }
    /// [Similar to Equations 1, 2](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055).
    fn bv_cmp_eq(&mut self, a: &Expression, b: &Expression, n_bits: usize) -> Expression {
        let le = self.bv_cmp_le(a, b, n_bits);
        let ge = self.bv_cmp_le(b, a, n_bits);
        self.bit_and(&[le, ge])
    }

    /// [Equations 1, 2](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055).
    fn bv_cmp_lt(&mut self, a: &Expression, b: &Expression, n_bits: usize) -> Expression {
        debug!("({:?}) < ({:?})", a, b);
        let s = self.fresh_bit("bv_le");
        let m = bv_modulus(n_bits);
        self.ilp
            .new_constraint((a.clone() - b.clone() - m * (1 - s.clone())) << -1);
        self.ilp
            .new_constraint((a.clone() - b.clone() + m * s.clone()) >> 0);
        s
    }

    /// [Equations 1, 2](https://ieeexplore.ieee.org/stamp/stamp.jsp?tp=&arnumber=915055).
    fn bv_cmp_le(&mut self, a: &Expression, b: &Expression, n_bits: usize) -> Expression {
        let not = self.bv_cmp_lt(b, a, n_bits);
        self.bit_not(&not)
    }

    /// Returns whether `a` is (`strict`ly) (`signed`ly) greater than `b`.
    /// Assumes they are each `w`-bit bit-vectors.
    fn bv_cmp(&mut self, w: usize, signed: bool, strict: bool, a: &Term, b: &Term) -> Expression {
        //assert!(!signed, "TODO: signed cmp");
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
        if strict {
            self.bv_cmp_lt(&b, &a, w)
        } else {
            self.bv_cmp_le(&b, &a, w)
        }
    }

    /// Given a sequence of `bits`, returns a wire which represents their sum,
    /// `\sum_{i>0} b_i2^i`.
    ///
    /// If `signed` is set, then the MSB is negated; i.e., the two's-complement sum is returned.
    fn debitify<I: ExactSizeIterator<Item = Expression>>(
        &self,
        bits: I,
        signed: bool,
    ) -> Expression {
        let n = bits.len();
        bits.enumerate().fold(Expression::from(0), |sum, (i, bit)| {
            let summand = bit * 2f64.powi(i as i32);
            if signed && i + 1 == n {
                sum - &summand
            } else {
                sum + &summand
            }
        })
    }

    fn get_bool(&self, t: &Term) -> &Expression {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bool(b) => b,
            _ => panic!("Non-bool for {:?}", t),
        }
    }

    fn set_bv_bits(&mut self, t: Term, bits: Vec<Expression>) {
        debug!("{} -> {:?}", t, bits);
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

    fn set_bv_uint(&mut self, t: Term, uint: Expression, width: usize) {
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
        !self.get_bv(t).borrow().bits.is_empty()
    }

    fn get_bv_uint(&self, t: &Term) -> Expression {
        self.get_bv(t).borrow().uint.clone()
    }

    fn get_bv_signed_int(&mut self, t: &Term) -> Expression {
        let bits = self.get_bv_bits(t);
        self.debitify(bits.into_iter(), true)
    }

    fn get_bv_bits(&mut self, t: &Term) -> Vec<Expression> {
        let entry_rc = self.get_bv(t);
        let mut entry = entry_rc.borrow_mut();
        if entry.bits.is_empty() {
            entry.bits = self.bit_decomp(&entry.uint, entry.width);
        }
        entry.bits.clone()
    }

    fn assert(&mut self, t: Term) {
        debug!("Assert: {}", t);
        self.embed(t.clone());
        let lc = self.get_bool(&t).clone();
        self.ilp.new_constraint(lc.eq(1));
    }
}

fn bv_modulus(n_bits: usize) -> f64 {
    2.0f64.powi(n_bits.try_into().unwrap())
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
        Sort::BitVector(_) => {
            converter.ilp.maximize(converter.get_bv_uint(&opt));
        }
        s => panic!("Cannot optimize term of sort {}", s),
    };

    converter.take_ilp()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::Constraints;
    use crate::ir::term::dist::test::PureBool;
    use crate::ir::term::test as test_vecs;
    use approx::assert_abs_diff_eq;
    use good_lp::default_solver;
    use quickcheck_macros::quickcheck;

    fn init() {
        let _ = env_logger::builder()
            .format_timestamp(None)
            .is_test(true)
            .try_init();
    }

    #[test]
    fn bool_test() {
        let cs = Computation {
            outputs: vec![
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                term![Op::Not; leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
                // max this
                term![AND;
                leaf_term(Op::Var("a".to_owned(), Sort::Bool)),
                leaf_term(Op::Var("b".to_owned(), Sort::Bool))],
            ],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let r = ilp.solve(default_solver).unwrap().1;
        assert_eq!(r.get("a").unwrap(), &1.0);
        assert_eq!(r.get("b").unwrap(), &0.0);
    }

    #[ignore]
    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(
            vec![t, leaf_term(Op::Const(Value::Bool(true)))],
            Vec::new(),
        );
        let mut ilp = to_ilp(cs);
        for (v, val) in &values {
            match val {
                Value::Bool(true) => {
                    if let Some(var) = ilp.var_names.get(v) {
                        let e = Expression::from(*var);
                        ilp.new_constraint(e.eq(1.0));
                    }
                }
                Value::Bool(false) => {
                    if let Some(var) = ilp.var_names.get(v) {
                        let e = Expression::from(*var);
                        ilp.new_constraint(e.eq(0.0));
                    }
                }
                _ => unreachable!(),
            }
        }
        let r = ilp.solve(default_solver);
        let solution = r.unwrap().1;
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

    fn const_test(term: Term) {
        init();
        let mut cs = Computation::new();
        cs.assert(term.clone());
        cs.assert(leaf_term(Op::Const(Value::Bool(true))));
        let ilp = to_ilp(cs);
        let r = ilp.solve(default_solver);
        if r.is_err() {
            panic!("Error: {:?} on {}", r, term)
        }
    }

    #[test]
    fn bool_and_test() {
        test_vecs::bool_and_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_eq_test() {
        test_vecs::bv_eq_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn bv_le_test() {
        test_vecs::bv_le_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn bv_lt_test() {
        test_vecs::bv_le_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn bv_sle_test() {
        test_vecs::bv_sle_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn bv_slt_test() {
        test_vecs::bv_sle_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn bv_and_test() {
        test_vecs::bv_and_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_or_test() {
        test_vecs::bv_or_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_add_test() {
        test_vecs::bv_add_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_mul_test() {
        test_vecs::bv_mul_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_concat_test() {
        test_vecs::bv_concat_tests()
            .into_iter()
            .for_each(const_test)
    }
    #[test]
    fn bv_neg_test() {
        test_vecs::bv_neg_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_not_test() {
        test_vecs::bv_not_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_sext_test() {
        test_vecs::bv_sext_tests().into_iter().for_each(const_test)
    }
    #[test]
    fn bv_uext_test() {
        test_vecs::bv_uext_tests().into_iter().for_each(const_test)
    }

    #[test]
    fn trivial_bv_opt() {
        let cs = Computation {
            outputs: vec![leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4)))],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let (max, vars) = ilp.solve(default_solver).unwrap();
        assert_eq!(max, 15.0);
        assert_eq!(vars.get("a").unwrap(), &15.0);
    }

    #[test]
    fn mul1_bv_opt() {
        let cs = Computation {
            outputs: vec![term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4))),
                bv_lit(1,4)
            ]],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let (max, vars) = ilp.solve(default_solver).unwrap();
        assert_abs_diff_eq!(max, 15.0, epsilon = 0.2);
        assert_abs_diff_eq!(vars.get("a").unwrap(), &15.0, epsilon = 0.2);
    }
    #[test]
    fn mul2_bv_opt() {
        let cs = Computation {
            outputs: vec![term![BV_MUL;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4))),
                bv_lit(2,4)
            ]],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let (max, _vars) = ilp.solve(default_solver).unwrap();
        assert_abs_diff_eq!(max, 14.0, epsilon = 0.2);
    }
    #[test]
    fn mul2_plus_bv_opt() {
        let cs = Computation {
            outputs: vec![term![BV_ADD;
                term![BV_MUL;
                    leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4))),
                    bv_lit(2,4)
                ],

                    leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4)))
            ]],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let (max, vars) = ilp.solve(default_solver).unwrap();
        assert_abs_diff_eq!(max, 15.0, epsilon = 0.2);
        assert_abs_diff_eq!(vars.get("a").unwrap(), &5.0, epsilon = 0.2);
    }
    #[test]
    fn ite_bv_opt() {
        let a = leaf_term(Op::Var("a".to_owned(), Sort::BitVector(4)));
        let c = leaf_term(Op::Var("c".to_owned(), Sort::Bool));
        let cs = Computation {
            outputs: vec![term![BV_ADD;
            term![ITE; c, bv_lit(2,4), bv_lit(1,4)],
            term![BV_MUL; a, bv_lit(2,4)]
            ]],
            ..Default::default()
        };
        let ilp = to_ilp(cs);
        let (max, vars) = ilp.solve(default_solver).unwrap();
        assert_abs_diff_eq!(max, 15.0, epsilon = 0.2);
        assert_abs_diff_eq!(vars.get("c").unwrap(), &0.0, epsilon = 0.2);
    }
}
