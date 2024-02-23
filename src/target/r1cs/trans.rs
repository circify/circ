//! Lowering IR to R1CS
//!
//! [Ben Braun's
//! thesis](https://github.com/circify/circ/tree/master/doc/resources/braun-bs-thesis.pdf)
//! is a good intro to how this process works.
use crate::cfg::CircCfg;
use crate::ir::term::*;
use crate::target::bitsize;
use crate::target::r1cs::*;

use circ_fields::FieldT;
use circ_opt::FieldDivByZero;
use log::{debug, trace};
use rug::ops::Pow;
use rug::Integer;

use std::cell::RefCell;
use std::fmt::Display;
use std::iter::ExactSizeIterator;
use std::rc::Rc;

struct BvEntry {
    width: usize,
    /// Empty if not yet created.
    uint: Option<TermLc>,
    /// Empty if not yet created.
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

#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Metric {
    n_constraints: u32,
    n_vars: u32,
}

impl std::ops::AddAssign<&Metric> for Metric {
    fn add_assign(&mut self, rhs: &Metric) {
        self.n_vars += rhs.n_vars;
        self.n_constraints += rhs.n_constraints;
    }
}

struct ToR1cs<'cfg> {
    r1cs: R1cs,
    cache: TermMap<EmbeddedTerm>,
    embed: Rc<RefCell<TermSet>>,
    next_idx: usize,
    zero: TermLc,
    one: TermLc,
    cfg: &'cfg CircCfg,
    field: FieldT,
    used_vars: HashSet<String>,
    profiling_data: TermMap<Metric>,
    metric: Metric,
    term_in_progress: Option<Term>,
}

impl<'cfg> ToR1cs<'cfg> {
    fn new(cfg: &'cfg CircCfg, precompute: precomp::PreComp, used_vars: HashSet<String>) -> Self {
        let field = cfg.field().clone();
        debug!("Starting R1CS back-end, field: {}", field);
        let r1cs = R1cs::new(field.clone(), precompute);
        let zero = TermLc(pf_lit(field.new_v(0u8)), r1cs.zero());
        let one = zero.clone() + 1;
        Self {
            r1cs,
            cache: TermMap::default(),
            embed: Default::default(),
            used_vars,
            next_idx: 0,
            zero,
            one,
            field,
            cfg,
            profiling_data: Default::default(),
            term_in_progress: None,
            metric: Default::default(),
        }
    }

    fn profile_start_term(&mut self, t: Term) {
        if self.cfg.r1cs.profile {
            assert!(self.term_in_progress.is_none());
            self.term_in_progress = Some(t);
            self.metric = Default::default();
        }
    }

    fn profile_end_term(&mut self) {
        if self.cfg.r1cs.profile {
            assert!(self.term_in_progress.is_some());
            let t = self.term_in_progress.take().unwrap();
            *self.profiling_data.entry(t).or_default() += &self.metric;
            self.metric = Default::default();
        }
    }

    fn profile_print(&self) {
        if self.cfg.r1cs.profile {
            let terms: TermSet = self.profiling_data.keys().cloned().collect();
            let mut cum_metrics: TermMap<Metric> = Default::default();
            for t in PostOrderIter::from_roots_and_skips(terms, Default::default()) {
                let mut cum = Metric::default();
                if let Some(d) = self.profiling_data.get(&t) {
                    cum += d;
                }
                for c in t.cs() {
                    cum += cum_metrics.get(c).unwrap();
                }
                cum_metrics.insert(t, cum);
            }
            let mut data: Vec<(Term, Metric, Metric)> = cum_metrics
                .into_iter()
                .map(|(term, cum)| {
                    let indiv = self
                        .profiling_data
                        .get(&term)
                        .cloned()
                        .unwrap_or(Default::default());
                    (term, cum, indiv)
                })
                .collect();
            data.sort_by(|(t0, c0, i0), (t1, c1, i1)| i0.cmp(i1).then(c0.cmp(c1)).then(t0.cmp(t1)));
            data.reverse();
            for (t, c, i) in data {
                if c.n_constraints != 0 {
                    println!(
                        "{:>8}: {:>8}cs cum, {:>8}vs cum, {:>8}cs, {:>8}vs;   {} {:?}",
                        format!("{}", t.id()),
                        c.n_constraints,
                        c.n_vars,
                        i.n_constraints,
                        i.n_vars,
                        t.op(),
                        t.cs().iter().map(|c| c.id()).collect::<Vec<_>>(),
                    )
                }
            }
        }
    }

    /// Create a committed witness vector. Each input is a (name, term) pair.
    fn committed_wit(&mut self, elements: Vec<(String, Term)>) {
        self.r1cs.add_committed_witness(elements.clone());
        for (name, value) in elements {
            let lc = self.r1cs.signal_lc(&name);
            let var = leaf_term(Op::Var(name, check(&value)));
            self.embed.borrow_mut().insert(var.clone());
            self.cache
                .insert(var, EmbeddedTerm::Field(TermLc(value, lc)));
        }
    }

    /// Get a new variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    ///
    /// `comp` is a term that computes the value.
    fn fresh_var<D: Display + ?Sized>(&mut self, ctx: &D, comp: Term, ty: VarType) -> TermLc {
        let n = if matches!(ty, VarType::Chall) {
            format!("{ctx}")
        } else {
            format!("{ctx}_n{}", self.next_idx)
        };
        self.next_idx += 1;
        debug_assert!(matches!(check(&comp), Sort::Field(_)));
        self.r1cs.add_var(n.clone(), comp.clone(), ty);
        self.metric.n_vars += 1;
        debug!("fresh: {n:?}");
        TermLc(comp, self.r1cs.signal_lc(&n))
    }

    /// Get a new witness. See [ToR1cs::fresh_var].
    fn fresh_wit<D: Display + ?Sized>(&mut self, ctx: &D, comp: Term) -> TermLc {
        self.fresh_var(ctx, comp, VarType::FinalWit)
    }

    /// Create a constraint
    fn constraint(&mut self, a: Lc, b: Lc, c: Lc) {
        self.metric.n_constraints += 1;
        self.r1cs.constraint(a, b, c);
    }

    /// Enforce `x` to be bit-valued
    fn enforce_bit(&mut self, b: TermLc) {
        self.constraint(b.1.clone(), (b - 1).1, self.r1cs.zero());
    }

    /// Get a new bit-valued variable, with name dependent on `d`.
    /// If values are being recorded, `value` must be provided.
    fn fresh_bit<D: Display + ?Sized>(&mut self, ctx: &D, comp: Term) -> TermLc {
        debug_assert!(matches!(check(&comp), Sort::Bool));
        let comp = term![Op::Ite; comp, self.one.0.clone(), self.zero.0.clone()];
        let v = self.fresh_var(ctx, comp, VarType::FinalWit);
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
        let m = self.fresh_wit(
            "is_zero_inv",
            term![Op::Ite; eqz.clone(), self.zero.0.clone(), term![PF_RECIP; x.0.clone()]],
        );
        let is_zero = self.fresh_wit(
            "is_zero",
            term![Op::Ite; eqz, self.one.0.clone(), self.zero.0.clone()],
        );
        self.constraint(m.1, x.1.clone(), -is_zero.1.clone() + 1);
        self.constraint(is_zero.1.clone(), x.1, self.r1cs.zero());
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
                    &format!("{d}_b{i}"),
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
            let sum = xs.fold(self.zero.clone(), |s, i| s + &i);
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
    fn mul(&mut self, mut a: TermLc, mut b: TermLc) -> TermLc {
        if b.1.as_const().is_some() {
            std::mem::swap(&mut a, &mut b);
        }
        let mul_val = term![PF_MUL; a.0, b.0];
        if let Some(c) = a.1.as_const() {
            let lc = b.1 * c;
            TermLc(mul_val, lc)
        } else {
            let c = self.fresh_wit("mul", mul_val);
            self.constraint(a.1, b.1, c.1.clone());
            c
        }
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

    /// Embed this variable as
    fn embed_var(&mut self, var: &Term, ty: VarType) {
        assert!(
            !self.cache.contains_key(var),
            "already have var {}",
            var.op()
        );
        assert!(!matches!(ty, VarType::CWit), "Unimplemented");
        if !self.used_vars.contains(var.as_var_name()) {
            return;
        }
        debug!("Embed var: {}", var.op());
        self.profile_start_term(var.clone());
        let public = matches!(ty, VarType::Inst);
        match var.op() {
            Op::Var(name, Sort::Bool) => {
                let comp = term![Op::Ite; var.clone(), self.one.0.clone(), self.zero.0.clone()];
                let lc = self.fresh_var(name, comp, ty);
                if !public {
                    self.enforce_bit(lc.clone());
                }
                self.cache.insert(var.clone(), EmbeddedTerm::Bool(lc));
                self.embed.borrow_mut().insert(var.clone());
            }
            Op::Var(name, Sort::BitVector(n_bits)) => {
                let public = matches!(ty, VarType::Inst);
                let lc = self.fresh_var(
                    name,
                    term![Op::UbvToPf(self.field.clone()); var.clone()],
                    ty,
                );
                self.set_bv_uint(var.clone(), lc, *n_bits);
                if !public {
                    self.get_bv_bits(var);
                }
            }
            Op::Var(name, Sort::Field(f)) => {
                assert_eq!(f, &self.field);
                let lc = self.fresh_var(name, var.clone(), ty);
                self.cache.insert(var.clone(), EmbeddedTerm::Field(lc));
                self.embed.borrow_mut().insert(var.clone());
            }
            o => unreachable!("Unhandled variable operator {}", o),
        }
        self.profile_end_term();
    }

    fn embed(&mut self, t: Term) {
        debug!("Embed: {}", t);
        let visited_set_rc = self.embed.clone();
        for c in
            extras::PostOrderSkipIter::new(t, &move |s: &Term| visited_set_rc.borrow().contains(s))
        {
            assert!(!self.embed.borrow().contains(&c));
            debug!("Embed op: {}", c.op());
            // Handle field access once and for all
            if let Op::Field(i) = &c.op() {
                // Need to borrow self in between search and insert. Could refactor.
                #[allow(clippy::map_entry)]
                if !self.cache.contains_key(&c) {
                    let t = self.get_field(&c.cs()[0], *i);
                    self.embed.borrow_mut().insert(c.clone());
                    self.cache.insert(c, t);
                }
            } else {
                self.profile_start_term(c.clone());
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
                self.profile_end_term();
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
            let lc = match &c.op() {
                Op::Var(..) => panic!("call embed_var instead"),
                Op::Const(Value::Bool(b)) => self.zero.clone() + *b as isize,
                Op::Eq => self.embed_eq(&c.cs()[0], &c.cs()[1]),
                Op::Ite => {
                    let a = self.get_bool(&c.cs()[0]).clone();
                    let b = self.get_bool(&c.cs()[1]).clone();
                    let c = self.get_bool(&c.cs()[2]).clone();
                    self.ite(a, b, &c)
                }
                Op::BoolMaj => {
                    let a = self.get_bool(&c.cs()[0]).clone();
                    let b = self.get_bool(&c.cs()[1]).clone();
                    let c = self.get_bool(&c.cs()[2]).clone();
                    // m = ab + bc + ca - 2abc
                    // m = ab + c(b + a - 2ab)
                    //   where i = ab
                    // m = i + c(b + a - 2i)
                    let i = self.mul(a.clone(), b.clone());
                    self.mul(c, b + &a - &(i.clone() * 2)) + &i
                }
                Op::Not => {
                    let a = self.get_bool(&c.cs()[0]);
                    self.bool_not(a)
                }
                Op::Implies => {
                    let a = self.get_bool(&c.cs()[0]).clone();
                    let b = self.get_bool(&c.cs()[1]).clone();
                    let not_a = self.bool_not(&a);
                    self.nary_or(vec![not_a, b].into_iter())
                }
                Op::BoolNaryOp(o) => {
                    let args = c
                        .cs()
                        .iter()
                        .map(|c| self.get_bool(c).clone())
                        .collect::<Vec<_>>();
                    match o {
                        BoolNaryOp::Or => self.nary_or(args.into_iter()),
                        BoolNaryOp::And => self.nary_and(args.into_iter()),
                        BoolNaryOp::Xor => self.nary_xor(args.into_iter()),
                    }
                }
                Op::BvBit(i) => {
                    let a = self.get_bv_bits(&c.cs()[0]);
                    a[*i].clone()
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
                Op::PfToBoolTrusted => {
                    // we trust that this is zero or one
                    self.get_pf(&c.cs()[0]).clone()
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
        if t.op() == &Op::Eq {
            t.cs().iter().for_each(|c| self.embed(c.clone()));
            self.profile_start_term(t.clone());
            self.assert_eq(&t.cs()[0], &t.cs()[1]);
            self.profile_end_term();
        } else if t.op() == &AND {
            for c in t.cs() {
                self.assert_bool(c);
            }
        } else if let Op::PfFitsInBits(n) = t.op() {
            self.embed(term![Op::PfToBv(*n); t.cs()[0].clone()]);
        } else {
            self.embed(t.clone());
            let lc = self.get_bool(t).clone();
            self.profile_start_term(t.clone());
            self.assert_zero(lc - 1);
            self.profile_end_term();
        }
    }

    /// Given a and b such that -2^n < a - b < 2^n, returns whether a >= b (or a > b if `strict` is
    /// set).
    fn bv_greater(&mut self, a: TermLc, b: TermLc, n: usize, strict: bool) -> TermLc {
        let tweak = if strict { -1 } else { 0 };
        let shift = self.r1cs.modulus.new_v(Integer::from(1) << n);
        let sum = a - &b + &shift + tweak;
        // unwrap does not panic because the length is n + 1
        self.bitify("cmp", &sum, n + 1, false).pop().unwrap()
    }

    /// Returns whether `a` is (`strict`ly) (`signed`ly) greater than `b`.
    /// Assumes they are each `w`-bit bit-vectors.
    fn bv_cmp(&mut self, w: usize, signed: bool, strict: bool, a: &Term, b: &Term) -> TermLc {
        if w + 2 < self.field.modulus().significant_bits() as usize {
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
            self.bv_greater(a, b, w, strict)
        } else {
            assert!(
                !signed,
                "Cannot perform signed comparisons on huge bit-vectors"
            );
            let a_bits = self.get_bv_bits(a);
            let b_bits = self.get_bv_bits(b);
            self.bv_bitwise_greater(a_bits, b_bits, strict)
        }
    }

    /// Treating `xs` and `ys` as unsigned bit-vectors (with LSB at index 0), emit a bit-wise
    /// comparison circuit.
    ///
    /// Useful for comparisons over very large bit-vectors.
    fn bv_bitwise_greater(&mut self, xs: Vec<TermLc>, ys: Vec<TermLc>, strict: bool) -> TermLc {
        let mut acc = self.zero.clone() + (!strict) as isize;
        for (x, y) in xs.into_iter().zip(ys) {
            let eq = self.bits_are_equal(&x, &y);
            let eq_and_acc = self.nary_and(vec![eq, acc].into_iter());
            let not_y = self.bool_not(&y);
            let x_gt_y = self.nary_and(vec![x, not_y].into_iter());
            acc = self.nary_or(vec![x_gt_y, eq_and_acc].into_iter());
        }
        acc
    }

    /// Shift `x` left by `2^y`, if bit-valued `c` is true.
    fn const_pow_shift_bv_lit(&mut self, x: &TermLc, y: usize, c: TermLc) -> TermLc {
        self.ite(c, x.clone() * (1 << (1 << y)), x)
    }

    /// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
    /// Returns an *oversized* number
    fn shift_bv_lit(&mut self, x: TermLc, y: Vec<TermLc>, ext_bit: Option<TermLc>) -> TermLc {
        if let Some(b) = ext_bit {
            let left = self.shift_bv_lit(x, y.clone(), None);
            let right = self.shift_bv_lit(b.clone(), y, None) - 1;
            left + &self.mul(b, right)
        } else {
            y.into_iter()
                .enumerate()
                .fold(x, |x, (i, yi)| self.const_pow_shift_bv_lit(&x, i, yi))
        }
    }

    /// Shift `x` left by `y`, filling the blank spots with bit-valued `ext_bit`.
    /// Returns a bit sequence.
    ///
    /// If `c` is true, returns bit sequence which is just a copy of `ext_bit`.
    fn shift_bv_bits(
        &mut self,
        x: TermLc,
        y: Vec<TermLc>,
        ext_bit: Option<TermLc>,
        x_w: usize,
        c: TermLc,
    ) -> Vec<TermLc> {
        let y_w = y.len();
        let mask: TermLc = match ext_bit.as_ref() {
            Some(e) => e.clone() * &self.r1cs.modulus.new_v((1 << x_w) - 1),
            None => self.zero.clone(),
        };
        let s = self.shift_bv_lit(x, y, ext_bit);
        let masked_s = self.ite(c, mask, &s);
        let mut bits = self.bitify("shift", &masked_s, (1 << y_w) + x_w - 1, false);
        bits.truncate(x_w);
        bits
    }

    /// Given a shift amount expressed as a bit-sequence, splits that shift into low bits and high
    /// bits. The number of low bits, `b`, is the minimum amount such that `data_w-1` is representable
    /// in `b` bits. The rest of the bits (the high ones) are or'd together into a single bit that is
    /// returned.
    fn split_shift_amt(
        &mut self,
        data_w: usize,
        mut shift_amt: Vec<TermLc>,
    ) -> (TermLc, Vec<TermLc>) {
        let b = bitsize(data_w - 1);
        let some_high_bit = self.nary_or(shift_amt.drain(b..));
        (some_high_bit, shift_amt)
    }

    fn embed_bv(&mut self, bv: Term) {
        //println!("Embed: {}", bv);
        //let bv2=  bv.clone();
        if let Sort::BitVector(n) = check(&bv) {
            if !self.cache.contains_key(&bv) {
                match &bv.op() {
                    Op::Var(..) => panic!("call embed_var instead"),
                    Op::Const(Value::BitVector(b)) => {
                        let bit_lcs = (0..b.width())
                            .map(|i| self.zero.clone() + b.uint().get_bit(i as u32) as isize)
                            .collect();
                        self.set_bv_bits(bv, bit_lcs);
                    }
                    Op::Ite => {
                        let c = self.get_bool(&bv.cs()[0]).clone();
                        let t = self.get_bv_uint(&bv.cs()[1]);
                        let f = self.get_bv_uint(&bv.cs()[2]);
                        let ite = self.ite(c, t, &f);
                        self.set_bv_uint(bv, ite, n);
                    }
                    Op::BvUnOp(BvUnOp::Not) => {
                        let bits = self.get_bv_bits(&bv.cs()[0]);
                        let not_bits = bits.iter().map(|bit| self.bool_not(bit)).collect();
                        self.set_bv_bits(bv, not_bits);
                    }
                    Op::BvUnOp(BvUnOp::Neg) => {
                        let x = self.get_bv_uint(&bv.cs()[0]);
                        // Wrong for x == 0
                        let almost_neg_x = self.zero.clone()
                            + &self.r1cs.modulus.new_v(Integer::from(2).pow(n as u32))
                            - &x;
                        let is_zero = self.is_zero(x);
                        let neg_x = self.ite(is_zero, self.zero.clone(), &almost_neg_x);
                        self.set_bv_uint(bv, neg_x, n);
                    }
                    Op::BvUext(extra_n) => {
                        if self.bv_has_bits(&bv.cs()[0]) {
                            let bits = self.get_bv_bits(&bv.cs()[0]);
                            let ext_bits = std::iter::repeat(self.zero.clone()).take(*extra_n);
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
                    Op::PfToBv(nbits) => {
                        let lc = self.get_pf(&bv.cs()[0]).clone();
                        let bits = self.bitify("pf2bv", &lc, *nbits, false);
                        self.set_bv_bits(bv.clone(), bits);
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
                                .cs()
                                .iter()
                                .map(|c| self.get_bv_uint(c))
                                .collect::<Vec<_>>();
                            let (res, width) = match o {
                                BvNaryOp::Add => {
                                    let sum =
                                        values.into_iter().fold(self.zero.clone(), |s, v| s + &v);
                                    let extra_width = bitsize(bv.cs().len().saturating_sub(1));
                                    (sum, n + extra_width)
                                }
                                BvNaryOp::Mul => {
                                    if bv.cs().len() * n < f_width {
                                        let z = self.zero.clone() + 1;
                                        (
                                            values.into_iter().fold(z, |acc, v| self.mul(acc, v)),
                                            bv.cs().len() * n,
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
                        let a = self.get_bv_uint(&bv.cs()[0]);
                        let b = self.get_bv_uint(&bv.cs()[1]);
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
                                let a_bv_term = term![Op::PfToBv(n); a.0.clone()];
                                let b_bv_term = term![Op::PfToBv(n); b.0.clone()];
                                let q_term = term![Op::UbvToPf(self.field.clone()); term![BV_UDIV; a_bv_term.clone(), b_bv_term.clone()]];
                                let r_term = term![Op::UbvToPf(self.field.clone()); term![BV_UREM; a_bv_term, b_bv_term]];
                                let q = self.fresh_wit("div_q", q_term);
                                let r = self.fresh_wit("div_r", r_term);
                                let qb = self.bitify("div_q", &q, n, false);
                                let rb = self.bitify("div_r", &r, n, false);
                                self.constraint(q.1.clone(), b.1.clone(), (a - &r).1);
                                // b == 0 -> q == M   //  b != 0 or q == M
                                // b != 0 -> r < b    //  b == 0 or r < b
                                // so, since we don't care about b == 0,
                                // q == M or r < b
                                // not(q != M and r >= b)
                                let r_ge_b = self.bv_greater(r, b, n, false);
                                let max = self.r1cs.modulus.new_v((Integer::from(1) << n) - 1);
                                let q_eq_max = self.is_zero(q - &max);
                                let q_ne_max = self.bool_not(&q_eq_max);
                                self.constraint(r_ge_b.1, q_ne_max.1, self.r1cs.zero());
                                let bits = match o {
                                    BvBinOp::Udiv => qb,
                                    BvBinOp::Urem => rb,
                                    _ => unreachable!(),
                                };
                                self.set_bv_bits(bv, bits);
                            }
                            // Shift cases
                            _ => {
                                let rb = self.get_bv_bits(&bv.cs()[1]);
                                let (high, low) = self.split_shift_amt(n, rb);
                                let bits = match o {
                                    BvBinOp::Shl => self.shift_bv_bits(a, low, None, n, high),
                                    BvBinOp::Lshr | BvBinOp::Ashr => {
                                        let mut lb = self.get_bv_bits(&bv.cs()[0]);
                                        lb.reverse();
                                        let ext_bit = match o {
                                            BvBinOp::Ashr => Some(lb.first().unwrap().clone()),
                                            _ => None,
                                        };
                                        let l = self.debitify(lb.into_iter(), false);
                                        let mut bits = self.shift_bv_bits(l, low, ext_bit, n, high);
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
                        for c in bv.cs().iter().rev() {
                            bits.extend(self.get_bv_bits(c));
                        }
                        self.set_bv_bits(bv, bits);
                    }
                    // inclusive!
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
        assert!(!self.cache.contains_key(&t));
        self.cache.insert(
            t,
            EmbeddedTerm::Bv(Rc::new(RefCell::new(BvEntry {
                uint: None,
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
                uint: Some(uint),
                width,
                bits: Vec::new(),
            }))),
        );
    }

    fn get_bv_lit(&self, t: &Term) -> Rc<RefCell<BvEntry>> {
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
        !(*self.get_bv_lit(t)).borrow().bits.is_empty()
    }

    fn get_bv_uint(&mut self, t: &Term) -> TermLc {
        let entry_rc = self.get_bv_lit(t);
        let mut entry = entry_rc.borrow_mut();
        if let Some(uint) = entry.uint.as_ref() {
            uint.clone()
        } else {
            let uint = self.debitify(entry.bits.clone().into_iter(), false);
            entry.uint = Some(uint.clone());
            uint
        }
    }

    fn get_bv_signed_int(&mut self, t: &Term) -> TermLc {
        let bits = self.get_bv_bits(t);
        self.debitify(bits.into_iter(), true)
    }

    fn get_bv_bits(&mut self, t: &Term) -> Vec<TermLc> {
        let entry_rc = self.get_bv_lit(t);
        let mut entry = entry_rc.borrow_mut();
        if entry.bits.is_empty() {
            entry.bits = self.bitify("getbits", entry.uint.as_ref().unwrap(), entry.width, false);
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
        //println!("Embed: {}", c);
        // TODO: skip if already embedded
        if !self.cache.contains_key(&c) {
            debug!("embed_pf {}", c);
            let lc = match &c.op() {
                Op::Var(..) => panic!("call embed_var instead"),
                Op::Const(Value::Field(r)) => TermLc(
                    c.clone(),
                    self.r1cs.constant(r.as_ty_ref(&self.r1cs.modulus)),
                ),
                Op::Ite => {
                    let cond = self.get_bool(&c.cs()[0]).clone();
                    let t = self.get_pf(&c.cs()[1]).clone();
                    let f = self.get_pf(&c.cs()[2]).clone();
                    self.ite(cond, t, &f)
                }
                Op::PfNaryOp(o) => {
                    let args = c.cs().iter().map(|c| self.get_pf(c));
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
                Op::UbvToPf(_) => self.get_bv_uint(&c.cs()[0]),
                Op::PfUnOp(PfUnOp::Neg) => -self.get_pf(&c.cs()[0]).clone(),
                Op::PfUnOp(PfUnOp::Recip) => match self.cfg.r1cs.div_by_zero {
                    FieldDivByZero::Incomplete => {
                        // ix = 1
                        let x = self.get_pf(&c.cs()[0]).clone();
                        let inv_x = self.fresh_wit("recip", term![PF_RECIP; x.0.clone()]);
                        self.constraint(x.1, inv_x.1.clone(), self.r1cs.zero() + 1);
                        inv_x
                    }
                    FieldDivByZero::NonDet => {
                        // ixx = x
                        let x = self.get_pf(&c.cs()[0]).clone();
                        let x2 = self.mul(x.clone(), x.clone());
                        let inv_x = self.fresh_wit("recip", term![PF_RECIP; x.0.clone()]);
                        self.constraint(x2.1, inv_x.1.clone(), x.1);
                        inv_x
                    }
                    FieldDivByZero::Zero => {
                        // ix = 1 - z
                        // zx = 0
                        // zi = 0
                        let x = self.get_pf(&c.cs()[0]).clone();
                        let eqz = term![Op::Eq; x.0.clone(), self.zero.0.clone()];
                        let i = self.fresh_wit(
                            "is_zero_inv",
                            term![Op::Ite; eqz.clone(), self.zero.0.clone(), term![PF_RECIP; x.0.clone()]],
                        );
                        let z = self.fresh_wit(
                            "is_zero",
                            term![Op::Ite; eqz, self.one.0.clone(), self.zero.0.clone()],
                        );
                        self.constraint(i.1.clone(), x.1.clone(), -z.1.clone() + 1);
                        self.constraint(z.1.clone(), x.1, self.r1cs.zero());
                        self.constraint(z.1, i.1.clone(), self.r1cs.zero());
                        i
                    }
                },
                Op::PfDiv => match self.cfg.r1cs.div_by_zero {
                    FieldDivByZero::Incomplete => {
                        // ix = y
                        let y = self.get_pf(&c.cs()[0]).clone();
                        let x = self.get_pf(&c.cs()[1]).clone();
                        let div = self.fresh_wit("div", term![PF_DIV; y.0.clone(), x.0.clone()]);
                        self.constraint(x.1, div.1.clone(), y.1);
                        div
                    }
                    _ => unimplemented!(),
                },
                _ => panic!("Non-field in embed_pf: {}", c),
            };
            self.cache.insert(c.clone(), EmbeddedTerm::Field(lc));
        }
        self.get_pf(&c)
    }

    fn assert_zero(&mut self, x: TermLc) {
        self.constraint(self.r1cs.zero(), self.r1cs.zero(), x.1);
    }
    fn assert(&mut self, t: Term) {
        debug!("Assert: {}", t);
        debug_assert!(check(&t) == Sort::Bool, "Non bool in assert");
        self.assert_bool(&t);
    }
}

/// Convert this (IR) constraint system `cs` to R1CS, over a prime field defined by `modulus`.
///
/// ## Returns
///
/// * Prover data (including the R1CS instance)
/// * Verifier data
pub fn to_r1cs(cs: &Computation, cfg: &CircCfg) -> R1cs {
    let public_inputs = cs.metadata.public_input_names_set();
    debug!("public inputs: {:?}", public_inputs);
    let used_vars = extras::free_variables(term(Op::Tuple, cs.outputs.clone()));
    let mut converter = ToR1cs::new(cfg, cs.precomputes.clone(), used_vars);
    debug!(
        "Term count: {}",
        cs.outputs
            .iter()
            .map(|c| PostOrderIter::new(c.clone()).count())
            .sum::<usize>()
    );
    debug!("declaring inputs");
    let vars = cs.metadata.interactive_vars();
    trace!("interactive_vars: {:#?}", vars);
    for i in &vars.instances {
        converter.embed_var(i, VarType::Inst);
    }
    for terms in &vars.committed_wit_vecs {
        let names_and_terms = terms
            .iter()
            .map(|t| (t.as_var_name().to_owned(), t.clone()))
            .collect();
        converter.committed_wit(names_and_terms);
    }
    for round in &vars.rounds {
        for w in &round.witnesses {
            converter.embed_var(w, VarType::RoundWit);
        }
        for c in &round.challenges {
            converter.embed_var(c, VarType::Chall);
        }
        converter.r1cs.end_round()
    }
    for w in &vars.final_witnesses {
        converter.embed_var(w, VarType::FinalWit);
    }
    debug!("Printing assertions");
    for c in &cs.outputs {
        converter.assert(c.clone());
    }
    converter.profile_print();
    converter.r1cs
}

#[cfg(test)]
pub mod test {
    use super::*;

    use crate::ir::proof::Constraints;
    use crate::ir::term::dist::test::*;
    use crate::target::r1cs::opt::reduce_linearities;

    use fxhash::FxHashMap;
    use quickcheck_macros::quickcheck;

    fn to_r1cs_dflt(cs: Computation) -> R1cs {
        to_r1cs(&cs, &CircCfg::default())
    }

    fn to_r1cs_mod17(cs: Computation) -> R1cs {
        let mut opt = crate::cfg::CircOpt::default();
        opt.field.custom_modulus = "17".into();
        to_r1cs(&cs, &CircCfg::from(opt))
    }

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
        let r1cs = to_r1cs_mod17(cs);
        r1cs.check_all(&values);
    }

    #[quickcheck]
    fn random_pure_bool(PureBool(t, values): PureBool) {
        let t = if eval(&t, &values).as_bool() {
            t
        } else {
            term![Op::Not; t]
        };
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let r1cs = to_r1cs_dflt(cs);
        r1cs.check_all(&values);
    }

    #[quickcheck]
    fn random_bool(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let cfg = CircCfg::default();
        let r1cs = to_r1cs(&cs, &cfg);
        r1cs.check_all(&values);
    }

    #[quickcheck]
    fn random_pure_bool_opt(ArbitraryBoolEnv(t, values): ArbitraryBoolEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        let cfg = CircCfg::default();
        let r1cs = to_r1cs(&cs, &cfg);
        r1cs.check_all(&values);
        let r1cs2 = reduce_linearities(r1cs, &cfg);
        r1cs2.check_all(&values);
    }

    #[quickcheck]
    fn random_bool_opt(ArbitraryTermEnv(t, values): ArbitraryTermEnv) {
        let v = eval(&t, &values);
        let t = term![Op::Eq; t, leaf_term(Op::Const(v))];
        let mut cs = Computation::from_constraint_system_parts(vec![t], Vec::new());
        crate::ir::opt::scalarize_vars::scalarize_inputs(&mut cs);
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let cfg = CircCfg::default();
        let r1cs = to_r1cs(&cs, &cfg);
        r1cs.check_all(&values);
        let r1cs2 = reduce_linearities(r1cs, &cfg);
        r1cs2.check_all(&values);
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
            vec![term![Op::Not; term![Op::Eq; bv_lit(0b10110, 8),
                              term![Op::BvUnOp(BvUnOp::Neg); leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))]]]],
            vec![leaf_term(Op::Var("b".to_owned(), Sort::BitVector(8)))],
        );
        let r1cs = to_r1cs_dflt(cs);
        r1cs.check_all(&values);
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
        let cfg = CircCfg::default();
        let r1cs = to_r1cs(&cs, &cfg);
        r1cs.check_all(&values);
        let r1cs2 = reduce_linearities(r1cs, &cfg);
        r1cs2.check_all(&values);
    }

    fn pf_dflt(i: isize) -> Term {
        leaf_term(Op::Const(Value::Field(CircCfg::default().field().new_v(i))))
    }

    fn const_test(term: Term) {
        let mut cs = Computation::new();
        cs.assert(term);
        let r1cs = to_r1cs_dflt(cs);
        r1cs.check_all(&Default::default());
    }

    #[test]
    fn div_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv_lit(0b1111,4), bv_lit(0b0001,4)],
            bv_lit(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv_lit(0b0111,4), bv_lit(0b0000,4)],
            bv_lit(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Udiv); bv_lit(0b1111,4), bv_lit(0b0010,4)],
            bv_lit(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv_lit(0b1111,4), bv_lit(0b1111,4)],
            bv_lit(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv_lit(0b1111,4), bv_lit(0b0001,4)],
            bv_lit(0b0000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv_lit(0b0111,4), bv_lit(0b0000,4)],
            bv_lit(0b0111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Urem); bv_lit(0b1111,4), bv_lit(0b0010,4)],
            bv_lit(0b0001, 4)
        ]);
    }

    #[test]
    fn sh_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv_lit(0b1111,4), bv_lit(0b0011,4)],
            bv_lit(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Shl); bv_lit(0b1101,4), bv_lit(0b0010,4)],
            bv_lit(0b0100, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv_lit(0b1111,4), bv_lit(0b0011,4)],
            bv_lit(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Ashr); bv_lit(0b0111,4), bv_lit(0b0010,4)],
            bv_lit(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv_lit(0b0111,4), bv_lit(0b0010,4)],
            bv_lit(0b0001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::BvBinOp(BvBinOp::Lshr); bv_lit(0b1111,4), bv_lit(0b0011,4)],
            bv_lit(0b0001, 4)
        ]);
    }

    #[test]
    fn pf2bv_lit() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf_dflt(8)],
            bv_lit(0b1000, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(4); pf_dflt(15)],
            bv_lit(0b1111, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![Op::PfToBv(8); pf_dflt(15)],
            bv_lit(0b1111, 8)
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
        let r1cs = to_r1cs_mod17(cs);
        r1cs.check_all(&values);
    }

    #[test]
    fn pf_fits_in_bits() {
        let mut cs = text::parse_computation(
            b"
            (computation
                (metadata (parties P) (inputs (a (mod 17)) (b (mod 17)) (c (mod 17))) (commitments))
                (precompute () () (#t ))
                (and
                    ((pf_fits_in_bits 1) a)
                    ((pf_fits_in_bits 2) (+ b c))
                    (= (+ b c) (+ c b))
                    ((pf_fits_in_bits 2) #f1m17)
                )
            )
        ",
        );
        let values = text::parse_value_map(
            b"(let(
            (a #f1m17)
            (b #f4m17)
            (c #f-1m17)
            ) false; ignored
            )",
        );
        crate::ir::opt::tuple::eliminate_tuples(&mut cs);
        let r1cs = to_r1cs_mod17(cs);
        r1cs.check_all(&values);
    }

    fn add_test_instance(args: &[u64], res: u64, bits: usize) {
        let sum: u64 = args.iter().sum::<u64>() & ((1 << bits) - 1);
        assert_eq!(sum, res);
        const_test(
            term![Op::Eq; term(BV_ADD, args.iter().map(|a| bv_lit(*a, bits)).collect()), bv_lit(res, bits)],
        );
    }

    #[test]
    fn add_test() {
        init();
        add_test_instance(&[0b0, 0b0, 0b0, 0b0], 0b0, 1);
        add_test_instance(&[0b1, 0b0, 0b0, 0b0], 0b1, 1);
        add_test_instance(&[0b1, 0b1, 0b1, 0b0], 0b1, 1);
        add_test_instance(&[0b1, 0b1, 0b1, 0b1], 0b0, 1);
        add_test_instance(&[0b11, 0b11, 0b11, 0b11], 0b00, 2);
        add_test_instance(&[0b11, 0b11, 0b11, 0b11, 0b11], 0b11, 2);
    }

    #[test]
    fn concat_test() {
        init();
        const_test(term![
            Op::Eq;
            term![BV_CONCAT; bv_lit(0b10,2), bv_lit(0b01,2)],
            bv_lit(0b1001, 4)
        ]);
        const_test(term![
            Op::Eq;
            term![BV_CONCAT; bv_lit(0b11,2), bv_lit(0b01,2)],
            bv_lit(0b1101, 4)
        ]);
    }

    #[test]
    fn maj_test() {
        init();
        const_test(term![
            Op::Eq;
            term![Op::BoolMaj; bool_lit(true), bool_lit(true), bool_lit(true)],
            bool_lit(true)
        ]);
    }
}
