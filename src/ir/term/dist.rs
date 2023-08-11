//! Distributions over terms (useful for fuzz testing)

use super::*;

use circ_fields::{FieldT, FieldV};
use rand::{distributions::Distribution, prelude::SliceRandom, Rng};
use std::iter::repeat;

// A distribution of boolean terms with some size.
// All subterms are booleans.
pub(crate) struct PureBoolDist(pub usize);

// A distribution of n usizes that sum to this value.
// (n, sum)
pub(crate) struct Sum(usize, usize);
impl rand::distributions::Distribution<Vec<usize>> for Sum {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Vec<usize> {
        let mut acc = self.1;
        let mut ns = Vec::new();
        assert!(acc == 0 || self.0 > 0);
        while acc > 0 && ns.len() < self.0 {
            let x = rng.gen_range(0..acc);
            acc -= x;
            ns.push(x);
        }
        while ns.len() < self.0 {
            ns.push(0);
        }
        if acc > 0 {
            *ns.last_mut().unwrap() += acc;
        }
        ns.shuffle(rng);
        ns
    }
}

impl rand::distributions::Distribution<Term> for PureBoolDist {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Term {
        let ops = &[
            Op::Const(Value::Bool(rng.gen())),
            Op::Var(
                std::str::from_utf8(&[b'a' + rng.gen_range(0..26)])
                    .unwrap()
                    .to_owned(),
                Sort::Bool,
            ),
            Op::Not,
            Op::Implies,
            Op::BoolNaryOp(BoolNaryOp::Or),
            Op::BoolNaryOp(BoolNaryOp::And),
            Op::BoolNaryOp(BoolNaryOp::Xor),
        ];
        let o = match self.0 {
            1 => ops[..2].choose(rng),  // arity 0
            2 => ops[2..3].choose(rng), // arity 1
            _ => ops[2..].choose(rng),  // others
        }
        .unwrap()
        .clone();
        // Now, self.0 is a least arity+1
        let a = o.arity().unwrap_or_else(|| rng.gen_range(2..self.0));
        let excess = self.0.saturating_sub(1 + a);
        let ns = Sum(a, excess).sample(rng);
        let subterms = ns
            .into_iter()
            .map(|n| PureBoolDist(n + 1).sample(rng))
            .collect::<Vec<_>>();
        term(o, subterms)
    }
}

#[derive(Clone)]
pub(crate) struct FixedSizeDist {
    pub size: usize,
    pub bv_width: Option<usize>,
    pub pf_t: Option<FieldT>,
    pub tuples: bool,
    pub sort: Sort,
}

impl FixedSizeDist {
    fn with_size(mut self, size: usize) -> Self {
        self.size = size;
        self
    }
    fn with_sort(mut self, sort: Sort) -> Self {
        self.sort = sort;
        self
    }
    fn sample_ident<R: Rng + ?Sized>(&self, prefix: &str, rng: &mut R) -> String {
        format!("{}_{}", prefix, (b'a' + rng.gen_range(0..26)) as char)
    }
    fn sample_value<R: Rng + ?Sized>(&self, sort: &Sort, rng: &mut R) -> Op {
        Op::Const(UniformValue(sort).sample(rng))
    }
    fn sample_op<R: Rng + ?Sized>(&self, sort: &Sort, rng: &mut R) -> Op {
        let mut ops = match sort {
            Sort::Bool => {
                let mut ops = vec![
                    self.sample_value(sort, rng),
                    Op::Var(self.sample_ident("b_", rng), sort.clone()),
                    Op::Not, // 2
                    Op::Implies,
                    Op::Eq,
                    Op::BoolNaryOp(BoolNaryOp::Or),
                    Op::BoolNaryOp(BoolNaryOp::And),
                    Op::BoolNaryOp(BoolNaryOp::Xor),
                ];
                if self.bv_width.is_some() {
                    ops.push(Op::BvBinPred(BvBinPred::Sge));
                    ops.push(Op::BvBinPred(BvBinPred::Sgt));
                    ops.push(Op::BvBinPred(BvBinPred::Sle));
                    ops.push(Op::BvBinPred(BvBinPred::Slt));
                    ops.push(Op::BvBinPred(BvBinPred::Uge));
                    ops.push(Op::BvBinPred(BvBinPred::Ugt));
                    ops.push(Op::BvBinPred(BvBinPred::Ule));
                    ops.push(Op::BvBinPred(BvBinPred::Ult));
                }
                ops
            }
            Sort::BitVector(w) => vec![
                self.sample_value(sort, rng),
                Op::Var(self.sample_ident(&format!("bv{w}"), rng), sort.clone()),
                Op::BvUnOp(BvUnOp::Neg),
                Op::BvUnOp(BvUnOp::Not),
                Op::BvUext(rng.gen_range(0..*w)),
                Op::BvSext(rng.gen_range(0..*w)),
                Op::BvBinOp(BvBinOp::Sub),
                Op::BvBinOp(BvBinOp::Udiv),
                Op::BvBinOp(BvBinOp::Urem),
                Op::BvNaryOp(BvNaryOp::Or),
                Op::BvNaryOp(BvNaryOp::And),
                Op::BvNaryOp(BvNaryOp::Xor),
                Op::BvNaryOp(BvNaryOp::Add),
                Op::BvNaryOp(BvNaryOp::Mul),
            ],
            Sort::Field(_) => {
                vec![
                    self.sample_value(sort, rng),
                    Op::Var(self.sample_ident("pf", rng), sort.clone()),
                    Op::PfUnOp(PfUnOp::Neg),
                    // Can error
                    // Op::PfUnOp(PfUnOp::Recip),
                    Op::PfNaryOp(PfNaryOp::Add),
                    Op::PfNaryOp(PfNaryOp::Mul),
                ]
            }
            Sort::Tuple(_) => {
                vec![
                    Op::Tuple,
                    self.sample_value(sort, rng),
                    // No variables!
                    Op::Var(
                        self.sample_ident(
                            &format!("tp_{sort}")
                                .replace('(', "[")
                                .replace(')', "]")
                                .replace(' ', "_"),
                            rng,
                        ),
                        sort.clone(),
                    ),
                ]
            }
            s => panic!("Unsampleable sort: {}", s),
        };
        ops.push(Op::Ite);
        if self.tuples && self.size > 1 {
            ops.push(Op::Field(rng.gen_range(0..(self.size - 1))));
        }
        ops.retain(|o| o.arity().map(|a| a < self.size).unwrap_or(self.size > 2));
        // always Some b/c variables & constants have 0 arity
        ops.choose(rng).cloned().unwrap()
    }
    fn sample_child_sorts<R: Rng + ?Sized>(&self, sort: &Sort, op: &Op, rng: &mut R) -> Vec<Sort> {
        match op {
            Op::Ite => vec![Sort::Bool, sort.clone(), sort.clone()],
            o if o.arity() == Some(0) => vec![],
            Op::Field(i) => vec![if let Sort::Tuple(mut ss) =
                self.sample_tuple_sort(*i + 1, self.size - 1, rng)
            {
                ss[*i] = sort.clone();
                Sort::Tuple(ss)
            } else {
                unreachable!()
            }],
            Op::Tuple => {
                if let Sort::Tuple(sorts) = sort {
                    sorts.to_vec()
                } else {
                    unreachable!("Bad sort for tuple cons: {}", sort)
                }
            }
            Op::Eq => {
                let mut sort_choices = vec![Sort::Bool];
                if self.tuples && self.size > 2 {
                    sort_choices.push(self.sample_tuple_sort(1, self.size - 1, rng));
                }
                if let Some(w) = &self.bv_width {
                    sort_choices.push(Sort::BitVector(*w));
                }
                if let Some(m) = &self.pf_t {
                    sort_choices.push(Sort::Field(m.clone()));
                }
                let s = sort_choices.choose(rng).unwrap();
                vec![s.clone(), s.clone()]
            }
            Op::BvBinPred(_) => {
                let s = Sort::BitVector(self.bv_width.unwrap());
                vec![s.clone(), s]
            }
            o if o.arity().is_none() && o != &Op::BvConcat => repeat(sort.clone())
                .take(rng.gen_range(1..self.size))
                .collect(),
            // perhaps allow concat?
            Op::BvBinOp(_) => vec![sort.clone(), sort.clone()],
            Op::BvUnOp(_) => vec![sort.clone()],
            Op::BvUext(ww) => vec![Sort::BitVector(sort.as_bv() - ww)],
            Op::BvSext(ww) => vec![Sort::BitVector(sort.as_bv() - ww)],
            Op::Not => vec![Sort::Bool],
            Op::Implies => vec![Sort::Bool, Sort::Bool],
            Op::PfUnOp(_) => vec![sort.clone()],
            _ => panic!("Cannot generate child sorts for {} yielding {}", op, sort),
        }
    }
    fn sample_tuple_sort<R: Rng + ?Sized>(
        &self,
        min_size: usize,
        max_size: usize,
        rng: &mut R,
    ) -> Sort {
        assert!(self.tuples);
        assert!(min_size <= max_size);
        let n = rng.gen_range(min_size..=max_size);
        let excess = max_size.saturating_sub(n);
        let parts = Sum(n, excess).sample(rng);
        Sort::Tuple(
            parts
                .into_iter()
                .map(|i| self.clone().sample_sort(rng, i + 1))
                .collect(),
        )
    }
    fn sample_sort<R: Rng + ?Sized>(&self, rng: &mut R, max_size: usize) -> Sort {
        match rng.gen_range(0..=3) {
            0 if self.bv_width.is_some() => Sort::BitVector(self.bv_width.unwrap()),
            1 if self.pf_t.is_some() => Sort::Field(self.pf_t.clone().unwrap()),
            2 if self.tuples && max_size > 1 => self.sample_tuple_sort(1, max_size - 1, rng),
            _ => Sort::Bool,
        }
    }
}

pub(crate) struct UniformBitVector(pub usize);

impl rand::distributions::Distribution<BitVector> for UniformBitVector {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> BitVector {
        let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
        rug_rng.seed(&Integer::from(rng.next_u32()));
        BitVector::new(
            Integer::from(Integer::random_bits(self.0 as u32, &mut rug_rng)),
            self.0,
        )
    }
}

pub(crate) struct UniformFieldV<'a>(&'a FieldT);

impl<'a> rand::distributions::Distribution<FieldV> for UniformFieldV<'a> {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> FieldV {
        self.0.random_v(rng)
    }
}

pub(crate) struct UniformValue<'a>(pub &'a Sort);

impl<'a> rand::distributions::Distribution<Value> for UniformValue<'a> {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Value {
        match self.0 {
            Sort::Bool => Value::Bool(rng.gen()),
            Sort::F32 => Value::F32(rng.gen()),
            Sort::F64 => Value::F64(rng.gen()),
            Sort::Field(fty) => Value::Field(UniformFieldV(fty).sample(rng)),
            Sort::BitVector(w) => Value::BitVector(UniformBitVector(*w).sample(rng)),
            Sort::Tuple(sorts) => {
                Value::Tuple(sorts.iter().map(|s| UniformValue(s).sample(rng)).collect())
            }
            s => unimplemented!("Cannot sample value of sort {}", s),
        }
    }
}

impl rand::distributions::Distribution<Term> for FixedSizeDist {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Term {
        let op = self.sample_op(&self.sort, rng);
        let sorts = self.sample_child_sorts(&self.sort, &op, rng);
        if sorts.is_empty() {
            leaf_term(op)
        } else {
            let mut dists: Vec<FixedSizeDist> = sorts
                .into_iter()
                .map(|s| self.clone().with_sort(s))
                .collect();
            let excess = self.size.saturating_sub(1 + dists.len());
            let ns = Sum(dists.len(), excess).sample(rng);
            for (dist, n) in dists.iter_mut().zip(ns) {
                *dist = dist.clone().with_size(n + 1);
            }
            let children: Vec<Term> = dists.into_iter().map(|d| d.sample(rng)).collect();
            term(op, children)
        }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    use fxhash::FxHashMap as HashMap;
    use quickcheck::{Arbitrary, Gen};
    use rand::distributions::Distribution;
    use rand::SeedableRng;

    #[derive(Clone, Debug)]
    pub struct PureBool(pub Term, pub FxHashMap<String, Value>);

    impl Arbitrary for PureBool {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let t = PureBoolDist(g.size()).sample(&mut rng);
            let values: FxHashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| {
                    if let Op::Var(n, _) = &c.op() {
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

    #[derive(Clone)]
    pub struct ArbitraryTerm(pub Term);

    impl std::fmt::Debug for ArbitraryTerm {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }

    impl Arbitrary for ArbitraryTerm {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let d = FixedSizeDist {
                bv_width: Some(8),
                pf_t: Some(FieldT::FBls12381),
                tuples: true,
                size: g.size(),
                sort: Sort::Bool,
            };
            let t = d.sample(&mut rng);
            ArbitraryTerm(t)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .rev();

            Box::new(ts.skip(1).map(ArbitraryTerm))
        }
    }

    #[derive(Clone)]
    /// A purely boolean term and an environment in which it can be evaluated.
    pub struct ArbitraryBoolEnv(pub Term, pub HashMap<String, Value>);

    impl Arbitrary for ArbitraryBoolEnv {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let d = PureBoolDist(g.size());
            let t = d.sample(&mut rng);
            let values: HashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| match &c.op() {
                    Op::Var(n, Sort::Bool) => Some((n.clone(), Value::Bool(bool::arbitrary(g)))),
                    _ => None,
                })
                .collect();
            ArbitraryBoolEnv(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .rev();
            let vs = self.1.clone();

            Box::new(ts.skip(1).map(move |t| ArbitraryBoolEnv(t, vs.clone())))
        }
    }

    impl std::fmt::Debug for ArbitraryBoolEnv {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}\nin\n{:?}", self.0, self.1)
        }
    }

    #[derive(Clone)]
    /// A term and an environment in which it can be evaluated.
    pub struct ArbitraryTermEnv(pub Term, pub HashMap<String, Value>);

    impl Arbitrary for ArbitraryTermEnv {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rng = rand::rngs::StdRng::seed_from_u64(u64::arbitrary(g));
            let d = FixedSizeDist {
                bv_width: Some(8),
                pf_t: Default::default(),
                tuples: true,
                size: g.size(),
                sort: Sort::Bool,
            };
            let t = d.sample(&mut rng);
            let values: HashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| match &c.op() {
                    Op::Var(n, s) => Some((n.clone(), UniformValue(s).sample(&mut rng))),
                    _ => None,
                })
                .collect();
            ArbitraryTermEnv(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone())
                .collect::<Vec<_>>()
                .into_iter()
                .rev();
            let vs = self.1.clone();

            Box::new(ts.skip(1).map(move |t| ArbitraryTermEnv(t, vs.clone())))
        }
    }

    impl std::fmt::Debug for ArbitraryTermEnv {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}\nin\n{:?}", self.0, self.1)
        }
    }
}
