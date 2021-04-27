use super::*;
use std::sync::Arc;

// A distribution of boolean terms with some size.
// All subterms are booleans.
pub struct PureBoolDist(pub usize);

// A distribution of n usizes that sum to this value.
// (n, sum)
pub struct Sum(usize, usize);
impl rand::distributions::Distribution<Vec<usize>> for Sum {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Vec<usize> {
        use rand::seq::SliceRandom;
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
        use rand::seq::SliceRandom;
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
        let excess = self.0 - 1 - a;
        let ns = Sum(a, excess).sample(rng);
        let subterms = ns
            .into_iter()
            .map(|n| PureBoolDist(n + 1).sample(rng))
            .collect::<Vec<_>>();
        term(o, subterms)
    }
}

pub struct FixedSizeDist {
    pub size: usize,
    pub bv_width: usize,
    pub pf_mod: Arc<Integer>,
    pub sort: Sort,
}

impl FixedSizeDist {
    fn with_size(&self, size: usize) -> Self {
        FixedSizeDist {
            size,
            sort: self.sort.clone(),
            pf_mod: self.pf_mod.clone(),
            bv_width: self.bv_width,
        }
    }
    fn with_sort(&self, sort: Sort) -> Self {
        FixedSizeDist {
            size: self.size,
            pf_mod: self.pf_mod.clone(),
            sort,
            bv_width: self.bv_width,
        }
    }
}

pub struct UniformBitVector(pub usize);

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

pub struct UniformFieldElem(pub Arc<Integer>);

impl rand::distributions::Distribution<FieldElem> for UniformFieldElem {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> FieldElem {
        let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
        rug_rng.seed(&Integer::from(rng.next_u32()));
        FieldElem::new(
            Integer::from(self.0.random_below_ref(&mut rug_rng)),
            self.0.clone(),
        )
    }
}

impl rand::distributions::Distribution<Term> for FixedSizeDist {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Term {
        use rand::seq::SliceRandom;
        match self.sort.clone() {
            Sort::Bool => {
                let ops = &[
                    Op::Const(Value::Bool(rng.gen())),
                    Op::Var(
                        std::str::from_utf8(&[b'a' + rng.gen_range(0..26)])
                            .unwrap()
                            .to_owned(),
                        Sort::Bool,
                    ),
                    Op::Not, // 2
                    Op::Implies,
                    Op::Eq,
                    Op::BvBinPred(BvBinPred::Sge),
                    Op::BvBinPred(BvBinPred::Sgt),
                    Op::BvBinPred(BvBinPred::Sle),
                    Op::BvBinPred(BvBinPred::Slt),
                    Op::BvBinPred(BvBinPred::Uge),
                    Op::BvBinPred(BvBinPred::Ugt),
                    Op::BvBinPred(BvBinPred::Ule),
                    Op::BvBinPred(BvBinPred::Ult),
                    Op::BoolNaryOp(BoolNaryOp::Or),
                    Op::BoolNaryOp(BoolNaryOp::And),
                    Op::BoolNaryOp(BoolNaryOp::Xor),
                    Op::Ite,
                ];
                let o = match self.size {
                    1 => ops[..2].choose(rng),   // arity 0
                    2 => ops[2..3].choose(rng),  // arity 1
                    3 => ops[2..16].choose(rng), // arity 2
                    _ => ops[2..].choose(rng),   // others
                }
                .unwrap()
                .clone();
                // Now, self.0 is a least arity+1
                let a = o.arity().unwrap_or_else(|| rng.gen_range(2..self.size));
                let excess = self.size - 1 - a;
                let ns = Sum(a, excess).sample(rng);
                let sort = match o {
                    Op::Eq => [
                        Sort::Bool,
                        Sort::BitVector(self.bv_width),
                        Sort::Field(self.pf_mod.clone()),
                    ]
                    .choose(rng)
                    .unwrap()
                    .clone(),
                    Op::BvBinPred(_) => Sort::BitVector(self.bv_width),
                    _ => Sort::Bool,
                };
                let subterms = ns
                    .into_iter()
                    .map(|n| self.with_size(n + 1).with_sort(sort.clone()).sample(rng))
                    .collect::<Vec<_>>();
                term(o, subterms)
            }
            Sort::BitVector(w) => {
                let ops = &[
                    Op::Const(Value::BitVector(UniformBitVector(w).sample(rng))),
                    Op::Var(
                        format!(
                            "{}_bv{}",
                            std::str::from_utf8(&[b'a' + rng.gen_range(0..26)]).unwrap(),
                            w
                        ),
                        Sort::BitVector(w),
                    ),
                    Op::BvUnOp(BvUnOp::Neg),
                    Op::BvUnOp(BvUnOp::Not),
                    Op::BvUext(rng.gen_range(0..w)),
                    Op::BvSext(rng.gen_range(0..w)),
                    Op::BvBinOp(BvBinOp::Sub),
                    Op::BvBinOp(BvBinOp::Udiv),
                    Op::BvBinOp(BvBinOp::Urem),
                    Op::BvNaryOp(BvNaryOp::Or),
                    Op::BvNaryOp(BvNaryOp::And),
                    Op::BvNaryOp(BvNaryOp::Xor),
                    Op::BvNaryOp(BvNaryOp::Add),
                    Op::BvNaryOp(BvNaryOp::Mul),
                    // Add ITEs
                ];
                let o = match self.size {
                    1 => ops[..2].choose(rng),  // arity 0
                    2 => ops[2..4].choose(rng), // arity 1
                    _ => ops[2..].choose(rng),  // others
                }
                .unwrap()
                .clone();
                let sort = match o {
                    Op::BvUext(ww) => Sort::BitVector(w - ww),
                    Op::BvSext(ww) => Sort::BitVector(w - ww),
                    _ => Sort::BitVector(w),
                };
                // Now, self.0 is a least arity+1
                let a = o.arity().unwrap_or_else(|| rng.gen_range(2..self.size));
                let excess = self.size - 1 - a;
                let ns = Sum(a, excess).sample(rng);
                let subterms = ns
                    .into_iter()
                    .map(|n| self.with_size(n + 1).with_sort(sort.clone()).sample(rng))
                    .collect::<Vec<_>>();
                term(o, subterms)
            }
            Sort::Field(m) => {
                let ops = &[
                    Op::Const(Value::Field(UniformFieldElem(m.clone()).sample(rng))),
                    Op::Var(
                        format!(
                            "{}_pf",
                            std::str::from_utf8(&[b'a' + rng.gen_range(0..26)]).unwrap(),
                        ),
                        Sort::Field(m.clone()),
                    ),
                    Op::PfUnOp(PfUnOp::Neg),
                    // Can error
                    // Op::PfUnOp(PfUnOp::Recip),
                    Op::PfNaryOp(PfNaryOp::Add),
                    Op::PfNaryOp(PfNaryOp::Mul),
                ];
                let o = match self.size {
                    1 => ops[..2].choose(rng),  // arity 0
                    2 => ops[2..3].choose(rng), // arity 1
                    _ => ops[2..].choose(rng),  // others
                }
                .unwrap()
                .clone();
                let sort = Sort::Field(m);
                // Now, self.0 is a least arity+1
                let a = o.arity().unwrap_or_else(|| rng.gen_range(2..self.size));
                let excess = self.size - 1 - a;
                let ns = Sum(a, excess).sample(rng);
                let subterms = ns
                    .into_iter()
                    .map(|n| self.with_size(n + 1).with_sort(sort.clone()).sample(rng))
                    .collect::<Vec<_>>();
                term(o, subterms)
            }
            s => panic!("Unsampleabl sort: {}", s),
        }
    }
}

#[cfg(test)]
pub mod test {
    use super::*;

    use quickcheck::{Arbitrary, Gen};
    use rand::distributions::Distribution;
    use rand::SeedableRng;
    use ahash::AHashMap as HashMap;

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
                bv_width: 8,
                pf_mod: Arc::new(Integer::from(super::field::TEST_FIELD)),
                size: g.size(),
                sort: Sort::Bool,
            };
            let t = d.sample(&mut rng);
            ArbitraryTerm(t)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone()).collect::<Vec<_>>();

            Box::new(ts.into_iter().rev().skip(1).map(ArbitraryTerm))
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
                .filter_map(|c| match &c.op {
                    Op::Var(n, Sort::Bool) => Some((n.clone(), Value::Bool(bool::arbitrary(g)))),
                    _ => None,
                })
                .collect();
            ArbitraryBoolEnv(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone()).collect::<Vec<_>>();
            let vs = self.1.clone();

            Box::new(
                ts.into_iter()
                    .rev()
                    .skip(1)
                    .map(move |t| ArbitraryBoolEnv(t, vs.clone())),
            )
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
                bv_width: 8,
                size: g.size(),
                pf_mod: Arc::new(Integer::from(super::field::TEST_FIELD)),
                sort: Sort::Bool,
            };
            let t = d.sample(&mut rng);
            let values: HashMap<String, Value> = PostOrderIter::new(t.clone())
                .filter_map(|c| match &c.op {
                    Op::Var(n, Sort::Bool) => Some((n.clone(), Value::Bool(bool::arbitrary(g)))),
                    Op::Var(n, Sort::BitVector(w)) => Some((
                        n.clone(),
                        Value::BitVector(UniformBitVector(*w).sample(&mut rng)),
                    )),
                    Op::Var(n, Sort::Field(w)) => Some((
                        n.clone(),
                        Value::Field(UniformFieldElem(w.clone()).sample(&mut rng)),
                    )),
                    _ => None,
                })
                .collect();
            ArbitraryTermEnv(t, values)
        }

        fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
            let ts = PostOrderIter::new(self.0.clone()).collect::<Vec<_>>();
            let vs = self.1.clone();

            Box::new(
                ts.into_iter()
                    .rev()
                    .skip(1)
                    .map(move |t| ArbitraryTermEnv(t, vs.clone())),
            )
        }
    }

    impl std::fmt::Debug for ArbitraryTermEnv {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}\nin\n{:?}", self.0, self.1)
        }
    }
}
