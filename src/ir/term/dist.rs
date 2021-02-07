use super::*;

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
    pub sort: Sort,
}

impl FixedSizeDist {
    fn with_size(&self, size: usize) -> Self {
        FixedSizeDist {
            size,
            sort: self.sort.clone(),
            bv_width: self.bv_width,
        }
    }
    fn with_sort(&self, sort: Sort) -> Self {
        FixedSizeDist {
            size: self.size,
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
                    Op::Eq => [Sort::Bool, Sort::BitVector(self.bv_width)]
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
            s => panic!("Unsampleabl sort: {}", s),
        }
    }
}
