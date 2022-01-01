//! Exporting our R1CS to bellman
use ::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::{PrimeField, PrimeFieldBits};
use gmp_mpfr_sys::gmp::limb_t;
use log::debug;
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::str::FromStr;

use super::*;

/// Convert a (rug) integer to a prime field element.
fn int_to_ff<F: PrimeField>(i: &Integer) -> F {
    let mut accumulator = F::from(0);
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    let limb_base = F::from(2).pow_vartime(&[limb_bits]);
    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= limb_base;
        accumulator += F::from(*digit as u64);
    }
    accumulator
}

/// Convert one our our linear combinations to a bellman linear combination.
/// Takes a zero linear combination. We could build it locally, but bellman provides one, so...
fn lc_to_bellman<F: PrimeField, CS: ConstraintSystem<F>>(
    vars: &HashMap<usize, Variable>,
    lc: &Lc,
    zero_lc: LinearCombination<F>,
) -> LinearCombination<F> {
    let mut lc_bellman = zero_lc;
    // This zero test is needed until https://github.com/zkcrypto/bellman/pull/78 is resolved
    if lc.constant != 0 {
        lc_bellman = lc_bellman + (int_to_ff(&lc.constant), CS::one());
    }
    for (v, c) in &lc.monomials {
        // ditto
        if c != &0 {
            lc_bellman = lc_bellman + (int_to_ff(c), *vars.get(v).unwrap());
        }
    }
    lc_bellman
}

fn modulus_as_int<F: PrimeFieldBits>() -> Integer {
    let mut bits = F::char_le_bits().to_bitvec();
    let mut acc = Integer::from(0);
    while let Some(b) = bits.pop() {
        acc <<= 1;
        acc += b as u8;
    }
    acc
}

impl<'a, F: PrimeField + PrimeFieldBits, S: Display + Eq + Hash + Ord> Circuit<F> for &'a R1cs<S> {
    fn synthesize<CS>(self, cs: &mut CS) -> std::result::Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let f_mod = modulus_as_int::<F>();
        assert_eq!(
            *self.modulus, f_mod,
            "\nR1CS has modulus \n{},\n but Bellman CS expectes \n{}",
            self.modulus, f_mod
        );
        let mut uses = self
            .idxs_signals
            .iter()
            .map(|(i, _)| (*i, 0))
            .collect::<HashMap<usize, usize>>();
        for (a, b, c) in self.constraints.iter() {
            [a, b, c].iter().for_each(|x| {
                x.monomials
                    .iter()
                    .for_each(|(i, _)| *uses.get_mut(i).unwrap() += 1)
            });
        }
        let mut vars = HashMap::default();
        for i in 0..self.next_idx {
            if let Some(s) = self.idxs_signals.get(&i) {
                //for (_i, s) in self.idxs_signals.get() {
                if uses.get(&i).unwrap() > &0 {
                    let name_f = || format!("{}", s);
                    let val_f = || {
                        Ok({
                            let i_val = self
                                .values
                                .as_ref()
                                .expect("missing values")
                                .get(&i)
                                .unwrap();
                            let ff_val = int_to_ff(i_val);
                            debug!("value : {} -> {:?} ({})", s, ff_val, i_val);
                            ff_val
                        })
                    };
                    let public = self.public_idxs.contains(&i);
                    debug!("var: {}, public: {}", s, public);
                    let v = if public {
                        cs.alloc_input(name_f, val_f)?
                    } else {
                        cs.alloc(name_f, val_f)?
                    };
                    vars.insert(i, v);
                } else {
                    debug!("drop dead var: {}", s);
                }
            }
        }
        for (i, (a, b, c)) in self.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| lc_to_bellman::<F, CS>(&vars, a, z),
                |z| lc_to_bellman::<F, CS>(&vars, b, z),
                |z| lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }
        debug!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.constraints.len()
        );
        Ok(())
    }
}

/// Convert a (rug) integer to a prime field element.
pub fn parse_instance<P: AsRef<Path>, F: PrimeField>(path: P) -> Vec<F> {
    let f = BufReader::new(File::open(path).unwrap());
    f.lines()
        .map(|line| {
            let s = line.unwrap();
            let i = Integer::from_str(s.trim()).unwrap();
            int_to_ff(&i)
        })
        .collect()
}

#[cfg(test)]
mod test {
    use super::*;
    use bls12_381::Scalar;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;
    use std::io::Write;

    #[derive(Clone, Debug)]
    struct BlsScalar(Integer);

    impl Arbitrary for BlsScalar {
        fn arbitrary(g: &mut Gen) -> Self {
            let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
            rug_rng.seed(&Integer::from(u32::arbitrary(g)));
            let modulus = Integer::from(
                Integer::parse_radix(
                    "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
                    16,
                )
                .unwrap(),
            );
            let i = Integer::from(modulus.random_below_ref(&mut rug_rng));
            BlsScalar(i)
        }
    }

    #[quickcheck]
    fn int_to_ff_random(BlsScalar(i): BlsScalar) -> bool {
        let by_fn = int_to_ff::<Scalar>(&i);
        let by_str = Scalar::from_str_vartime(&format!("{}", i)).unwrap();
        by_fn == by_str
    }

    fn convert(i: Integer) {
        let by_fn = int_to_ff::<Scalar>(&i);
        let by_str = Scalar::from_str_vartime(&format!("{}", i)).unwrap();
        assert_eq!(by_fn, by_str);
    }

    #[test]
    fn neg_one() {
        let modulus = Integer::from(
            Integer::parse_radix(
                "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001",
                16,
            )
            .unwrap(),
        );
        convert(modulus.clone() - 1);
    }

    #[test]
    fn zero() {
        convert(Integer::from(0));
    }

    #[test]
    fn one() {
        convert(Integer::from(1));
    }

    #[test]
    fn parse() {
        let path = format!("{}/instance", std::env::temp_dir().to_str().unwrap());
        {
            let mut f = File::create(&path).unwrap();
            write!(f, "5\n6").unwrap();
        }
        let i = parse_instance::<_, Scalar>(&path);
        assert_eq!(i[0], Scalar::from(5));
        assert_eq!(i[1], Scalar::from(6));
    }
}
