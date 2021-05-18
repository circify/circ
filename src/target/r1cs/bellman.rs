//! Exporting our R1CS to bellman
use ::bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::PrimeField;
use gmp_mpfr_sys::gmp::limb_t;
use log::debug;
use std::collections::HashMap;

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
    lc_bellman = lc_bellman + (int_to_ff(&lc.constant), CS::one());
    for (v, c) in &lc.monomials {
        lc_bellman = lc_bellman + (int_to_ff(c), vars.get(v).unwrap().clone());
    }
    lc_bellman
}

fn modulus_as_int<F: PrimeField>() -> Integer {
    let mut bits = F::char_le_bits().to_bitvec();
    let mut acc = Integer::from(0);
    while let Some(b) = bits.pop() {
        acc = acc << 1;
        acc += b as u8;
    }
    acc
}

impl<'a, F: PrimeField, S: Display + Eq + Hash> Circuit<F> for &'a R1cs<S> {
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
        let vars = self
            .idxs_signals
            .iter()
            .map(|(i, s)| {
                cs.alloc(
                    || format!("{}", s),
                    || {
                        Ok({
                            let i_val = self.values.as_ref().unwrap().get(i).unwrap();
                            let ff_val = int_to_ff(i_val);
                            debug!("witness: {} -> {:?} ({})", s, ff_val, i_val);
                            ff_val
                        })
                    },
                )
                .map(|v| (*i, v))
            })
            .collect::<Result<HashMap<_, _>, _>>()?;
        for (i, (a, b, c)) in self.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{}", i),
                |z| lc_to_bellman::<F, CS>(&vars, a, z),
                |z| lc_to_bellman::<F, CS>(&vars, b, z),
                |z| lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use bls12_381::Scalar;
    use quickcheck::{Arbitrary, Gen};
    use quickcheck_macros::quickcheck;

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
        let by_str = Scalar::from_str(&format!("{}", i)).unwrap();
        by_fn == by_str
    }

    fn convert(i: Integer) {
        let by_fn = int_to_ff::<Scalar>(&i);
        let by_str = Scalar::from_str(&format!("{}", i)).unwrap();
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
}
