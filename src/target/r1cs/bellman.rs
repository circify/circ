//! Exporting our R1CS to bellman
use ::bellman::{groth16, Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};
use ff::{Field, PrimeField, PrimeFieldBits};
use fxhash::FxHashMap;
use group::WnafGroup;
use log::debug;
use pairing::{Engine, MultiMillerLoop};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::marker::PhantomData;
use std::path::Path;
use std::str::FromStr;

use rug::integer::{IsPrime, Order};
use rug::Integer;

use super::proof;
use super::{wit_comp::StagedWitCompEvaluator, Lc, ProverData, Var, VarType, VerifierData};
use crate::ir::term::Value;

/// Convert a (rug) integer to a prime field element.
pub(super) fn int_to_ff<F: PrimeField>(i: Integer) -> F {
    assert!(i >= 0);
    let digits: Vec<u8> = i.to_digits(rug::integer::Order::LsfLe);
    let mut repr = F::Repr::default();
    assert!(digits.len() <= repr.as_ref().len());
    repr.as_mut()[..digits.len()].copy_from_slice(&digits);
    F::from_repr_vartime(repr).unwrap()
}

/// Convert one our our linear combinations to a bellman linear combination.
/// Takes a zero linear combination. We could build it locally, but bellman provides one, so...
pub(super) fn lc_to_bellman<F: PrimeField, CS: ConstraintSystem<F>>(
    vars: &HashMap<Var, Variable>,
    lc: &Lc,
    zero_lc: LinearCombination<F>,
) -> LinearCombination<F> {
    let mut lc_bellman = zero_lc;
    // This zero test is needed until https://github.com/zkcrypto/bellman/pull/78 is resolved
    if !lc.constant.is_zero() {
        lc_bellman = lc_bellman + (int_to_ff((&lc.constant).into()), CS::one());
    }
    for (v, c) in &lc.monomials {
        // ditto
        if !c.is_zero() {
            lc_bellman = lc_bellman + (int_to_ff(c.into()), *vars.get(v).unwrap());
        }
    }
    lc_bellman
}

// hmmm... this should work essentially all the time, I think
pub(super) fn get_modulus<F: Field + PrimeField>() -> Integer {
    let neg_1_f = -F::one();
    let p_lsf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Lsf) + 1;
    let p_msf: Integer = Integer::from_digits(neg_1_f.to_repr().as_ref(), Order::Msf) + 1;
    if p_lsf.is_probably_prime(30) != IsPrime::No {
        p_lsf
    } else if p_msf.is_probably_prime(30) != IsPrime::No {
        p_msf
    } else {
        panic!("could not determine ff::Field byte order")
    }
}

/// A synthesizable bellman circuit.
///
/// Optionally contains a variable value map. This must be populated to use the
/// bellman prover.
pub struct SynthInput<'a>(&'a ProverData, Option<&'a FxHashMap<String, Value>>);

impl<'a, F: PrimeField> Circuit<F> for SynthInput<'a> {
    #[track_caller]
    fn synthesize<CS>(self, cs: &mut CS) -> std::result::Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let f_mod = get_modulus::<F>();
        assert_eq!(
            self.0.r1cs.field.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Bellman CS expects \n{}",
            self.0.r1cs.field,
            f_mod
        );
        let mut vars = HashMap::with_capacity(self.0.r1cs.vars.len());
        let values: Option<Vec<_>> = self.1.map(|values| {
            let mut evaluator = StagedWitCompEvaluator::new(&self.0.precompute);
            let mut ffs = Vec::new();
            ffs.extend(evaluator.eval_stage(values.clone()).into_iter().cloned());
            ffs.extend(
                evaluator
                    .eval_stage(Default::default())
                    .into_iter()
                    .cloned(),
            );
            ffs
        });
        for (i, var) in self.0.r1cs.vars.iter().copied().enumerate() {
            assert!(
                !matches!(var.ty(), VarType::CWit),
                "Bellman doesn't support committed witnesses"
            );
            assert!(
                !matches!(var.ty(), VarType::RoundWit | VarType::Chall),
                "Bellman doesn't support rounds"
            );
            let public = matches!(var.ty(), VarType::Inst);
            let name = self.0.r1cs.names.get(&var).unwrap();
            let name_f = || format!("{name:?}");
            let val_f = || {
                Ok({
                    let i_val = &values.as_ref().expect("missing values")[i];
                    let ff_val = int_to_ff(i_val.as_pf().into());
                    debug!("value : {name:?} -> {ff_val:?} ({i_val})");
                    ff_val
                })
            };
            debug!("var: {:?}, public: {}", name, public);
            let v = if public {
                cs.alloc_input(name_f, val_f)?
            } else {
                cs.alloc(name_f, val_f)?
            };
            vars.insert(var, v);
        }
        let bellman_lcs: Vec<(_, _, _)> = self
            .0
            .r1cs
            .constraints
            .par_iter()
            .map(|(a, b, c)| {
                (
                    lc_to_bellman::<F, CS>(&vars, a, LinearCombination::zero()),
                    lc_to_bellman::<F, CS>(&vars, b, LinearCombination::zero()),
                    lc_to_bellman::<F, CS>(&vars, c, LinearCombination::zero()),
                )
            })
            .collect();

        for (i, (a, b, c)) in bellman_lcs.into_iter().enumerate() {
            cs.enforce(|| format!("con{i}"), |_| a, |_| b, |_| c);
        }
        debug!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.0.r1cs.constraints.len()
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
            int_to_ff(i)
        })
        .collect()
}

mod serde_pk {
    use bellman::groth16::Parameters;
    use pairing::Engine;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, E: Engine>(
        p: &Parameters<E>,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        let mut bs: Vec<u8> = Vec::new();
        p.write(&mut bs).unwrap();
        serde_bytes::ByteBuf::from(bs).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, E: Engine>(
        de: D,
    ) -> Result<Parameters<E>, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        Ok(Parameters::read(&**bs, false).unwrap())
    }
}

mod serde_vk {
    use bellman::groth16::VerifyingKey;
    use pairing::Engine;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, E: Engine>(
        p: &VerifyingKey<E>,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        let mut bs: Vec<u8> = Vec::new();
        p.write(&mut bs).unwrap();
        serde_bytes::ByteBuf::from(bs).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, E: Engine>(
        de: D,
    ) -> Result<VerifyingKey<E>, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        Ok(VerifyingKey::read(&**bs).unwrap())
    }
}

mod serde_pf {
    use bellman::groth16::Proof;
    use pairing::Engine;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, E: Engine>(p: &Proof<E>, ser: S) -> Result<S::Ok, S::Error> {
        let mut bs: Vec<u8> = Vec::new();
        p.write(&mut bs).unwrap();
        serde_bytes::ByteBuf::from(bs).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, E: Engine>(de: D) -> Result<Proof<E>, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        Ok(Proof::read(&**bs).unwrap())
    }
}

/// The [::bellman] implementation of Groth16.
pub struct Bellman<E: Engine>(PhantomData<E>);

/// The pk for [Bellman]
#[derive(Serialize, Deserialize)]
pub struct ProvingKey<E: Engine>(
    ProverData,
    #[serde(with = "serde_pk")] groth16::Parameters<E>,
);

/// The vk for [Bellman]
#[derive(Serialize, Deserialize)]
pub struct VerifyingKey<E: Engine>(
    VerifierData,
    #[serde(with = "serde_vk")] groth16::VerifyingKey<E>,
);

/// The proof for [Bellman]
#[derive(Serialize, Deserialize)]
pub struct Proof<E: Engine>(#[serde(with = "serde_pf")] groth16::Proof<E>);

impl<E: Engine> proof::ProofSystem for Bellman<E>
where
    E: MultiMillerLoop,
    E::G1: WnafGroup,
    E::G2: WnafGroup,
    E::Fr: PrimeFieldBits,
{
    type VerifyingKey = VerifyingKey<E>;

    type ProvingKey = ProvingKey<E>;

    type Proof = Proof<E>;

    fn setup(p_data: ProverData, v_data: VerifierData) -> (Self::ProvingKey, Self::VerifyingKey) {
        assert_eq!(p_data.r1cs.commitments.len(), 0);
        let rng = &mut rand::thread_rng();
        let params =
            groth16::generate_random_parameters::<E, _, _>(SynthInput(&p_data, None), rng).unwrap();
        let v_params = params.vk.clone();
        (ProvingKey(p_data, params), VerifyingKey(v_data, v_params))
    }

    fn prove(pk: &Self::ProvingKey, witness: &FxHashMap<String, Value>) -> Self::Proof {
        let rng = &mut rand::thread_rng();
        pk.0.check_all(witness);
        Proof(groth16::create_random_proof(SynthInput(&pk.0, Some(witness)), &pk.1, rng).unwrap())
    }

    fn verify(vk: &Self::VerifyingKey, inst: &FxHashMap<String, Value>, pf: &Self::Proof) -> bool {
        let pvk = groth16::prepare_verifying_key(&vk.1);
        let r1cs_inst_map = vk.0.eval(inst);
        let r1cs_inst: Vec<E::Fr> = r1cs_inst_map
            .into_iter()
            .map(|i| int_to_ff(i.i()))
            .collect();
        groth16::verify_proof(&pvk, &pf.0, &r1cs_inst).is_ok()
    }
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
        let by_fn = int_to_ff::<Scalar>(i.clone());
        let by_str = Scalar::from_str_vartime(&format!("{i}")).unwrap();
        by_fn == by_str
    }

    fn convert(i: Integer) {
        let by_fn = int_to_ff::<Scalar>(i.clone());
        let by_str = Scalar::from_str_vartime(&format!("{i}")).unwrap();
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
        convert(modulus - 1);
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
