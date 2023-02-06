//! Exporting our R1CS to bellman
use ::bellman::{
    cc::{CcCircuit, CcConstraintSystem},
    mirage, SynthesisError,
};
use ff::{PrimeField, PrimeFieldBits};
use fxhash::FxHashMap;
use group::WnafGroup;
use log::debug;
use pairing::{Engine, MultiMillerLoop};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::marker::PhantomData;
use std::path::Path;
use std::str::FromStr;

use rug::Integer;

use super::proof;
use super::{wit_comp::StagedWitCompEvaluator, ProverData, VarType, VerifierData};
use crate::ir::term::Value;

use super::bellman::{get_modulus, int_to_ff, lc_to_bellman};

fn ff_to_int<F: PrimeFieldBits>(f: F) -> Integer {
    let mut buffer = vec![];
    use std::io::Read;
    f.to_le_bits()
        .as_bitslice()
        .read_to_end(&mut buffer)
        .unwrap();
    Integer::from_digits(&buffer, rug::integer::Order::Lsf)
}

/// A synthesizable bellman circuit.
///
/// Optionally contains a variable value map. This must be populated to use the
/// bellman prover.
pub struct SynthInput<'a>(&'a ProverData, Option<&'a FxHashMap<String, Value>>);

impl<'a, F: PrimeField + PrimeFieldBits> CcCircuit<F> for SynthInput<'a> {
    #[track_caller]
    fn synthesize<CS>(self, cs: &mut CS) -> std::result::Result<(), SynthesisError>
    where
        CS: CcConstraintSystem<F>,
    {
        let f_mod = get_modulus::<F>();
        assert_eq!(
            self.0.r1cs.field.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but mirage CS expects \n{}",
            self.0.r1cs.field,
            f_mod
        );
        let mut vars = HashMap::with_capacity(self.0.r1cs.vars.len());
        // (assignment values, evaluator, next evaluator inputs)
        let mut wit_comp: Option<(
            Vec<Value>,
            StagedWitCompEvaluator<'a>,
            FxHashMap<String, Value>,
        )> = self.1.map(|inputs| {
            (
                Vec::new(),
                StagedWitCompEvaluator::new(&self.0.precompute),
                inputs.clone(),
            )
        });
        let mut var_idx = 0;
        let num_stages = self.0.precompute.stage_sizes().count();
        for (i, num_vars) in self.0.precompute.stage_sizes().enumerate() {
            if let Some((ref mut var_values, ref mut evaluator, ref mut inputs)) = wit_comp.as_mut()
            {
                var_values.extend(
                    evaluator
                        .eval_stage(std::mem::take(inputs))
                        .into_iter()
                        .cloned(),
                );
            }
            let num_challs = if i + 1 < num_stages {
                self.0.precompute.num_stage_inputs(i + 1)
            } else {
                0
            };
            for j in 0..(num_vars + num_challs) {
                let var = self.0.r1cs.vars[var_idx];
                let name_f = || format!("{var:?}");
                let val_f = || {
                    Ok({
                        let i_val = &wit_comp.as_ref().expect("missing values").0[var_idx];
                        let ff_val = int_to_ff(i_val.as_pf().into());
                        debug!("value : {var:?} -> {ff_val:?} ({i_val})");
                        ff_val
                    })
                };
                let v = match var.ty() {
                    VarType::Inst => cs.alloc_input(name_f, val_f)?,
                    VarType::RoundWit => cs.alloc(name_f, val_f)?,
                    VarType::FinalWit => cs.alloc(name_f, val_f)?,
                    VarType::Chall => {
                        let (v, val) = cs.alloc_random(name_f)?;
                        if let Some((ref mut values, _, ref mut inputs)) = wit_comp.as_mut() {
                            let val =
                                Value::Field(self.0.r1cs.field.new_v(ff_to_int(val.unwrap())));
                            values.push(val.clone());
                            let name = self.0.r1cs.names.get(&var).unwrap();
                            inputs.insert(name.to_owned(), val);
                        }
                        v
                    }
                    VarType::CWit => unimplemented!(),
                };
                vars.insert(var, v);
                var_idx += 1;
                if j + 1 == num_vars && num_challs > 0 {
                    cs.end_aux_block(|| format!("block {}", i - 1))?;
                }
            }
        }

        for (i, (a, b, c)) in self.0.r1cs.constraints.iter().enumerate() {
            cs.enforce(
                || format!("con{i}"),
                |z| lc_to_bellman::<F, CS>(&vars, a, z),
                |z| lc_to_bellman::<F, CS>(&vars, b, z),
                |z| lc_to_bellman::<F, CS>(&vars, c, z),
            );
        }
        debug!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.0.r1cs.constraints.len()
        );
        Ok(())
    }

    fn num_aux_blocks(&self) -> usize {
        self.0.precompute.stage_sizes().count() - 2
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
    use bellman::mirage::Parameters;
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
    use bellman::mirage::VerifyingKey;
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
    use bellman::mirage::Proof;
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
pub struct Mirage<E: Engine>(PhantomData<E>);

/// The pk for [mirage]
#[derive(Serialize, Deserialize)]
pub struct ProvingKey<E: Engine>(
    ProverData,
    #[serde(with = "serde_pk")] mirage::Parameters<E>,
);

/// The vk for [mirage]
#[derive(Serialize, Deserialize)]
pub struct VerifyingKey<E: Engine>(
    VerifierData,
    #[serde(with = "serde_vk")] mirage::VerifyingKey<E>,
);

/// The proof for [mirage]
#[derive(Serialize, Deserialize)]
pub struct Proof<E: Engine>(#[serde(with = "serde_pf")] mirage::Proof<E>);

impl<E: Engine> proof::ProofSystem for Mirage<E>
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
        let rng = &mut rand::thread_rng();
        let params =
            mirage::generate_random_parameters::<E, _, _>(SynthInput(&p_data, None), rng).unwrap();
        let v_params = params.vk.clone();
        (ProvingKey(p_data, params), VerifyingKey(v_data, v_params))
    }

    fn prove(pk: &Self::ProvingKey, witness: &FxHashMap<String, Value>) -> Self::Proof {
        let rng = &mut rand::thread_rng();
        pk.0.check_all(witness);
        Proof(mirage::create_random_proof(SynthInput(&pk.0, Some(witness)), &pk.1, rng).unwrap())
    }

    fn verify(vk: &Self::VerifyingKey, inst: &FxHashMap<String, Value>, pf: &Self::Proof) -> bool {
        let pvk = mirage::prepare_verifying_key(&vk.1);
        let r1cs_inst_map = vk.0.eval(inst);
        let r1cs_inst: Vec<E::Fr> = r1cs_inst_map
            .into_iter()
            .map(|i| int_to_ff(i.i()))
            .collect();
        mirage::verify_proof(&pvk, &pf.0, &r1cs_inst).is_ok()
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

    #[quickcheck]
    fn roundtrip_random(BlsScalar(i): BlsScalar) -> bool {
        let ff = int_to_ff::<Scalar>(i.clone());
        let i2 = ff_to_int(ff);
        i == i2
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
