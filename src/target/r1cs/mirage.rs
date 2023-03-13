//! Exporting our R1CS to field1ield1ellman
#![allow(unused)]
use ::bellman::{
    cc::{CcCircuit, CcConstraintSystem},
    kw15, mirage, SynthesisError,
};
use ff::{Field, PrimeField, PrimeFieldBits};
use fxhash::FxHashMap;
use group::GroupEncoding;
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

mod cp_link;

fn ff_to_int<F: PrimeFieldBits>(f: F) -> Integer {
    let mut buffer = vec![];
    use std::io::Read;
    f.to_le_bits()
        .as_bitslice()
        .read_to_end(&mut buffer)
        .unwrap();
    Integer::from_digits(&buffer, rug::integer::Order::Lsf)
}

fn val_to_ff<F: PrimeField>(v: Value) -> F {
    int_to_ff(v.as_pf().into())
}

/// A synthesizable bellman circuit.
///
/// Optionally contains a variable value map. This must be populated to use the
/// bellman prover.
pub struct SynthInput<'a, F>(
    /// The prover data
    &'a ProverData,
    /// The inputs
    Option<&'a FxHashMap<String, Value>>,
    /// Commitment randomness
    Option<Vec<F>>,
);

impl<'a, F: PrimeField + PrimeFieldBits> CcCircuit<F> for SynthInput<'a, F> {
    #[track_caller]
    fn synthesize<CS>(self, cs: &mut CS) -> std::result::Result<(), SynthesisError>
    where
        CS: CcConstraintSystem<F>,
    {
        if let Some(v) = self.2.as_ref() {
            assert_eq!(self.0.r1cs.commitments.len(), v.len());
        }
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
        let mut uses: HashMap<super::Var, usize> =
            self.0.r1cs.vars.iter().map(|v| (*v, 0)).collect();
        for c in &self.0.r1cs.constraints {
            for lc in &[&c.0, &c.1, &c.2] {
                for (k, v) in &lc.monomials {
                    if !(v.is_zero()) {
                        *uses.get_mut(k).unwrap() += 1;
                    }
                }
            }
        }
        for (v, uses) in &uses {
            if uses == &0 {
                println!("{v:?}: no uses");
            }
        }
        let mut var_idx = 0;
        let num_stages = self.0.precompute.stage_sizes().count();
        let mut cwit_randomness_vars = Vec::new();
        let n_stages = self.0.precompute.stage_sizes().count();
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
            let mut num_cwits: Vec<usize> =
                self.0.r1cs.commitments.iter().map(|c| c.len()).collect();
            num_cwits.reverse();
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
                    VarType::CWit => {
                        assert!(!num_cwits.is_empty());
                        *num_cwits.last_mut().unwrap() -= 1;
                        let v = cs.alloc(name_f, val_f)?;
                        while let Some(n) = num_cwits.last() {
                            if n == &0 {
                                num_cwits.pop();
                                let rand_var = cs.alloc(
                                    || format!("cwit{}_rand", cwit_randomness_vars.len()),
                                    || Ok(self.2.as_ref().unwrap()[cwit_randomness_vars.len()]),
                                )?;
                                cwit_randomness_vars.push(rand_var);
                                cs.end_aux_block(|| format!("commit {}", num_cwits.len()))?;
                            } else {
                                break;
                            }
                        }
                        v
                    }
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
        let one = CS::one();
        cs.enforce(
            || "rand_vars_dummy".to_string(),
            |z| cwit_randomness_vars.iter().fold(z, |acc, v| acc + *v),
            |z| z + (F::from(1), one),
            |z| cwit_randomness_vars.iter().fold(z, |acc, v| acc + *v),
        );
        debug!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.0.r1cs.constraints.len()
        );
        Ok(())
    }

    fn num_aux_blocks(&self) -> usize {
        self.0.precompute.stage_sizes().count() - 2 + self.0.r1cs.commitments.len()
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

macro_rules! bellman_serde_impl {
    ($ty_path:path,$ty:tt) => {
        use pairing::Engine;
        use serde::{Deserialize, Deserializer, Serialize, Serializer};
        use $ty_path;

        #[allow(dead_code)]
        pub fn serialize<S: Serializer, E: Engine>(p: &$ty<E>, ser: S) -> Result<S::Ok, S::Error> {
            let mut bs: Vec<u8> = Vec::new();
            p.write(&mut bs).unwrap();
            serde_bytes::ByteBuf::from(bs).serialize(ser)
        }

        #[allow(dead_code)]
        pub fn deserialize<'de, D: Deserializer<'de>, E: Engine>(
            de: D,
        ) -> Result<$ty<E>, D::Error> {
            let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
            Ok($ty::read(&**bs).unwrap())
        }
    };
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
    bellman_serde_impl!(bellman::mirage::VerifyingKey, VerifyingKey);
}

mod serde_pf {
    bellman_serde_impl!(bellman::mirage::Proof, Proof);
}

mod serde_kw15_pf {
    bellman_serde_impl!(bellman::kw15::Proof, Proof);
}

mod serde_kw15_pk {
    bellman_serde_impl!(bellman::kw15::ProvingKey, ProvingKey);
}

mod serde_kw15_vk {
    bellman_serde_impl!(bellman::kw15::VerifyingKey, VerifyingKey);
}

mod serde_group {
    use group::GroupEncoding;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, G: GroupEncoding>(p: &G, ser: S) -> Result<S::Ok, S::Error> {
        serde_bytes::ByteBuf::from(p.to_bytes().as_ref().to_vec()).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, G: GroupEncoding>(de: D) -> Result<G, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        let mut encoding = G::Repr::default();
        encoding.as_mut().copy_from_slice(&bs);
        Ok(G::from_bytes(&encoding).unwrap())
    }
}

mod serde_group_vec {
    use byteorder::{BigEndian, ReadBytesExt, WriteBytesExt};
    use group::GroupEncoding;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, G: GroupEncoding>(
        p: &Vec<G>,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        use std::io::Write;
        let mut bytes = Vec::new();
        bytes.write_u64::<BigEndian>(p.len() as u64).unwrap();
        for i in p {
            bytes.write_all(i.to_bytes().as_ref()).unwrap();
        }
        serde_bytes::ByteBuf::from(bytes).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, G: GroupEncoding>(
        de: D,
    ) -> Result<Vec<G>, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        let mut bytes = bs.into_vec();
        let mut reader = bytes.as_slice();
        let len = reader.read_u64::<BigEndian>().unwrap() as usize;
        let mut groups = Vec::new();
        for _ in 0..len {
            let mut encoding = G::Repr::default();
            let n = encoding.as_ref().len();
            encoding.as_mut().copy_from_slice(&reader[..n]);
            reader = &reader[n..];
            groups.push(G::from_bytes(&encoding).unwrap())
        }
        assert_eq!(reader.len(), 0);
        Ok(groups)
    }
}

mod serde_field {
    use ff::PrimeField;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer, F: PrimeField>(p: &F, ser: S) -> Result<S::Ok, S::Error> {
        serde_bytes::ByteBuf::from(p.to_repr().as_ref().to_vec()).serialize(ser)
    }

    pub fn deserialize<'de, D: Deserializer<'de>, F: PrimeField>(de: D) -> Result<F, D::Error> {
        let bs: serde_bytes::ByteBuf = Deserialize::deserialize(de)?;
        let mut encoding = F::Repr::default();
        encoding.as_mut().copy_from_slice(&bs);
        Ok(F::from_repr(encoding).unwrap())
    }
}

/// The [::bellman] implementation of Groth16.
pub struct Mirage<E: Engine>(PhantomData<E>);

/// The pk for [mirage]
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProvingKey<E: Engine> {
    data: ProverData,
    #[serde(with = "serde_pk")]
    mirage: mirage::Parameters<E>,
    link: cp_link::ProvingKey<E>,
}

/// The vk for [mirage]
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifyingKey<E: Engine> {
    data: VerifierData,
    #[serde(with = "serde_vk")]
    mirage: mirage::VerifyingKey<E>,
    link: cp_link::VerifyingKey<E>,
    ck: cp_link::CommitKey<E>,
}

/// The proof for [mirage]
#[derive(Serialize, Deserialize)]
#[serde(bound = "")]
pub struct Proof<E: Engine> {
    #[serde(with = "serde_pf")]
    mirage: mirage::Proof<E>,
    link: cp_link::Proof<E>,
}

/// The commitment for [mirage]
#[derive(Serialize, Deserialize)]
pub struct Commitment<G: GroupEncoding>(#[serde(with = "serde_group")] G);

/// The commitment randomness for [mirage]
#[derive(Serialize, Deserialize, Default)]
pub struct ComRand<F: PrimeField>(#[serde(with = "serde_field")] F);

impl<E: Engine> proof::CommitProofSystem for Mirage<E>
where
    E: MultiMillerLoop,
    E::G1: WnafGroup,
    E::G2: WnafGroup,
    E::Fr: PrimeFieldBits,
{
    type VerifyingKey = VerifyingKey<E>;

    type ProvingKey = ProvingKey<E>;

    type Proof = Proof<E>;

    type Commitment = Commitment<E::G1>;

    type ComRand = ComRand<E::Fr>;

    fn cp_setup(
        p_data: ProverData,
        v_data: VerifierData,
    ) -> (Self::ProvingKey, Self::VerifyingKey) {
        let rng = &mut rand::thread_rng();
        let num_cmts = p_data.r1cs.commitments.len();
        let data_len = p_data
            .r1cs
            .commitments
            .first()
            .map(|c| c.len())
            .unwrap_or(0);
        let params =
            mirage::generate_random_parameters::<E, _, _>(SynthInput(&p_data, None, None), rng)
                .unwrap();
        let cks = (0..num_cmts)
            .map(|i| {
                let mut all_keys: Vec<_> = (*params.ls[i]).clone();
                let rand_key = all_keys.pop().unwrap();
                cp_link::CommitKey {
                    data_keys: all_keys,
                    rand_key,
                }
            })
            .collect();
        let ck = cp_link::sample_ck(rng, data_len);
        let (link_pk, link_vk) = cp_link::key_gen(ck.clone(), cks, rng);
        let v_params = params.vk.clone();
        (
            ProvingKey {
                data: p_data,
                mirage: params,
                link: link_pk,
            },
            VerifyingKey {
                ck,
                data: v_data,
                mirage: v_params,
                link: link_vk,
            },
        )
    }

    fn cp_prove(
        pk: &Self::ProvingKey,
        witness: &FxHashMap<String, Value>,
        rand: &[Self::ComRand],
    ) -> Self::Proof {
        assert_eq!(rand.len(), pk.data.num_commitments());
        let rng = &mut rand::thread_rng();
        pk.data.check_all(witness);
        let rands: Vec<E::Fr> = rand.iter().map(|r| r.0).collect();
        let mut rng = &mut rand::thread_rng();
        let pf_rands: Vec<E::Fr> = (0..rand.len()).map(|_| E::Fr::random(&mut *rng)).collect();
        let (mirage_pf, mut aux_blocks) = mirage::create_random_proof(
            SynthInput(&pk.data, Some(witness), Some(pf_rands.clone())),
            &pk.mirage,
            rng,
        )
        .unwrap();
        // cut randomness
        for block in &mut aux_blocks {
            block.pop();
        }
        while aux_blocks.len() > rands.len() {
            aux_blocks.pop();
        }
        let link = cp_link::prove(&pk.link, rands, pf_rands, aux_blocks);
        Proof {
            mirage: mirage_pf,
            link,
        }
    }

    fn cp_verify(
        vk: &Self::VerifyingKey,
        inst: &FxHashMap<String, Value>,
        pf: &Self::Proof,
        cmts: &[Self::Commitment],
    ) -> bool {
        assert_eq!(cmts.len(), vk.data.num_commitments());
        let pvk = mirage::prepare_verifying_key(&vk.mirage);
        let r1cs_inst_map = vk.data.eval(inst);
        let r1cs_inst: Vec<E::Fr> = r1cs_inst_map
            .into_iter()
            .map(|i| int_to_ff(i.i()))
            .collect();
        mirage::verify_proof(&pvk, &pf.mirage, &r1cs_inst).is_ok()
    }

    fn cp_commit(vk: &Self::VerifyingKey, data: Value, rand: &Self::ComRand) -> Self::Commitment {
        let data_vec: Vec<Value> = data.as_array().values();
        let data_vec: Vec<E::Fr> = data_vec.into_iter().map(val_to_ff).collect();
        assert_eq!(data_vec.len(), vk.ck.data_keys.len());
        Commitment(cp_link::commit(vk.ck.clone(), data_vec, rand.0).into())
    }

    fn sample_com_rand() -> Self::ComRand {
        use ff::Field;
        let mut rng = &mut rand::thread_rng();
        ComRand(E::Fr::random(rng))
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
