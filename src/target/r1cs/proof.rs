//! A trait for CirC-compatible proofs

use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

use bincode::{deserialize_from, serialize_into};
use fxhash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};

use super::{ProverData, VerifierData};
use crate::ir::term::text::parse_value_map;
use crate::ir::term::Value;

fn serialize_into_file<S: Serialize, P: AsRef<Path>>(data: &S, path: P) -> std::io::Result<()> {
    let mut file = BufWriter::new(File::create(path.as_ref())?);
    serialize_into(&mut file, data).unwrap();
    Ok(())
}

fn deserialize_from_file<D: for<'a> Deserialize<'a>, P: AsRef<Path>>(
    path: P,
) -> std::io::Result<D> {
    Ok(deserialize_from(BufReader::new(File::open(path.as_ref())?)).unwrap())
}

fn value_map_from_path<P: AsRef<Path>>(path: P) -> std::io::Result<HashMap<String, Value>> {
    Ok(parse_value_map(&std::fs::read(path)?))
}

/// A trait for CirC-compatible proofs
pub trait ProofSystem {
    /// A verifying key. Also used for commitments.
    type VerifyingKey: Serialize + for<'a> Deserialize<'a>;
    /// A proving key
    type ProvingKey: Serialize + for<'a> Deserialize<'a>;
    /// A proof
    type Proof: Serialize + for<'a> Deserialize<'a>;

    /// Setup
    fn setup(p_data: ProverData, v_data: VerifierData) -> (Self::ProvingKey, Self::VerifyingKey);
    /// Proving
    fn prove(pk: &Self::ProvingKey, witness: &HashMap<String, Value>) -> Self::Proof;
    /// Verification
    fn verify(vk: &Self::VerifyingKey, inst: &HashMap<String, Value>, pf: &Self::Proof) -> bool;

    /// Setup to files
    fn setup_fs(
        p_data: ProverData,
        v_data: VerifierData,
        pk_path: impl AsRef<Path>,
        vk_path: impl AsRef<Path>,
    ) -> std::io::Result<()> {
        let (pk, vk) = Self::setup(p_data, v_data);
        serialize_into_file(&pk, pk_path)?;
        serialize_into_file(&vk, vk_path)?;
        Ok(())
    }
    /// Prove to/from files
    fn prove_fs(
        pk_path: impl AsRef<Path>,
        witness_path: impl AsRef<Path>,
        pf_path: impl AsRef<Path>,
    ) -> std::io::Result<()> {
        let pk: Self::ProvingKey = deserialize_from_file(pk_path)?;
        let witness = value_map_from_path(witness_path)?;
        let pf = Self::prove(&pk, &witness);
        serialize_into_file(&pf, pf_path)
    }
    /// Verify from files
    fn verify_fs(
        vk_path: impl AsRef<Path>,
        instance_path: impl AsRef<Path>,
        pf_path: impl AsRef<Path>,
    ) -> std::io::Result<bool> {
        let instance = value_map_from_path(&instance_path)?;
        let vk: Self::VerifyingKey = deserialize_from_file(vk_path)?;
        let pf: Self::Proof = deserialize_from_file(pf_path)?;
        Ok(Self::verify(&vk, &instance, &pf))
    }
}

/// A commit-and-prove proof system.
pub trait CommitProofSystem {
    /// A verifying key. Also used for commitments.
    type VerifyingKey: Serialize + for<'a> Deserialize<'a>;
    /// A proving key
    type ProvingKey: Serialize + for<'a> Deserialize<'a>;
    /// A proof
    type Proof: Serialize + for<'a> Deserialize<'a>;
    /// A commitment to part of a witness.
    type Commitment: Serialize + for<'a> Deserialize<'a>;
    /// Randomness for a commitment.
    type ComRand: Serialize + for<'a> Deserialize<'a> + Default;
    /// Setup
    fn cp_setup(p_data: ProverData, v_data: VerifierData)
        -> (Self::ProvingKey, Self::VerifyingKey);
    /// Proving
    fn cp_prove(
        pk: &Self::ProvingKey,
        witness: &HashMap<String, Value>,
        rands: &[Self::ComRand],
    ) -> Self::Proof;
    /// Verification
    fn cp_verify(
        vk: &Self::VerifyingKey,
        inst: &HashMap<String, Value>,
        pf: &Self::Proof,
        cmts: &[Self::Commitment],
    ) -> bool;
    /// Commitment. The data should be a field-to-field array.
    fn cp_commit(vk: &Self::VerifyingKey, data: Value, rand: &Self::ComRand) -> Self::Commitment;
    /// Sample commitment randomness.
    fn sample_com_rand() -> Self::ComRand;

    /// Setup to files
    fn cp_setup_fs(
        p_data: ProverData,
        v_data: VerifierData,
        pk_path: impl AsRef<Path>,
        vk_path: impl AsRef<Path>,
    ) -> std::io::Result<()> {
        let (pk, vk) = Self::cp_setup(p_data, v_data);
        serialize_into_file(&pk, pk_path)?;
        serialize_into_file(&vk, vk_path)?;
        Ok(())
    }
    /// Prove to/from files
    fn cp_prove_fs(
        pk_path: impl AsRef<Path>,
        witness_path: impl AsRef<Path>,
        pf_path: impl AsRef<Path>,
        rand_paths: Vec<impl AsRef<Path>>,
    ) -> std::io::Result<()> {
        let pk: Self::ProvingKey = deserialize_from_file(pk_path)?;
        let witness = value_map_from_path(witness_path)?;
        let mut rands: Vec<Self::ComRand> = Vec::new();
        for p in rand_paths {
            rands.push(deserialize_from_file(p)?);
        }
        let pf = Self::cp_prove(&pk, &witness, &rands);
        serialize_into_file(&pf, pf_path)
    }
    /// Verify from files
    fn cp_verify_fs(
        vk_path: impl AsRef<Path>,
        instance_path: impl AsRef<Path>,
        pf_path: impl AsRef<Path>,
        cmt_paths: Vec<impl AsRef<Path>>,
    ) -> std::io::Result<bool> {
        let instance = value_map_from_path(instance_path)?;
        let vk: Self::VerifyingKey = deserialize_from_file(vk_path)?;
        let pf: Self::Proof = deserialize_from_file(pf_path)?;
        let mut cmts: Vec<Self::Commitment> = Vec::new();
        for p in cmt_paths {
            cmts.push(deserialize_from_file(p)?);
        }
        Ok(Self::cp_verify(&vk, &instance, &pf, &cmts))
    }
    /// Commitment. The data should be a field-to-field array.
    fn cp_commit_fs(
        vk_path: impl AsRef<Path>,
        data_path: impl AsRef<Path>,
        rand_path: impl AsRef<Path>,
        cmt_path: impl AsRef<Path>,
    ) -> std::io::Result<()> {
        let vk: Self::VerifyingKey = deserialize_from_file(vk_path)?;
        let data_map = value_map_from_path(data_path)?;
        assert_eq!(1, data_map.len());
        let data = data_map.into_iter().next().unwrap().1;
        let rand: Self::ComRand = deserialize_from_file(rand_path)?;
        let cmt = Self::cp_commit(&vk, data, &rand);
        serialize_into_file(&cmt, cmt_path)
    }
    /// Sample commitment randomness.
    fn sample_com_rand_fs(rand_path: impl AsRef<Path>) -> std::io::Result<()> {
        let r = Self::sample_com_rand();
        serialize_into_file(&r, rand_path)
    }
}

impl<P: CommitProofSystem> ProofSystem for P {
    type VerifyingKey = <P as CommitProofSystem>::VerifyingKey;
    type ProvingKey = <P as CommitProofSystem>::ProvingKey;
    type Proof = <P as CommitProofSystem>::Proof;

    fn setup(p_data: ProverData, v_data: VerifierData) -> (Self::ProvingKey, Self::VerifyingKey) {
        assert_eq!(
            0,
            p_data.num_commitments(),
            "This predicate has commitments---use a CP proof system"
        );
        assert_eq!(
            0,
            v_data.num_commitments(),
            "This predicate has commitments---use a CP proof system"
        );
        Self::cp_setup(p_data, v_data)
    }

    fn prove(pk: &Self::ProvingKey, witness: &HashMap<String, Value>) -> Self::Proof {
        Self::cp_prove(pk, witness, &[])
    }

    fn verify(vk: &Self::VerifyingKey, inst: &HashMap<String, Value>, pf: &Self::Proof) -> bool {
        Self::cp_verify(vk, inst, pf, &[])
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cfg::CircCfg;
    use crate::ir::term::*;
    use crate::target::r1cs;

    #[allow(dead_code)]
    fn test_setup_prove_verify<PS: ProofSystem>(
        cs: Computation,
        p_input: HashMap<String, Value>,
        v_input: HashMap<String, Value>,
    ) {
        let cfg = CircCfg::default();
        let r1cs = r1cs::trans::to_r1cs(&cs, &cfg);
        let (p_data, v_data) = r1cs.finalize(&cs);
        let (pk, vk) = PS::setup(p_data, v_data);
        let pf = PS::prove(&pk, &p_input);
        assert!(PS::verify(&vk, &v_input, &pf));
    }

    #[cfg(feature = "bellman")]
    mod mirage {
        use super::super::super::mirage::Mirage;
        use super::*;

        #[test]
        fn bool_np() {
            let c = text::parse_computation(
                b"
            (computation
                (metadata
                    (parties P)
                    (inputs (a bool (party 0)) (b bool (party 0)) (return bool))
                    (commitments)
                )
                (precompute
                    ((a bool) (b bool))
                    ((return bool))
                    (tuple (and a b))
                )
                (=  (and a b) return)
            )",
            );
            let p_input = text::parse_value_map(
                b"
            (let (
              (a true)
              (b true)
              ) false; ignored
              )",
            );
            let v_input = text::parse_value_map(
                b"
            (let (
              (return true)
              ) false; ignored
              )",
            );
            test_setup_prove_verify::<Mirage<bls12_381::Bls12>>(c, p_input, v_input);
        }

        #[test]
        fn rand_perm() {
            env_logger::try_init().ok();
            let c = text::parse_computation(
                b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (a0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (a1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (a2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (c (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                    )
                    (commitments)
                )
                (precompute () () (tuple))
                (=
                    (* (+ a0 c) (+ a1 c) (+ a2 c))
                    (* (+ b0 c) (+ b1 c) (+ b2 c))
                )
            )",
            );
            let p_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
                (a0 #f1)
                (a1 #f-1)
                (a2 #f4)
                (b0 #f-1)
                (b1 #f1)
                (b2 #f4)
                ) false))");
            let v_input = text::parse_value_map(
                b"
            (let (
              ) false; ignored
              )",
            );
            test_setup_prove_verify::<Mirage<bls12_381::Bls12>>(c, p_input, v_input);
        }

        #[test]
        fn rand_double_perm() {
            let c = text::parse_computation(
                b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (a0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (a1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (a2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (c (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                        (d (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                    )
                    (commitments)
                )
                (precompute () () (tuple))
                (and
                    (=
                        (* (+ a0 c) (+ a1 c) (+ a2 c))
                        (* (+ b0 c) (+ b1 c) (+ b2 c))
                    )
                    (=
                        (* (+ a0 d) (+ a1 d) (+ a2 d))
                        (* (+ b0 d) (+ b1 d) (+ b2 d))
                    )
                )
            )",
            );
            let p_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
                (a0 #f1)
                (a1 #f-1)
                (a2 #f4)
                (b0 #f-1)
                (b1 #f1)
                (b2 #f4)
                ) false))");
            let v_input = text::parse_value_map(
                b"
            (let (
              ) false; ignored
              )",
            );
            test_setup_prove_verify::<Mirage<bls12_381::Bls12>>(c, p_input, v_input);
        }

        #[test]
        fn rand_double_perm_inst() {
            let c = text::parse_computation(
                b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (a0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                        (a1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                        (a2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                        (b0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b1 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (b2 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (c (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                        (d (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                    )
                    (commitments)
                )
                (precompute () () (tuple))
                (and
                    (=
                        (* (+ a0 c) (+ a1 c) (+ a2 c))
                        (* (+ b0 c) (+ b1 c) (+ b2 c))
                    )
                    (=
                        (* (+ a0 d) (+ a1 d) (+ a2 d))
                        (* (+ b0 d) (+ b1 d) (+ b2 d))
                    )
                )
            )",
            );
            let p_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
                (a0 #f1)
                (a1 #f-1)
                (a2 #f4)
                (b0 #f-1)
                (b1 #f1)
                (b2 #f4)
                ) false))");
            let v_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
                (a0 #f1)
                (a1 #f-1)
                (a2 #f4)
              ) false; ignored
              ))",
            );
            test_setup_prove_verify::<Mirage<bls12_381::Bls12>>(c, p_input, v_input);
        }

        #[test]
        fn precomp_with_chall() {
            let c = text::parse_computation(
                b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (a0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0))
                        (ha (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (party 0) (round 1))
                        (d (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513) (random))
                    )
                    (commitments)
                )
                (precompute (
                    (a0 (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                ) (
                    (ha (mod 52435875175126190479447740508185965837690552500527637822603658699938581184513))
                ) (tuple
                    (* a0 d)
                ))
                    (=
                        ha
                        (* a0 d)
                    )
            )",
            );
            let p_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
                (a0 #f1)
                ) false))");
            let v_input = text::parse_value_map(
                b"
                (set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
            (let (
              ) false; ignored
              ))",
            );
            test_setup_prove_verify::<Mirage<bls12_381::Bls12>>(c, p_input, v_input);
        }
    }
}
