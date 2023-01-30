//! A trait for CirC-compatible proofs

use std::fs::File;
use std::path::Path;

use bincode::{deserialize_from, serialize_into};
use fxhash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};

use super::{ProverData, VerifierData};
use crate::ir::term::text::parse_value_map;
use crate::ir::term::Value;

/// A trait for CirC-compatible proofs
pub trait ProofSystem {
    /// A verifying key
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
    fn setup_fs<P1, P2>(
        p_data: ProverData,
        v_data: VerifierData,
        pk_path: P1,
        vk_path: P2,
    ) -> std::io::Result<()>
    where
        P1: AsRef<Path>,
        P2: AsRef<Path>,
    {
        let (pk, vk) = Self::setup(p_data, v_data);
        let mut pk_file = File::create(pk_path)?;
        let mut vk_file = File::create(vk_path)?;
        serialize_into(&mut pk_file, &pk).unwrap();
        serialize_into(&mut vk_file, &vk).unwrap();
        Ok(())
    }
    /// Prove to/from files
    fn prove_fs<P1, P2>(pk_path: P1, witness_path: P2, pf_path: P2) -> std::io::Result<()>
    where
        P1: AsRef<Path>,
        P2: AsRef<Path>,
    {
        let pk_file = File::open(pk_path)?;
        let mut pf_file = File::create(pf_path)?;
        let witness_bytes = std::fs::read(witness_path)?;
        let witness = parse_value_map(&witness_bytes);
        let pk: Self::ProvingKey = deserialize_from(pk_file).unwrap();
        let pf = Self::prove(&pk, &witness);
        serialize_into(&mut pf_file, &pf).unwrap();
        Ok(())
    }
    /// Verify from files
    fn verify_fs<P1, P2>(vk_path: P1, instance_path: P2, pf_path: P2) -> std::io::Result<bool>
    where
        P1: AsRef<Path>,
        P2: AsRef<Path>,
    {
        let vk_file = File::open(vk_path)?;
        let pf_file = File::open(pf_path)?;
        let instance_bytes = std::fs::read(instance_path)?;
        let instance = parse_value_map(&instance_bytes);
        let vk: Self::VerifyingKey = deserialize_from(vk_file).unwrap();
        let pf: Self::Proof = deserialize_from(pf_file).unwrap();
        Ok(Self::verify(&vk, &instance, &pf))
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
