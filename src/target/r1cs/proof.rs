//! A trait for CirC-compatible proofs

use std::fs::File;
use std::path::Path;

use bincode::{deserialize_from, serialize_into};
use fxhash::FxHashMap as HashMap;
use serde::{Deserialize, Serialize};

use super::{ProverDataNew, VerifierDataNew};
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
    fn setup(
        p_data: ProverDataNew,
        v_data: VerifierDataNew,
    ) -> (Self::ProvingKey, Self::VerifyingKey);
    /// Proving
    fn prove(pk: &Self::ProvingKey, witness: &HashMap<String, Value>) -> Self::Proof;
    /// Verification
    fn verify(vk: &Self::VerifyingKey, inst: &HashMap<String, Value>, pf: &Self::Proof) -> bool;

    /// Setup to files
    fn setup_fs<P1, P2>(
        p_data: ProverDataNew,
        v_data: VerifierDataNew,
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
        let mut pk_file = File::open(pk_path)?;
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
        let mut vk_file = File::open(vk_path)?;
        let mut pf_file = File::open(pf_path)?;
        let instance_bytes = std::fs::read(instance_path)?;
        let instance = parse_value_map(&instance_bytes);
        let vk: Self::VerifyingKey = deserialize_from(vk_file).unwrap();
        let pf: Self::Proof = deserialize_from(pf_file).unwrap();
        Ok(Self::verify(&vk, &instance, &pf))
    }
}

#[cfg(test)]
mod test {
    // TODO: generic proof system test.
}
