//! Exporting our R1CS to bellman

#![allow(unused_imports)]

use ark_ff::fields::PrimeField;
use ark_marlin::{rng::FiatShamirRng, IndexProverKey, IndexVerifierKey, Marlin, Proof};
use ark_poly::polynomial::univariate::DensePolynomial;
use ark_poly_commit::PolynomialCommitment;
use ark_relations::{
    lc,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Field, LinearCombination, Variable},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};

use bincode::{deserialize_from, serialize_into};
use digest::Digest;
use fxhash::FxHashMap;
use gmp_mpfr_sys::gmp::limb_t;
use group::WnafGroup;
use log::debug;
use std::collections::HashMap;
use std::error::Error;
use std::fs::File;
use std::io;
use std::path::Path;

use rug::integer::{IsPrime, Order};
use rug::Integer;

use super::*;

type ArkResult<T> = ark_relations::r1cs::Result<T>;

//#[derive(Debug, Clone, Serialize, Deserialize)]
///// A Rank 1 Constraint System.
//pub struct R1cs<S: Hash + Eq> {
//    modulus: FieldT,
//    signal_idxs: HashMap<S, usize>,
//    idxs_signals: HashMap<usize, S>,
//    next_idx: usize,
//    public_idxs: HashSet<usize>,
//    constraints: Vec<(Lc, Lc, Lc)>,
//    terms: Vec<Term>,
//}
/// Convert a (rug) integer to a prime field element.
fn int_to_ff<F: Field>(i: Integer) -> F {
    let mut accumulator = F::from(0u64);
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    let limb_base = F::from(2u64).pow(&[limb_bits]);
    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= limb_base;
        accumulator += F::from(*digit as u64);
    }
    accumulator
}

fn count_non_zeros(constraints: &[(Lc, Lc, Lc)]) -> usize {
    constraints.iter().fold(0, |acc, (ac, bc, cc)| {
        let acc = if ac.is_zero() { acc + 1 } else { acc };
        let acc = if bc.is_zero() { acc + 1 } else { acc };
        let acc = if cc.is_zero() { acc + 1 } else { acc };
        acc
    })
}

/// Convert one our our linear combinations to a bellman linear combination.
/// Takes a zero linear combination. We could build it locally, but bellman provides one, so...
fn lc_to_ark<F: Field>(vars: &HashMap<usize, Variable>, lc: &Lc) -> LinearCombination<F> {
    let mut lc_ark = lc!();
    lc_ark = lc_ark + (int_to_ff((&lc.constant).into()), Variable::One);
    for (v, c) in &lc.monomials {
        // ditto
        lc_ark = lc_ark + (int_to_ff(c.into()), *vars.get(v).unwrap());
    }
    lc_ark
}

/// A synthesizable marlin circuit.
///
/// Optionally contains a variable value map. This must be populated to use the
/// bellman prover.
/// OVERHAUL VLAUE MAP -> no longer makes sense
/// Value => closure?
pub struct SynthInput<'a>(&'a R1cs<String>, &'a Option<FxHashMap<String, Value>>);

impl<'a, F: Field> ConstraintSynthesizer<F> for SynthInput<'a> {
    #[track_caller]
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ArkResult<()> {
        let f_mod = Integer::from_digits(F::characteristic(), Order::Lsf);
        assert_eq!(
            self.0.modulus.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Marlin CS expects \n{}",
            self.0.modulus,
            f_mod
        );
        let mut uses = HashMap::with_capacity(self.0.next_idx);
        for (a, b, c) in self.0.constraints.iter() {
            [a, b, c].iter().for_each(|y| {
                y.monomials.keys().for_each(|k| {
                    uses.get_mut(k)
                        .map(|i| {
                            *i += 1;
                        })
                        .or_else(|| {
                            uses.insert(*k, 1);
                            None
                        });
                })
            });
        }
        let mut vars = HashMap::with_capacity(self.0.next_idx);
        for i in 0..self.0.next_idx {
            if let Some(s) = self.0.idxs_signals.get(&i) {
                //for (_i, s) in self.0.idxs_signals.get() {
                if uses.get(&i).is_some() {
                    let val_f = || {
                        Ok({
                            let i_val = self.1.as_ref().expect("missing values").get(s).unwrap();
                            let ff_val = int_to_ff(i_val.as_pf().into());
                            debug!("value : {} -> {:?} ({})", s, ff_val, i_val);
                            ff_val
                        })
                    };
                    let public = self.0.public_idxs.contains(&i);
                    debug!("var: {}, public: {}", s, public);
                    let v = if public {
                        // add epoch number
                        cs.new_input_variable(val_f)?
                    } else {
                        cs.new_witness_variable(val_f)?
                    };
                    ////
                    //cs.new_verifier_challenge(name? epoch_num)
                    vars.insert(i, v);
                } else {
                    debug!("drop dead var: {}", s);
                }
            }
        }
        for (_i, (a, b, c)) in self.0.constraints.iter().enumerate() {
            cs.enforce_constraint(
                lc_to_ark::<F>(&vars, a),
                lc_to_ark::<F>(&vars, b),
                lc_to_ark::<F>(&vars, c),
            )?;
        }
        debug!(
            "done with synth: {} vars {} cs",
            vars.len(),
            self.0.constraints.len()
        );
        Ok(())
    }
}

/// Given
/// * a proving-key path,
/// * a verifying-key path,
/// * prover data, and
/// * verifier data
/// generate parameters and write them and the data to files at those paths.
pub fn gen_params<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    P1: AsRef<Path>,
    P2: AsRef<Path>,
>(
    pk_path: P1,
    vk_path: P2,
    p_data: &ProverData,
    v_data: &VerifierData,
) -> Result<(), Box<dyn Error>> {
    let rng = &mut rand::thread_rng();
    let srs = Marlin::<F, PC, FS>::universal_setup(
        // TODO: without *2 this doesn't work for some reason... fix
        p_data.r1cs.constraints.len() * 2,
        p_data.r1cs.idxs_signals.len(),
        count_non_zeros(&p_data.r1cs.constraints),
        rng,
    )
    .unwrap();
    let (pk, vk) = Marlin::<F, PC, FS>::index(&srs, SynthInput(&p_data.r1cs, &None)).unwrap();
    write_prover_key_and_data(pk_path, &pk, p_data)?;
    write_verifier_key_and_data(vk_path, &vk, v_data)?;
    Ok(())
}

fn write_prover_key_and_data<
    P: AsRef<Path>,
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
>(
    path: P,
    prover_key: &IndexProverKey<F, PC>,
    data: &ProverData,
) -> Result<(), Box<dyn Error>> {
    let mut pk: Vec<u8> = Vec::new();
    prover_key.serialize(&mut pk)?;
    let mut file = File::create(path)?;
    serialize_into(&mut file, &(&pk, &data)).unwrap();
    Ok(())
}

fn read_prover_key_and_data<
    P: AsRef<Path>,
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
>(
    path: P,
) -> Result<(IndexProverKey<F, PC>, ProverData), Box<dyn Error>> {
    let mut file = File::open(path)?;
    let (pk_bytes, data): (Vec<u8>, ProverData) = deserialize_from(&mut file).unwrap();
    let pk = IndexProverKey::<F, PC>::deserialize(pk_bytes.as_slice())?;
    Ok((pk, data))
}

fn write_verifier_key_and_data<
    P: AsRef<Path>,
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
>(
    path: P,
    key: &IndexVerifierKey<F, PC>,
    data: &VerifierData,
) -> Result<(), Box<dyn Error>> {
    let mut vk: Vec<u8> = Vec::new();
    key.serialize(&mut vk)?;
    let mut file = File::create(path)?;
    serialize_into(&mut file, &(&vk, &data)).unwrap();
    Ok(())
}

fn read_verifier_key_and_data<
    P: AsRef<Path>,
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
>(
    path: P,
) -> Result<(IndexVerifierKey<F, PC>, VerifierData), Box<dyn Error>> {
    let mut file = File::open(path)?;
    let (vk_bytes, data): (Vec<u8>, VerifierData) = deserialize_from(&mut file).unwrap();
    let vk = IndexVerifierKey::<F, PC>::deserialize(vk_bytes.as_slice())?;
    Ok((vk, data))
}

/// Given
/// * a proving-key path,
/// * a proof path, and
/// * a prover input map
/// generate a random proof and writes it to the path
pub fn prove<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    P1: AsRef<Path>,
    P2: AsRef<Path>,
>(
    pk_path: P1,
    pf_path: P2,
    inputs_map: &FxHashMap<String, Value>,
) -> Result<(), Box<dyn Error>> {
    let (pk, prover_data) = read_prover_key_and_data::<_, F, PC>(pk_path)?;
    let rng = &mut rand::thread_rng();
    for (input, (sort, _epoch)) in &prover_data.precompute_inputs {
        let value = inputs_map
            .get(input)
            .unwrap_or_else(|| panic!("No input for {}", input));
        let sort2 = value.sort();
        assert_eq!(
            sort, &sort2,
            "Sort mismatch for {}. Expected\n\t{} but got\n\t{}",
            input, sort, sort2
        );
    }
    let new_map = prover_data.precompute.eval(inputs_map);
    prover_data.r1cs.check_all(&new_map);
    let pf = Marlin::<F, PC, FS>::prove(&pk, SynthInput(&prover_data.r1cs, &Some(new_map)), rng)
        .unwrap();
    let mut pf_file = File::create(pf_path)?;
    pf.serialize(&mut pf_file)?;
    Ok(())
}

/// Given
/// * a verifying-key path,
/// * a proof path,
/// * and a verifier input map
/// checks the proof at that path
pub fn verify<
    F: PrimeField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    P1: AsRef<Path>,
    P2: AsRef<Path>,
>(
    vk_path: P1,
    pf_path: P2,
    inputs_map: &FxHashMap<String, Value>,
) -> Result<(), Box<dyn Error>> {
    let (vk, verifier_data) = read_verifier_key_and_data::<_, F, PC>(vk_path)?;
    let rng = &mut rand::thread_rng();
    //let pvk = prepare_verifying_key(&vk);
    let inputs = verifier_data.eval(inputs_map);
    let inputs_as_ff: Vec<F> = inputs.into_iter().map(int_to_ff).collect();
    let mut pf_file = File::open(pf_path).unwrap();
    let pf = Proof::deserialize(&mut pf_file).unwrap();
    Marlin::<F, PC, FS>::verify(&vk, &inputs_as_ff, &pf, rng).unwrap();
    Ok(())
}
