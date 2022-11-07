//! Exporting our R1CS to bellman
use ::bellman::{
    groth16::{
        create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof,
        Parameters, Proof, VerifyingKey,
    },
    Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable,
};
use bincode::{deserialize_from, serialize_into};
use ff::{Field, PrimeField, PrimeFieldBits};
use fxhash::FxHashMap;
use gmp_mpfr_sys::gmp::limb_t;
use group::WnafGroup;
use log::debug;
use pairing::{Engine, MultiMillerLoop};
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::Path;
use std::str::FromStr;

use rug::integer::{IsPrime, Order};
use rug::Integer;

use super::*;

/// Convert a (rug) integer to a prime field element.
fn int_to_ff<F: PrimeField>(i: Integer) -> F {
    let mut accumulator = F::from(0);
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    let limb_base = F::from(2).pow_vartime([limb_bits]);
    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= limb_base;
        accumulator += F::from(*digit);
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
fn get_modulus<F: Field + PrimeField>() -> Integer {
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
pub struct SynthInput<'a>(&'a R1cs<String>, &'a Option<FxHashMap<String, Value>>);

impl<'a, F: PrimeField> Circuit<F> for SynthInput<'a> {
    #[track_caller]
    fn synthesize<CS>(self, cs: &mut CS) -> std::result::Result<(), SynthesisError>
    where
        CS: ConstraintSystem<F>,
    {
        let f_mod = get_modulus::<F>();
        assert_eq!(
            self.0.modulus.modulus(),
            &f_mod,
            "\nR1CS has modulus \n{},\n but Bellman CS expects \n{}",
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
                    let name_f = || s.to_string();
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
        for (i, (a, b, c)) in self.0.constraints.iter().enumerate() {
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
            self.0.constraints.len()
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

/// Given
/// * a proving-key path,
/// * a verifying-key path,
/// * prover data, and
/// * verifier data
/// generate parameters and write them and the data to files at those paths.
pub fn gen_params<E: Engine, P1: AsRef<Path>, P2: AsRef<Path>>(
    pk_path: P1,
    vk_path: P2,
    p_data: &ProverData,
    v_data: &VerifierData,
) -> io::Result<()>
where
    E::G1: WnafGroup,
    E::G2: WnafGroup,
{
    let rng = &mut rand::thread_rng();
    let p = generate_random_parameters::<E, _, _>(SynthInput(&p_data.r1cs, &None), rng).unwrap();
    write_prover_key_and_data(pk_path, &p, p_data)?;
    write_verifier_key_and_data(vk_path, &p.vk, v_data)?;
    Ok(())
}

fn write_prover_key_and_data<P: AsRef<Path>, E: Engine>(
    path: P,
    params: &Parameters<E>,
    data: &ProverData,
) -> io::Result<()> {
    let mut pk: Vec<u8> = Vec::new();
    params.write(&mut pk)?;
    let mut file = File::create(path)?;
    serialize_into(&mut file, &(&pk, &data)).unwrap();
    Ok(())
}

fn read_prover_key_and_data<P: AsRef<Path>, E: Engine>(
    path: P,
) -> io::Result<(Parameters<E>, ProverData)> {
    let mut file = File::open(path)?;
    let (pk_bytes, data): (Vec<u8>, ProverData) = deserialize_from(&mut file).unwrap();
    let pk: Parameters<E> = Parameters::read(pk_bytes.as_slice(), false)?;
    Ok((pk, data))
}

fn write_verifier_key_and_data<P: AsRef<Path>, E: Engine>(
    path: P,
    key: &VerifyingKey<E>,
    data: &VerifierData,
) -> io::Result<()> {
    let mut vk: Vec<u8> = Vec::new();
    key.write(&mut vk)?;
    let mut file = File::create(path)?;
    serialize_into(&mut file, &(&vk, &data)).unwrap();
    Ok(())
}

fn read_verifier_key_and_data<P: AsRef<Path>, E: Engine>(
    path: P,
) -> io::Result<(VerifyingKey<E>, VerifierData)> {
    let mut file = File::open(path)?;
    let (vk_bytes, data): (Vec<u8>, VerifierData) = deserialize_from(&mut file).unwrap();
    let vk: VerifyingKey<E> = VerifyingKey::read(vk_bytes.as_slice())?;
    Ok((vk, data))
}

/// Given
/// * a proving-key path,
/// * a proof path, and
/// * a prover input map
/// generate a random proof and writes it to the path
pub fn prove<E: Engine, P1: AsRef<Path>, P2: AsRef<Path>>(
    pk_path: P1,
    pf_path: P2,
    inputs_map: &FxHashMap<String, Value>,
) -> io::Result<()>
where
    E::Fr: PrimeFieldBits,
{
    let (pk, prover_data) = read_prover_key_and_data::<_, E>(pk_path)?;
    let rng = &mut rand::thread_rng();
    for (input, sort) in &prover_data.precompute_inputs {
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
    let pf = create_random_proof(SynthInput(&prover_data.r1cs, &Some(new_map)), &pk, rng).unwrap();
    let mut pf_file = File::create(pf_path)?;
    pf.write(&mut pf_file)?;
    Ok(())
}

/// Given
/// * a verifying-key path,
/// * a proof path,
/// * and a verifier input map
/// checks the proof at that path
pub fn verify<E: MultiMillerLoop, P1: AsRef<Path>, P2: AsRef<Path>>(
    vk_path: P1,
    pf_path: P2,
    inputs_map: &FxHashMap<String, Value>,
) -> io::Result<()> {
    let (vk, verifier_data) = read_verifier_key_and_data::<_, E>(vk_path)?;
    let pvk = prepare_verifying_key(&vk);
    let inputs = verifier_data.eval(inputs_map);
    let inputs_as_ff: Vec<E::Fr> = inputs.into_iter().map(int_to_ff).collect();
    let mut pf_file = File::open(pf_path).unwrap();
    let pf = Proof::read(&mut pf_file).unwrap();
    verify_proof(&pvk, &pf, &inputs_as_ff).unwrap();
    Ok(())
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
        let by_str = Scalar::from_str_vartime(&format!("{}", i)).unwrap();
        by_fn == by_str
    }

    fn convert(i: Integer) {
        let by_fn = int_to_ff::<Scalar>(i.clone());
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
