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

fn val_to_scalar(v: &Value) -> Scalar {
    match v.sort() {
        Sort::Field(_) => return int_to_scalar(&v.as_pf().i()),
        _ => panic!("Underlying value should be a field")
    };

}

fn int_to_scalar(i: &Integer) -> Scalar {
    let mut accumulator = Scalar::zero();
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    assert_eq!(limb_bits, 64);

    let two: u64 = 2;
    let mut m = Scalar::from(two.pow(63) as u64);
    m = m * Scalar::from(2 as u64);

    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= m;
        accumulator += Scalar::from(*digit as u64);
    }
    return accumulator;

}

// circ Lc (const, monomials <Integer>) -> Vec<Variable>
fn lc_to_v(lc: &Lc, const_id: usize, trans: &HashMap<usize,usize>) -> Vec<Variable> {
    let mut v: Vec<Variable> = Vec::new();

    for (k,m) in &lc.monomials {
        let scalar = int_to_scalar(&m.i());

        let var = Variable {
            sid: trans.get(k).unwrap().clone(),
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    if lc.constant.i() != Integer::from(0 as u32) {
        let scalar = int_to_scalar(&lc.constant.i());
        let var = Variable {
            sid: const_id,
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    v
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
    

    //let pf = create_random_proof(SynthInput(&prover_data.r1cs, &Some(new_map)), &pk, rng).unwrap();
    let mut prover_transcript = Transcript::new(b"nizk_transcript");
    let pf = NIZK::prove(inst, witness, inputs, &gens, &mut prover_transcript);

    let mut pf_file = File::create(pf_path)?;
    //pf.write(&mut pf_file)?;
    let buf = bincode::serialize_into(&pf)?;
    pf_file.write_all(&buf[..])?;

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
    
    //let pf = Proof::read(&mut pf_file).unwrap();
    //verify_proof(&pvk, &pf, &inputs_as_ff).unwrap();
    let pf = bincode::deserialize_from(&buf[..]).unwrap()
    let mut verifier_transcript = Transcript::new(b"nizk_example");
    assert!(proof.verify(&inst, inputs, &mut verifier_transcript, gens).is_ok());

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
