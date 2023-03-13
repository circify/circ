use super::*;

use bls12_381::Bls12;
use group::Group;
use rand::{RngCore, SeedableRng};
use rand_chacha::ChaChaRng;

pub fn test_rng() -> Box<dyn RngCore> {
    Box::new(ChaChaRng::from_seed([0u8; 32]))
}

#[allow(clippy::type_complexity)]
/// Returns (common_ck, cks, common_cmts, cmts, data, common_rands, rands)
fn random_statement<E: Engine, R: RngCore>(
    num_cmts: usize,
    data_len: usize,
    mut rng: &mut R,
) -> (
    CommitKey<E>,
    Vec<CommitKey<E>>,
    Vec<E::G1Affine>,
    Vec<E::G1Affine>,
    Vec<Vec<E::Fr>>,
    Vec<E::Fr>,
    Vec<E::Fr>,
)
where
    E::Fr: PrimeFieldBits,
{
    let data: Vec<Vec<E::Fr>> = (0..num_cmts)
        .map(|_| (0..data_len).map(|_| E::Fr::random(&mut *rng)).collect())
        .collect();
    let common_rands: Vec<E::Fr> = (0..num_cmts).map(|_| E::Fr::random(&mut *rng)).collect();
    let rands: Vec<E::Fr> = (0..num_cmts).map(|_| E::Fr::random(&mut *rng)).collect();
    let common_ck = sample_ck(rng, data_len);
    let cks: Vec<CommitKey<E>> = (0..num_cmts)
        .map(|_| sample_ck(&mut *rng, data_len))
        .collect();
    let common_cmts: Vec<E::G1Affine> = data
        .iter()
        .zip(&common_rands)
        .map(|(v, r)| commit(common_ck.clone(), v.clone(), *r))
        .collect();
    let cmts: Vec<E::G1Affine> = data
        .iter()
        .zip(&common_rands)
        .zip(&cks)
        .map(|((v, r), ck)| commit(ck.clone(), v.clone(), *r))
        .collect();
    (common_ck, cks, common_cmts, cmts, data, common_rands, rands)
}

fn random_test<E>(num_cmts: usize, data_len: usize, iterations: usize)
where
    E: MultiMillerLoop,
    E::Fr: PrimeFieldBits,
{
    let rng = &mut test_rng();
    for _ in 0..iterations {
        let (common_ck, cks, common_cmts, cmts, data, common_rands, rands) =
            random_statement::<E, _>(num_cmts, data_len, rng);
        let (pk, vk) = key_gen(common_ck.clone(), cks.clone(), rng);
        let pf = prove(&pk, common_rands, rands, data);
        assert!(verify(&vk, common_cmts, cmts, &pf));
    }
}

#[test]
fn bls12_381_four_by_four() {
    random_test::<Bls12>(4, 4, 5);
}

#[test]
fn bls12_381_two_by_ten() {
    random_test::<Bls12>(2, 10, 5);
}

#[test]
fn bls12_381_zero_by_zero() {
    random_test::<Bls12>(0, 0, 5);
}
