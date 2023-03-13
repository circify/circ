//! A specialized implementation of pedersen commitments and CP link from LegoSNARK
//!
//! The (index) relation has the following components (we omit those related to commitment
//! randomness, for brevity):
//!
//! * index:
//!   * N: data len
//!   * C: number of commitments
//!   * common_ck: a single commitment key for data of length N
//!   * cks: C commitment keys for data of length N
//! * instance:
//!   * common_cmts: C commitments
//!   * cmts: C commitments
//! * witness:
//!   * data: C vectors of length N
//!
//! The relation holds when for i in 1..C:
//!
//! * common_cmts[i] = Commit(common_ck, data[i]) AND
//! * cmts[i] = Commit(cks[i], data[i])
//!
//! Thus, the relation "links" the commitments cmts under different keys to the commitments
//! common_cmts under the same key.
//!
//! ## Implementation details
//!
//! We build a matrix containing commit keys. Let N be the new data length and C be the number of
//! commitments. Our KW15 scheme is (0-)indexed as follows. The matrix is 2C by (N+2) C
//!
//! * For i in 0..C: commitment i is common_cmts[i]
//! * For i in 0..C: commitment C + i is cmts[i]
//! * For i in 0..C: for j in 0..N: scalar i * N + j is data[i][j]
//! * For i in 0..C: scalar N * C + i is common_rands[i]
//! * For i in 0..C: scalar N * C + C + i is rands[i]

use ff::{Field, PrimeFieldBits};
use group::Group;
use pairing::{Engine, MultiMillerLoop};
use rand::RngCore;
use serde::{Deserialize, Serialize};

use bellman::kw15;
use std::sync::Arc;

/// A commitment key (supporting commitment randomness)
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct CommitKey<E: Engine> {
    #[serde(with = "super::serde_group_vec")]
    pub data_keys: Vec<E::G1Affine>,
    #[serde(with = "super::serde_group")]
    pub rand_key: E::G1Affine,
}

/// For writing CP link proofs
#[derive(Serialize, Deserialize)]
pub struct ProvingKey<E: Engine> {
    data_len: usize,
    num_cmts: usize,
    #[serde(with = "super::serde_kw15_pk")]
    inner: kw15::ProvingKey<E>,
}

/// For verifying CP link proofs
#[derive(Serialize, Deserialize)]
pub struct VerifyingKey<E: Engine> {
    num_cmts: usize,
    #[serde(with = "super::serde_kw15_vk")]
    inner: kw15::VerifyingKey<E>,
}

/// A CP link proof
#[derive(Serialize, Deserialize)]
pub struct Proof<E: Engine> {
    #[serde(with = "super::serde_kw15_pf")]
    inner: kw15::Proof<E>,
}

/// Sample a commitment key
pub fn sample_ck<E: Engine, R: RngCore>(rng: &mut R, data_len: usize) -> CommitKey<E> {
    CommitKey {
        data_keys: (0..data_len)
            .map(|_| E::G1::random(&mut *rng).into())
            .collect(),
        rand_key: E::G1::random(&mut *rng).into(),
    }
}

/// Sample commitment randomness
pub fn sample_rand<E: Engine, R: RngCore>(rng: &mut R) -> E::Fr {
    E::Fr::random(rng)
}

/// Sample commitment randomness
pub fn commit<E: Engine>(mut ck: CommitKey<E>, mut data: Vec<E::Fr>, rand: E::Fr) -> E::G1Affine
where
    E::Fr: PrimeFieldBits,
{
    ck.data_keys.push(ck.rand_key);
    data.push(rand);
    kw15::commit::<E>(Arc::new(ck.data_keys), &data).into()
}

/// Generate keys for future CP link proofs.
///
/// ## Parameters
///
/// * `common_ck`: the common commitment key
/// * `cks`: different commitment keys
/// * `rng`: for randomness
pub fn key_gen<E, R>(
    common_ck: CommitKey<E>,
    cks: Vec<CommitKey<E>>,
    rng: &mut R,
) -> (ProvingKey<E>, VerifyingKey<E>)
where
    E: Engine,
    R: RngCore,
{
    for ci in &cks {
        assert_eq!(common_ck.data_keys.len(), ci.data_keys.len());
    }
    // data length, with randomness added
    let n = common_ck.data_keys.len();
    // number of commitments
    let c = cks.len();
    let mut matrix = kw15::Matrix::<E>::new(2 * c, (n + 2) * c);
    for (i, ck) in cks.into_iter().enumerate() {
        for j in 0..n {
            matrix.add_entry(i, n * i + j, common_ck.data_keys[j]);
            matrix.add_entry(c + i, n * i + j, ck.data_keys[j]);
        }
        matrix.add_entry(c, n * c + i, common_ck.rand_key);
        matrix.add_entry(c, n * c + c + i, ck.rand_key);
    }
    let (pk, vk) = kw15::key_gen(&matrix, rng);
    (
        ProvingKey {
            data_len: n,
            num_cmts: c,
            inner: pk,
        },
        VerifyingKey {
            num_cmts: c,
            inner: vk,
        },
    )
}

/// Create a CP link proof.
///
/// ## Parameters
///
/// * `pk`: from [key_gen]
/// * `common_rands`: a commitment randomness for each vector, for the commitment to that vector under the common key.
/// * `rands`: a commitment randomness for each vector, for the commitment to that vector under different keys.
/// * `datas`: each vector
pub fn prove<E>(
    pk: &ProvingKey<E>,
    common_rands: Vec<E::Fr>,
    rands: Vec<E::Fr>,
    datas: Vec<Vec<E::Fr>>,
) -> Proof<E>
where
    E: Engine,
    E::Fr: PrimeFieldBits,
{
    assert_eq!(pk.num_cmts, rands.len());
    assert_eq!(pk.num_cmts, datas.len());
    assert_eq!(pk.num_cmts, common_rands.len());
    for d in &datas {
        assert_eq!(pk.data_len, d.len());
    }
    let c = pk.num_cmts;
    let n = pk.data_len;
    let data: Vec<E::Fr> = datas
        .into_iter()
        .flatten()
        .chain(common_rands)
        .chain(rands)
        .collect();
    Proof {
        inner: kw15::prove(&pk.inner, &data),
    }
}

/// Verify a CP link proof.
///
/// ## Parameters
///
/// * `vk`: from [key_gen]
/// * `common_cmts`: commitments to the vectors, all under the same commitment key
/// * `cmts`: commitments to the vectors, under different commitment keys
/// * `pf`: the proof
pub fn verify<E>(
    vk: &VerifyingKey<E>,
    mut common_cmts: Vec<E::G1Affine>,
    cmts: Vec<E::G1Affine>,
    pf: &Proof<E>,
) -> bool
where
    E: MultiMillerLoop,
{
    assert_eq!(vk.num_cmts, common_cmts.len());
    assert_eq!(vk.num_cmts, cmts.len());
    common_cmts.extend(cmts);
    let pvk = kw15::PreparedVerifyingKey::from(&vk.inner);
    kw15::verify(&pvk, &common_cmts, &pf.inner)
}

#[cfg(test)]
mod test;
