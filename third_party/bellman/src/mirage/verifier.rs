use group::{prime::PrimeCurveAffine, Curve};
use pairing::{MillerLoopResult, MultiMillerLoop};
use std::ops::{AddAssign, Neg};

use super::{PreparedVerifyingKey, Proof, VerifyingKey};

use crate::VerificationError;

pub mod batch;

pub fn prepare_verifying_key<E: MultiMillerLoop>(vk: &VerifyingKey<E>) -> PreparedVerifyingKey<E> {
    let gamma = vk.gamma_g2.neg();
    let delta = vk.delta_g2.neg();
    let deltap = vk.deltap_g2.neg();

    PreparedVerifyingKey {
        alpha_g1_beta_g2: E::pairing(&vk.alpha_g1, &vk.beta_g2),
        neg_gamma_g2: gamma.into(),
        neg_delta_g2: delta.into(),
        neg_deltap_g2: deltap.into(),
        ic: vk.ic.clone(),
        num_coins: vk.num_coins,
    }
}

pub fn verify_proof<'a, E: MultiMillerLoop>(
    pvk: &'a PreparedVerifyingKey<E>,
    proof: &Proof<E>,
    public_inputs: &[E::Fr],
) -> Result<(), VerificationError> {
    if (public_inputs.len() + pvk.num_coins + 1) != pvk.ic.len() {
        println!(
            "got {} inputs and {} coins, expect total to be {}",
            public_inputs.len(),
            pvk.num_coins,
            pvk.ic.len() - 1
        );
        return Err(VerificationError::InvalidVerifyingKey);
    }

    let mut all_inputs = public_inputs.to_vec();
    // re-generate proof coins
    for i in 0..pvk.num_coins {
        use ff::Field;
        // we use 1 when computing coins... so add it back...
        let coin = super::compute_coin::<E, E::Fr>(
            &[&[E::Fr::one()][..], &public_inputs].concat(),
            proof.d,
            i,
        );
        all_inputs.push(coin);
        //assert_eq!(coin, *c);
    }

    let mut acc = pvk.ic[0].to_curve();

    //let all_inputs = [public_inputs, &proof.coins].concat();

    for (i, b) in all_inputs.iter().zip(pvk.ic.iter().skip(1)) {
        AddAssign::<&E::G1>::add_assign(&mut acc, &(*b * i));
    }

    // The original verification equation is:
    // A * B = alpha * beta + inputs * gamma + C * delta
    // ... however, we rearrange it so that it is:
    // A * B - inputs * gamma - C * delta = alpha * beta
    // or equivalently:
    // A * B + inputs * (-gamma) + C * (-delta) = alpha * beta
    // which allows us to do a single final exponentiation.

    if pvk.alpha_g1_beta_g2
        == E::multi_miller_loop(&[
            (&proof.a, &proof.b.into()),
            (&acc.to_affine(), &pvk.neg_gamma_g2),
            (&proof.c, &pvk.neg_delta_g2),
            (&proof.d, &pvk.neg_deltap_g2),
        ])
        .final_exponentiation()
    {
        Ok(())
    } else {
        Err(VerificationError::InvalidProof)
    }
}
