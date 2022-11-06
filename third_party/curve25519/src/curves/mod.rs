use crate::{Fq, Fr};
use ark_ec::{
    models::CurveConfig,
    twisted_edwards::{Affine, MontCurveConfig, MontgomeryAffine, Projective, TECurveConfig},
};
use ark_ff::MontFp;

#[cfg(test)]
mod tests;

pub type EdwardsAffine = Affine<EdwardsParameters>;
pub type EdwardsProjective = Projective<EdwardsParameters>;
pub type NonZeroMontgomeryAffine = MontgomeryAffine<EdwardsParameters>;

#[derive(Clone, Default, PartialEq, Eq)]
pub struct EdwardsParameters;

impl CurveConfig for EdwardsParameters {
    type BaseField = Fq;
    type ScalarField = Fr;

    /// COFACTOR = 8
    const COFACTOR: &'static [u64] = &[8];

    /// COFACTOR_INV (mod r) =
    /// 2713877091499598330239944961141122840321418634767465352250731601857045344121
    const COFACTOR_INV: Fr =
        MontFp!("2713877091499598330239944961141122840321418634767465352250731601857045344121");
}

// We want to emphasize that this twisted Edwards curve is not ed25519.
impl TECurveConfig for EdwardsParameters {
    /// COEFF_A = 486664
    const COEFF_A: Fq = MontFp!("486664");

    /// COEFF_D = 486660
    const COEFF_D: Fq = MontFp!("486660");

    /// Generated randomly
    const GENERATOR: EdwardsAffine = EdwardsAffine::new_unchecked(GENERATOR_X, GENERATOR_Y);

    type MontCurveConfig = EdwardsParameters;
}

impl MontCurveConfig for EdwardsParameters {
    /// COEFF_A = 486662
    const COEFF_A: Fq = MontFp!("486662");

    /// COEFF_B = 1
    const COEFF_B: Fq = MontFp!("1");

    type TECurveConfig = EdwardsParameters;
}

/// GENERATOR_X =
/// 38213832894368730265794714087330135568483813637251082400757400312561599933396
const GENERATOR_X: Fq =
    MontFp!("38213832894368730265794714087330135568483813637251082400757400312561599933396");

/// GENERATOR_Y =
/// (4/5)
/// 46316835694926478169428394003475163141307993866256225615783033603165251855960
const GENERATOR_Y: Fq =
    MontFp!("46316835694926478169428394003475163141307993866256225615783033603165251855960");
