//! Field type defaults
//
// NOTE: when we eventually break CirC into separate crates,
//       each crate may want its own field type default

#[cfg(all(not(feature = "ff_dfl"), not(feature = "ristretto255")))]
use circ_fields::moduli::*;
use circ_fields::FieldT;
#[cfg(not(feature = "ff_dfl"))]
use lazy_static::lazy_static;
#[cfg(feature = "ristretto255")]
use rug::Integer;

#[cfg(all(
    feature = "bls12381",
    not(feature = "bn254"),
    not(feature = "ristretto255"),
    feature = "ff_dfl"
))]
/// Default field
pub const DFL_T: FieldT = FieldT::FBls12381;
#[cfg(all(
    feature = "bls12381",
    not(feature = "bn254"),
    not(feature = "ristretto255"),
    not(feature = "ff_dfl")
))]
lazy_static! {
    /// Default field
    pub static ref DFL_T: FieldT = FieldT::IntField(F_BLS12381_FMOD_ARC.clone());
}

#[cfg(all(
    not(feature = "bls12381"),
    feature = "bn254",
    not(feature = "ristretto255"),
    feature = "ff_dfl"
))]
/// Default field
pub const DFL_T: FieldT = FieldT::FBn254;
#[cfg(all(
    not(feature = "bls12381"),
    feature = "bn254",
    not(feature = "ristretto255"),
    not(feature = "ff_dfl")
))]
lazy_static! {
    /// Default field
    pub static ref DFL_T: FieldT = FieldT::IntField(F_BN254_FMOD_ARC.clone());
}

#[cfg(all(
    not(feature = "bls12381"),
    not(feature = "bn254"),
    feature = "ristretto255"
))]
lazy_static! {
    /// Spartan modulus
    pub static ref RISTRETTO255_MOD: Integer = Integer::from_str_radix(
        "7237005577332262213973186563042994240857116359379907606001950938285454250989",
         10
    ).unwrap();
}
#[cfg(all(
    not(feature = "bls12381"),
    not(feature = "bn254"),
    feature = "ristretto255"
))]
lazy_static! {
    /// Default field
    pub static ref DFL_T: FieldT = FieldT::from(RISTRETTO255_MOD.clone());
}
