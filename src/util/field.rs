//! Field type defaults
//
// NOTE: when we eventually break CirC into separate crates,
//       each crate may want its own field type default

#[cfg(not(feature = "ff_dfl"))]
use circ_fields::moduli::*;
use circ_fields::FieldT;
#[cfg(not(feature = "ff_dfl"))]
use lazy_static::lazy_static;

#[cfg(all(feature = "bls12381", feature = "ff_dfl"))]
/// Default field
pub const DFL_T: FieldT = FieldT::FBls12381;
#[cfg(all(feature = "bls12381", not(feature = "ff_dfl")))]
lazy_static! {
    /// Default field
    pub static ref DFL_T: FieldT = FieldT::IntField(F_BLS12381_FMOD_ARC.clone());
}

#[cfg(all(not(feature = "bls12381"), feature = "ff_dfl"))]
/// Default field
pub const DFL_T: FieldT = FieldT::FBn254;
#[cfg(all(not(feature = "bls12381"), not(feature = "ff_dfl")))]
lazy_static! {
    /// Default field
    pub static ref DFL_T: FieldT = FieldT::IntField(F_BN254_FMOD_ARC.clone());
}
