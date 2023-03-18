//! Fields for use in CirC

#![warn(missing_docs)]
#![deny(warnings)]

mod ff_field;
mod int_field;

/// Exports for moduli defined in this crate, as ARCs
pub mod moduli {
    pub use super::ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
}

use ark_curve25519::Fr;
use ark_ff::PrimeField;
use ark_ff::{BigInt, BigInteger, Field as ark_Field};
use ff_field::{FBls12381, FBn254};
use ff_field::{F_BLS12381_FMOD, F_BN254_FMOD};
use ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
use int_field::IntField;
use lazy_static::lazy_static;
use num_traits::Zero;

use ff::Field;
use paste::paste;
use rand::distributions::Standard;
use rand::prelude::Distribution;
use rug::integer::Order;
use rug::Integer;
use serde::de::Visitor;
use serde::ser::Error;
use serde::{Deserialize, Serialize};
use std::fmt::{self, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::sync::Arc;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

// TODO: rework this using macros?

/// Field element type
#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FieldT {
    /// BLS12-381 scalar field as `ff`
    FBls12381,
    /// BN-254 scalar field as `ff`
    FBn254,
    /// FCurve25519
    FCurve25519,
    /// Generic field element based on `rug::Integer`
    IntField(Arc<Integer>),
}

lazy_static! {
    /// Field modulus
    pub static ref F_CURVE25519_FMOD: Integer = Integer::from_digits(&Fr::MODULUS.to_bytes_be(), Order::MsfBe);
    /// Field modulus arc
    pub static ref F_CURVE25519_FMOD_ARC: Arc<Integer> = Arc::new(F_CURVE25519_FMOD.clone());
}

impl Display for FieldT {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::FCurve25519 => write!(f, "FieldT::FCurve25519"),
            Self::FBls12381 => write!(f, "FieldT::FBls12381"),
            Self::FBn254 => write!(f, "FieldT::FBn254"),
            Self::IntField(m) => write!(f, "FieldT::(mod {})", &*m),
        }
    }
}

impl From<Arc<Integer>> for FieldT {
    fn from(m: Arc<Integer>) -> Self {
        Self::as_ff_opt(m.as_ref()).unwrap_or(Self::IntField(m))
    }
}

impl From<Integer> for FieldT {
    fn from(m: Integer) -> Self {
        Self::as_ff_opt(&m).unwrap_or_else(|| Self::IntField(Arc::new(m)))
    }
}

impl From<&Integer> for FieldT {
    fn from(m: &Integer) -> Self {
        Self::as_ff_opt(m).unwrap_or_else(|| Self::IntField(Arc::new(m.clone())))
    }
}

impl FieldT {
    // Returns a FieldT if this modulus can be represented as `ff`, `None` otherwise.
    fn as_ff_opt(m: &Integer) -> Option<Self> {
        match m {
            m if m == &*F_BLS12381_FMOD => Some(Self::FBls12381),
            m if m == &*F_BN254_FMOD => Some(Self::FBn254),
            m if m == &*F_CURVE25519_FMOD => Some(Self::FCurve25519),
            _ => None,
        }
    }

    /// Field modulus
    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self {
            Self::FCurve25519 => &*F_CURVE25519_FMOD,
            Self::FBls12381 => &*F_BLS12381_FMOD,
            Self::FBn254 => &*F_BN254_FMOD,
            Self::IntField(m) => m.as_ref(),
        }
    }

    /// Field modulus as an ARC
    #[inline]
    pub fn modulus_arc(&self) -> Arc<Integer> {
        match self {
            Self::FCurve25519 => F_CURVE25519_FMOD_ARC.clone(),
            Self::FBls12381 => F_BLS12381_FMOD_ARC.clone(),
            Self::FBn254 => F_BN254_FMOD_ARC.clone(),
            Self::IntField(m) => m.clone(),
        }
    }

    /// Default value for this type
    #[inline]
    pub fn default_value(&self) -> FieldV {
        match self {
            Self::FCurve25519 => FieldV::FCurve25519(FCurve25519(Fr::zero())),
            Self::FBls12381 => FieldV::FBls12381(Default::default()),
            Self::FBn254 => FieldV::FBn254(Default::default()),
            Self::IntField(m) => FieldV::IntField(IntField::new(Integer::from(0), m.clone())),
        }
    }

    /// Zero for this type
    #[inline]
    pub fn zero(&self) -> FieldV {
        self.default_value()
    }

    /// Random value of this type
    #[inline]
    pub fn random_v(&self, rng: impl rand::RngCore) -> FieldV {
        FieldV::random(self.clone(), rng)
    }

    /// New value of this type
    #[inline]
    pub fn new_v<I>(&self, i: I) -> FieldV
    where
        Integer: From<I>,
    {
        FieldV::new_ty(i, self.clone())
    }
}

/// Field element value
#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FieldV {
    /// BLS12-381 scalar field element as `ff`
    FBls12381(FBls12381),
    /// BN-254 scalar field element as `ff`
    FBn254(FBn254),
    /// FCurve25519
    FCurve25519(FCurve25519),
    /// Generic field element based on `rug::Integer`
    IntField(IntField),
}

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash)]
/// field for curve25519
pub struct FCurve25519(pub Fr);

impl Serialize for FCurve25519 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut bytes = Vec::<u8>::new();
        if let Err(_) = self.0.serialize_uncompressed(&mut bytes) {
            return Err(S::Error::custom("serialize uncompressed error!"))
        };
        serializer.serialize_bytes(&bytes)
    }
}

impl<'de> Deserialize<'de> for FCurve25519 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct MyFrVisitor;

        impl<'de> Visitor<'de> for MyFrVisitor {
            type Value = FCurve25519;
            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                let f: Fr = CanonicalDeserialize::deserialize_uncompressed(v).unwrap();
                Ok(FCurve25519(f))
            }

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct MyFr")
            }
        }

        deserializer.deserialize_bytes(MyFrVisitor)
    }
}

impl FieldV {
    /// Type of this value
    #[inline]
    pub fn ty(&self) -> FieldT {
        match self {
            Self::FCurve25519(_) => FieldT::FCurve25519,
            Self::FBls12381(_) => FieldT::FBls12381,
            Self::FBn254(_) => FieldT::FBn254,
            Self::IntField(i) => FieldT::IntField(i.modulus_arc()),
        }
    }

    /// New field element from value and modulus.
    ///
    /// This function uses `FieldT::from`, which means that if there is
    /// an `ff` implementation available it will return that, otherwise
    /// it will use a `rug::Integer` implementation.
    #[inline]
    pub fn new<I>(i: I, m: Arc<Integer>) -> Self
    where
        Integer: From<I>,
    {
        Self::new_ty(i, FieldT::from(m))
    }

    /// Check that a value is well formed
    #[track_caller]
    #[inline]
    pub fn check(&self, loc: &str) {
        if let Self::IntField(m) = self {
            m.check(loc);
        }
    }

    /// Field modulus as `&rug::Integer`
    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self {
            Self::FCurve25519(_) => &*F_CURVE25519_FMOD,
            Self::FBls12381(_) => &*F_BLS12381_FMOD,
            Self::FBn254(_) => &*F_BN254_FMOD,
            Self::IntField(i) => i.modulus(),
        }
    }

    /// Compute the multiplicative inverse (panics on 0)
    #[track_caller]
    #[inline]
    pub fn recip_ref(&self) -> Self {
        match self {
            Self::FCurve25519(pf) => Self::FCurve25519(FCurve25519(pf.0.inverse().unwrap())),
            Self::FBls12381(pf) => Self::FBls12381(pf.invert().unwrap()),
            Self::FBn254(pf) => Self::FBn254(pf.invert().unwrap()),
            Self::IntField(i) => Self::IntField(i.clone().recip()),
        }
    }

    /// Ccompute the multiplicative inverse (panics on 0)
    #[track_caller]
    #[inline]
    pub fn recip(self) -> Self {
        match self {
            Self::FCurve25519(pf) => Self::FCurve25519(FCurve25519(pf.0.inverse().unwrap())),
            Self::FBls12381(pf) => Self::FBls12381(pf.invert().unwrap()),
            Self::FBn254(pf) => Self::FBn254(pf.invert().unwrap()),
            Self::IntField(i) => Self::IntField(i.recip()),
        }
    }

    /// Get value as an integer
    #[inline]
    pub fn i(&self) -> Integer {
        self.into()
    }

    /// Test if value is zero
    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::FCurve25519(pf) => pf.0.is_zero(),
            Self::FBls12381(pf) => bool::from(ff::Field::is_zero(pf)),
            Self::FBn254(pf) => bool::from(ff::Field::is_zero(pf)),
            Self::IntField(i) => i.is_zero(),
        }
    }

    /// Test if value is 1
    #[inline]
    pub fn is_one(&self) -> bool {
        use num_traits::One;
        match self {
            Self::FCurve25519(pf) => pf.0.is_one(),
            Self::FBls12381(pf) => pf.is_one(),
            Self::FBn254(pf) => pf.is_one(),
            Self::IntField(i) => i.i == 1,
        }
    }

    #[inline]
    fn new_ty<I>(i: I, ty: FieldT) -> Self
    where
        Integer: From<I>,
    {
        let i = Integer::from(i);
        match ty {
            FieldT::FCurve25519 => {
                let i = BigInt::from_bits_be(&i.to_digits(Order::MsfBe));
                Self::FCurve25519(FCurve25519(Fr::from_bigint(i).unwrap()))
            }
            FieldT::FBls12381 => Self::FBls12381(FBls12381::from(i)),
            FieldT::FBn254 => Self::FBn254(FBn254::from(i)),
            FieldT::IntField(m) => Self::IntField(IntField::new(i, m)),
        }
    }

    fn random(ty: FieldT, mut rng: impl rand::RngCore) -> Self {
        match ty {
            FieldT::FCurve25519 => Self::FCurve25519(FCurve25519(Standard.sample(&mut rng))),
            FieldT::FBls12381 => Self::FBls12381(FBls12381::random(rng)),
            FieldT::FBn254 => Self::FBn254(FBn254::random(rng)),
            FieldT::IntField(m) => {
                let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
                rug_rng.seed(&Integer::from(rng.next_u64()));
                let i = Integer::from(m.random_below_ref(&mut rug_rng));
                Self::IntField(IntField::new(i, m))
            }
        }
    }

    /// Convert to a different FieldT --- will fail if moduli are not the same!
    #[track_caller]
    #[inline]
    pub fn as_ty_ref(&self, ty: &FieldT) -> Self {
        if &self.ty() == ty {
            self.clone()
        } else if self.modulus() != ty.modulus() {
            panic!(
                "Incompatible modulus specified: {:#?} vs {:#?}",
                self.ty(),
                ty,
            );
        } else {
            ty.new_v(self.i())
        }
    }
}

impl Display for FieldV {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::FCurve25519(pf) => pf.0.fmt(f),
            Self::FBls12381(pf) => write!(f, "#f{}m{}", Integer::from(pf), &*F_BLS12381_FMOD),
            Self::FBn254(pf) => write!(f, "#f{}m{}", Integer::from(pf), &*F_BN254_FMOD),
            Self::IntField(i) => i.fmt(f),
        }
    }
}

macro_rules! arith_impl {
    ($Trait: ident, $fn: ident) => {
        paste! {
            impl $Trait<FieldV> for FieldV {
                type Output = Self;
                fn $fn(mut self, other: Self) -> Self {
                    self.[<$fn _assign>](&other);
                    self
                }
            }

            impl $Trait<&FieldV> for FieldV {
                type Output = Self;
                fn $fn(mut self, other: &Self) -> Self {
                    self.[<$fn _assign>](other);
                    self
                }
            }

            impl [<$Trait Assign>]<&FieldV> for FieldV {
                fn [<$fn _assign>](&mut self, other: &FieldV) {
                    match (self, other) {
                        (Self::FBls12381(f1), Self::FBls12381(f2)) => f1.[<$fn _assign>](f2),
                        (Self::FBn254(f1), Self::FBn254(f2)) => f1.[<$fn _assign>](f2),
                        (Self::IntField(i1), Self::IntField(i2)) => i1.[<$fn _assign>](i2),
                        (Self::FCurve25519(i1), Self::FCurve25519(i2)) => i1.0.[<$fn _assign>](i2.0),
                        (s, o) => panic!("Operation [<$Trait Assign>] on {} and {}", s.ty(), o.ty()),
                    }
                }
            }

            impl [<$Trait Assign>]<FieldV> for FieldV {
                fn [<$fn _assign>](&mut self, other: FieldV) {
                    self.[<$fn _assign>](&other);
                }
            }
        }
    }
}

arith_impl!(Add, add);
arith_impl!(Mul, mul);
arith_impl!(Sub, sub);

impl Neg for FieldV {
    type Output = Self;
    fn neg(self) -> Self {
        match self {
            Self::FCurve25519(pf) => Self::FCurve25519(FCurve25519(pf.0.neg())),
            Self::FBls12381(pf) => Self::FBls12381(pf.neg()),
            Self::FBn254(pf) => Self::FBn254(pf.neg()),
            Self::IntField(i) => Self::IntField(i.neg()),
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<FieldV> for FBls12381 {
    fn into(self) -> FieldV {
        FieldV::FBls12381(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<FieldV> for FBn254 {
    fn into(self) -> FieldV {
        FieldV::FBn254(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<FieldV> for IntField {
    fn into(self) -> FieldV {
        FieldV::IntField(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for FieldV {
    fn into(self) -> Integer {
        match self {
            FieldV::FCurve25519(f) => {
                let i: BigInt<4> = f.0.into_bigint();
                Integer::from_digits(&i.to_bytes_be(), Order::MsfBe)
            }
            FieldV::FBls12381(f) => Integer::from(&f),
            FieldV::FBn254(f) => Integer::from(&f),
            FieldV::IntField(i) => i.i,
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for &FieldV {
    fn into(self) -> Integer {
        match self {
            FieldV::FCurve25519(f) => {
                Integer::from_digits(&f.0.into_bigint().to_bytes_be(), Order::MsfBe)
            }
            FieldV::FBls12381(f) => Integer::from(f),
            FieldV::FBn254(f) => Integer::from(f),
            FieldV::IntField(i) => i.i.clone(),
        }
    }
}