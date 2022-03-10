//! Fields for use in CirC

mod ff_field;
mod int_field;

pub mod moduli {
    pub use super::ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
}

use ff_field::{FBls12381, FBn254};
use ff_field::{F_BLS12381_FMOD, F_BN254_FMOD};
use ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
use int_field::IntField;

use ff::Field;
use paste::paste;
use rug::Integer;
use std::fmt::{self, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::sync::Arc;

// TODO: rework this using macros?

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash)]
pub enum FieldT {
    FBls12381,
    FBn254,
    IntField(Arc<Integer>),
}

impl Display for FieldT {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::FBls12381 => write!(f, "FieldT::FBls12381"),
            Self::FBn254 => write!(f, "FieldT::FBn254"),
            Self::IntField(m) => write!(f, "FieldT::(mod {})", &*m),
        }
    }
}

impl From<Arc<Integer>> for FieldT {
    fn from(m: Arc<Integer>) -> Self {
        match m.as_ref() {
            m if m == &*F_BLS12381_FMOD => Self::FBls12381,
            m if m == &*F_BN254_FMOD => Self::FBn254,
            _ => Self::IntField(m),
        }
    }
}

impl From<Integer> for FieldT {
    fn from(m: Integer) -> Self {
        match &m {
            m if m == &*F_BLS12381_FMOD => Self::FBls12381,
            m if m == &*F_BN254_FMOD => Self::FBn254,
            _ => Self::IntField(Arc::new(m)),
        }
    }
}

impl From<&Integer> for FieldT {
    fn from(m: &Integer) -> Self {
        match m {
            m if m == &*F_BLS12381_FMOD => Self::FBls12381,
            m if m == &*F_BN254_FMOD => Self::FBn254,
            _ => Self::IntField(Arc::new(m.clone())),
        }
    }
}

impl FieldT {
    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self {
            Self::FBls12381 => &*F_BLS12381_FMOD,
            Self::FBn254 => &*F_BN254_FMOD,
            Self::IntField(m) => m.as_ref(),
        }
    }

    #[inline]
    pub fn modulus_arc(&self) -> Arc<Integer> {
        match self {
            Self::FBls12381 => F_BLS12381_FMOD_ARC.clone(),
            Self::FBn254 => F_BN254_FMOD_ARC.clone(),
            Self::IntField(m) => m.clone(),
        }
    }

    #[inline]
    pub fn default_value(&self) -> FieldV {
        match self {
            Self::FBls12381 => FieldV::FBls12381(Default::default()),
            Self::FBn254 => FieldV::FBn254(Default::default()),
            Self::IntField(m) => FieldV::IntField(IntField::new(Integer::from(0), m.clone())),
        }
    }

    #[inline]
    pub fn zero(&self) -> FieldV {
        self.default_value()
    }

    #[inline]
    pub fn random_v(&self, rng: impl rand::RngCore) -> FieldV {
        FieldV::random(self.clone(), rng)
    }

    #[inline]
    pub fn new_v<I>(&self, i: I) -> FieldV
    where
        Integer: From<I>,
    {
        FieldV::new_ty(i, self.clone())
    }
}

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash)]
pub enum FieldV {
    FBls12381(FBls12381),
    FBn254(FBn254),
    IntField(IntField),
}

impl FieldV {
    #[inline]
    pub fn ty(&self) -> FieldT {
        match self {
            Self::FBls12381(_) => FieldT::FBls12381,
            Self::FBn254(_) => FieldT::FBn254,
            Self::IntField(i) => FieldT::IntField(i.modulus_arc()),
        }
    }

    #[inline]
    pub fn new<I>(i: I, m: Arc<Integer>) -> Self
    where
        Integer: From<I>,
    {
        Self::new_ty(i, FieldT::from(m))
    }

    #[track_caller]
    #[inline]
    pub fn check(&self, loc: &str) {
        if let Self::IntField(m) = self {
            m.check(loc);
        }
    }

    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self {
            Self::FBls12381(_) => &*F_BLS12381_FMOD,
            Self::FBn254(_) => &*F_BN254_FMOD,
            Self::IntField(i) => i.modulus(),
        }
    }

    #[track_caller]
    #[inline]
    pub fn recip_ref(&self) -> Self {
        match self {
            Self::FBls12381(pf) => Self::FBls12381(pf.invert().unwrap()),
            Self::FBn254(pf) => Self::FBn254(pf.invert().unwrap()),
            Self::IntField(i) => Self::IntField(i.clone().recip()),
        }
    }

    #[track_caller]
    #[inline]
    pub fn recip(self) -> Self {
        match self {
            Self::FBls12381(pf) => Self::FBls12381(pf.invert().unwrap()),
            Self::FBn254(pf) => Self::FBn254(pf.invert().unwrap()),
            Self::IntField(i) => Self::IntField(i.recip()),
        }
    }

    #[inline]
    pub fn i(&self) -> Integer {
        self.into()
    }

    #[inline]
    pub fn is_zero(&self) -> bool {
        match self {
            Self::FBls12381(pf) => bool::from(pf.is_zero()),
            Self::FBn254(pf) => bool::from(pf.is_zero()),
            Self::IntField(i) => i.is_zero(),
        }
    }

    #[inline]
    pub fn is_one(&self) -> bool {
        use num_traits::One;
        match self {
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
            FieldT::FBls12381 => Self::FBls12381(FBls12381::from(i)),
            FieldT::FBn254 => Self::FBn254(FBn254::from(i)),
            FieldT::IntField(m) => Self::IntField(IntField::new(i, m)),
        }
    }

    fn random(ty: FieldT, mut rng: impl rand::RngCore) -> Self {
        match ty {
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
}

impl Display for FieldV {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
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
            FieldV::FBls12381(f) => Integer::from(f),
            FieldV::FBn254(f) => Integer::from(f),
            FieldV::IntField(i) => i.i.clone(),
        }
    }
}
