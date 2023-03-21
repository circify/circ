//! Fields for use in CirC

#![warn(missing_docs)]
#![deny(warnings)]

mod ff_field;
mod int_field;
pub mod size;

/// Exports for moduli defined in this crate, as ARCs
pub mod moduli {
    pub use super::ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
}

use ff_field::{FBls12381, FBn254};
use ff_field::{F_BLS12381_FMOD, F_BN254_FMOD};
use ff_field::{F_BLS12381_FMOD_ARC, F_BN254_FMOD_ARC};
use int_field::IntField;

use datasize::DataSize;
use ff::Field;
use paste::paste;
use rug::Integer;
use serde::{Deserialize, Serialize};
use std::fmt::{self, Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::sync::Arc;

// TODO: rework this using macros?

/// Field element type
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize, Deserialize, DataSize)]
pub enum FieldT {
    /// BLS12-381 scalar field as `ff`
    FBls12381,
    /// BN-254 scalar field as `ff`
    FBn254,
    /// Generic field element based on `rug::Integer`
    IntField(Arc<Integer>),
}

impl Display for FieldT {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::FBls12381 => write!(f, "FieldT::FBls12381"),
            Self::FBn254 => write!(f, "FieldT::FBn254"),
            Self::IntField(m) => write!(f, "FieldT::(mod {})", m),
        }
    }
}

impl Debug for FieldT {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
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
            _ => None,
        }
    }

    /// If this field has an inline tag, get it.
    fn inline_tag(&self) -> Option<InlineFieldTag> {
        match self {
            FieldT::FBls12381 => Some(InlineFieldTag::Bls12381),
            FieldT::FBn254 => Some(InlineFieldTag::Bn254),
            FieldT::IntField(_) => None,
        }
    }

    /// Field modulus
    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self {
            Self::FBls12381 => &F_BLS12381_FMOD,
            Self::FBn254 => &F_BN254_FMOD,
            Self::IntField(m) => m.as_ref(),
        }
    }

    /// Field modulus as an ARC
    #[inline]
    pub fn modulus_arc(&self) -> Arc<Integer> {
        match self {
            Self::FBls12381 => F_BLS12381_FMOD_ARC.clone(),
            Self::FBn254 => F_BN254_FMOD_ARC.clone(),
            Self::IntField(m) => m.clone(),
        }
    }

    /// Default value for this type
    #[inline]
    pub fn default_value(&self) -> FieldV {
        match self {
            Self::FBls12381 => FieldV::from(InlineFieldV(0, InlineFieldTag::Bls12381)),
            Self::FBn254 => FieldV::from(InlineFieldV(0, InlineFieldTag::Bn254)),
            Self::IntField(_) => self.new_v(0),
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
        FieldV::new_ty_long(i, self.clone())
    }

    /// New value of this type
    #[inline]
    pub fn new_v_prim<I>(&self, i: I) -> FieldV
    where
        i64: From<I>,
    {
        FieldV::new_ty(i, self.clone())
    }
}

/// Field element value
///
/// ## Implementation Notes
///
/// The contents are either:
/// * a pointer to an enum [FullFieldV] or
/// * a i62 with a type-tag
///
/// The tag can be:
/// * 00: pointer
/// * 01, 10: different fields
/// * 11: invalid (for now)
#[derive(Serialize, Deserialize)]
#[serde(into = "FullFieldV", from = "FullFieldV")]
pub struct FieldV(i64);

/// Number of bits in [FieldV] used for the tag.
const N_TAG_BITS: u8 = 2;
/// Number of bits in [FieldV] used for the tag.
const N_TAG_BITS_I64: i64 = N_TAG_BITS as i64;
/// Mask that selects the tag bits in a [FieldV].
const TAG_BITS_MASK: i64 = (1 << N_TAG_BITS_I64) - 1;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum FieldTag {
    FullField,
    InlineBls12381,
    InlineBn254,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum InlineFieldTag {
    Bls12381,
    Bn254,
}

impl From<u8> for FieldTag {
    fn from(value: u8) -> Self {
        match value {
            0 => FieldTag::FullField,
            1 => FieldTag::InlineBls12381,
            2 => FieldTag::InlineBn254,
            _ => panic!("Invalid field tag {}", value),
        }
    }
}

impl From<InlineFieldTag> for FieldTag {
    fn from(value: InlineFieldTag) -> Self {
        match value {
            InlineFieldTag::Bls12381 => FieldTag::InlineBls12381,
            InlineFieldTag::Bn254 => FieldTag::InlineBn254,
        }
    }
}

impl From<FieldTag> for InlineFieldTag {
    fn from(value: FieldTag) -> Self {
        match value {
            FieldTag::InlineBls12381 => InlineFieldTag::Bls12381,
            FieldTag::InlineBn254 => InlineFieldTag::Bn254,
            FieldTag::FullField => panic!("Tag {:?} is not inline", value),
        }
    }
}

impl FieldTag {
    const fn u8(&self) -> u8 {
        match self {
            FieldTag::FullField => 0,
            FieldTag::InlineBls12381 => 1,
            FieldTag::InlineBn254 => 2,
        }
    }
}

impl InlineFieldTag {
    fn ty(&self) -> FieldT {
        match self {
            InlineFieldTag::Bls12381 => FieldT::FBls12381,
            InlineFieldTag::Bn254 => FieldT::FBn254,
        }
    }
    fn modulus(&self) -> &'static Integer {
        match self {
            InlineFieldTag::Bls12381 => &F_BLS12381_FMOD,
            InlineFieldTag::Bn254 => &F_BN254_FMOD,
        }
    }
    fn matches(&self, v: &FullFieldV) -> bool {
        match (self, v) {
            (InlineFieldTag::Bls12381, FullFieldV::FBls12381(_)) => true,
            (InlineFieldTag::Bn254, FullFieldV::FBn254(_)) => true,
            _ => false,
        }
    }
    #[track_caller]
    fn assert_matches(&self, v: &FullFieldV) {
        assert!(self.matches(v), "Field {:?} does not match {:?}", self, v);
    }
}

struct InlineFieldV(i64, InlineFieldTag);

impl InlineFieldV {
    fn i64_in_range(i: i64) -> bool {
        ((i << N_TAG_BITS_I64) >> N_TAG_BITS_I64) == i
    }
    fn signed_bits(&self) -> u32 {
        if self.0 < 0 {
            65 - self.0.leading_ones()
        } else {
            65 - self.0.leading_zeros()
        }
    }
    fn repr_as_i64(&self) -> i64 {
        debug_assert!(InlineFieldV::i64_in_range(self.0));
        self.0 << N_TAG_BITS_I64 | FieldTag::from(self.1).u8() as i64
    }
}

impl From<InlineFieldV> for FieldV {
    fn from(v: InlineFieldV) -> Self {
        FieldV(v.repr_as_i64())
    }
}
impl From<FullFieldV> for FieldV {
    fn from(f: FullFieldV) -> Self {
        let this = Self(Box::into_raw(Box::new(f)) as i64);
        assert!(this.is_full());
        this
    }
}
impl From<FieldV> for FullFieldV {
    fn from(mut f: FieldV) -> Self {
        if f.is_full() {
            f.take_full()
        } else {
            FullFieldV::from(f.inline())
        }
    }
}

impl FieldV {
    fn tag(&self) -> FieldTag {
        FieldTag::from((self.0 & TAG_BITS_MASK) as u8)
    }
    fn inline_i64(&self) -> i64 {
        debug_assert_ne!(self.tag(), FieldTag::FullField);
        self.0 >> N_TAG_BITS_I64
    }
    fn full_mut(&mut self) -> &mut FullFieldV {
        assert!(self.is_full());
        let ptr: *mut FullFieldV = self.0 as *mut _;
        unsafe { &mut *ptr }
    }
    fn full_ref(&self) -> &FullFieldV {
        assert!(self.is_full());
        let ptr: *const FullFieldV = self.0 as *const _;
        unsafe { &*ptr }
    }
    fn full_cow(&self) -> std::borrow::Cow<FullFieldV> {
        if self.is_full() {
            std::borrow::Cow::Borrowed(self.full_ref())
        } else {
            std::borrow::Cow::Owned(FullFieldV::from(self.inline()))
        }
    }
    fn take_full(&mut self) -> FullFieldV {
        assert!(self.is_full());
        unsafe {
            let ptr: *mut FullFieldV = self.0 as *mut FullFieldV;
            let box_ = Box::from_raw(ptr);
            self.0 = InlineFieldV(0, InlineFieldTag::Bls12381).repr_as_i64();
            *box_
        }
    }
    fn is_full(&self) -> bool {
        self.tag() == FieldTag::FullField
    }
    fn inline(&self) -> InlineFieldV {
        debug_assert!(!self.is_full());
        InlineFieldV(self.inline_i64(), self.tag().into())
    }
    fn promote(&mut self) -> &mut FullFieldV {
        if !self.is_full() {
            *self = Self::from(FullFieldV::from(self.inline()));
        }
        self.full_mut()
    }
    fn either_ref(&self) -> Result<InlineFieldV, &FullFieldV> {
        if self.is_full() {
            Err(self.full_ref())
        } else {
            Ok(self.inline())
        }
    }
}

impl Clone for FieldV {
    #[inline]
    fn clone(&self) -> Self {
        self.either_ref()
            .map(|i| i.into())
            .unwrap_or_else(|full| Self::from(full.clone()))
    }
}

impl PartialOrd for FieldV {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FieldV {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.full_cow().cmp(&other.full_cow())
    }
}

impl PartialEq for FieldV {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.full_cow().eq(&other.full_cow())
    }
}

impl Eq for FieldV {}

impl std::hash::Hash for FieldV {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.full_cow().hash(state)
    }
}

impl std::ops::Drop for FieldV {
    fn drop(&mut self) {
        if self.is_full() {
            std::mem::drop(self.take_full())
        }
    }
}

/// Field element value
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Hash, Serialize, Deserialize, DataSize)]
pub enum FullFieldV {
    /// BLS12-381 scalar field element as `ff`
    FBls12381(FBls12381),
    /// BN-254 scalar field element as `ff`
    FBn254(FBn254),
    /// Generic field element based on `rug::Integer`
    IntField(IntField),
}

impl From<InlineFieldV> for FullFieldV {
    fn from(value: InlineFieldV) -> Self {
        match value.1 {
            InlineFieldTag::Bls12381 => FullFieldV::FBls12381(value.0.into()),
            InlineFieldTag::Bn254 => FullFieldV::FBn254(value.0.into()),
        }
    }
}

impl FullFieldV {
    /// Type of this value
    #[inline]
    fn ty(&self) -> FieldT {
        match self {
            FullFieldV::FBls12381(_) => FieldT::FBls12381,
            FullFieldV::FBn254(_) => FieldT::FBn254,
            FullFieldV::IntField(i) => FieldT::IntField(i.modulus_arc()),
        }
    }

    /// Raise this element to a power.
    #[inline]
    fn pow(&self, u: u64) -> Self {
        match self {
            FullFieldV::FBls12381(f) => FullFieldV::FBls12381(f.pow_vartime(&[u])),
            FullFieldV::FBn254(f) => FullFieldV::FBn254(f.pow_vartime(&[u])),
            FullFieldV::IntField(i) => FullFieldV::IntField(IntField::new(
                i.i.clone().pow_mod(&Integer::from(u), i.modulus()).unwrap(),
                i.modulus_arc(),
            )),
        }
    }

    /// Get this field element as a signed integer. No particular cut-off is guaranteed.
    #[inline]
    fn signed_int(&self) -> Integer {
        let mut i: Integer = self.into();
        if i.significant_bits() >= self.ty().modulus().significant_bits() - 1 {
            i -= self.ty().modulus();
        }
        i
    }
}

impl FieldV {
    /// Type of this value
    #[inline]
    pub fn ty(&self) -> FieldT {
        match self.either_ref() {
            Ok(InlineFieldV(_, t)) => t.ty(),
            Err(i) => i.ty(),
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
        Self::new_ty_long(i, FieldT::from(m))
    }

    /// Check that a value is well formed
    #[track_caller]
    #[inline]
    pub fn check(&self, loc: &str) {
        if let Err(FullFieldV::IntField(m)) = self.either_ref() {
            m.check(loc);
        }
    }

    /// Field modulus as `&rug::Integer`
    #[inline]
    pub fn modulus(&self) -> &Integer {
        match self.either_ref() {
            Ok(InlineFieldV(_, t)) => t.modulus(),
            Err(FullFieldV::FBls12381(_)) => &F_BLS12381_FMOD,
            Err(FullFieldV::FBn254(_)) => &F_BN254_FMOD,
            Err(FullFieldV::IntField(i)) => i.modulus(),
        }
    }

    /// Compute the multiplicative inverse (panics on 0)
    #[track_caller]
    #[inline]
    pub fn recip_ref(&self) -> Self {
        match &*self.full_cow() {
            FullFieldV::FBls12381(pf) => Self::from(FullFieldV::FBls12381(pf.invert().unwrap())),
            FullFieldV::FBn254(pf) => Self::from(FullFieldV::FBn254(pf.invert().unwrap())),
            FullFieldV::IntField(i) => Self::from(FullFieldV::IntField(i.clone().recip())),
        }
    }

    /// Ccompute the multiplicative inverse (panics on 0)
    #[track_caller]
    #[inline]
    pub fn recip(self) -> Self {
        match &*self.full_cow() {
            FullFieldV::FBls12381(pf) => Self::from(FullFieldV::FBls12381(pf.invert().unwrap())),
            FullFieldV::FBn254(pf) => Self::from(FullFieldV::FBn254(pf.invert().unwrap())),
            FullFieldV::IntField(i) => Self::from(FullFieldV::IntField(i.clone().recip())),
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
        match self.either_ref() {
            Ok(InlineFieldV(i, _)) => i == 0,
            Err(FullFieldV::FBls12381(pf)) => bool::from(pf.is_zero()),
            Err(FullFieldV::FBn254(pf)) => bool::from(pf.is_zero()),
            Err(FullFieldV::IntField(i)) => i.is_zero(),
        }
    }

    /// Test if value is 1
    #[inline]
    pub fn is_one(&self) -> bool {
        use num_traits::One;
        match self.either_ref() {
            Ok(InlineFieldV(i, _)) => i == 1,
            Err(FullFieldV::FBls12381(pf)) => bool::from(pf.is_one()),
            Err(FullFieldV::FBn254(pf)) => bool::from(pf.is_one()),
            Err(FullFieldV::IntField(i)) => i.i == 1,
        }
    }

    #[inline]
    fn new_ty_long<I>(i: I, ty: FieldT) -> Self
    where
        Integer: From<I>,
    {
        // TODO: relax interface.
        let i = Integer::from(i);
        if i.signed_bits() < 64 - N_TAG_BITS as u32 {
            if let Some(t) = ty.inline_tag() {
                return Self::from(InlineFieldV(i.to_i64_wrapping(), t));
            }
        }
        Self::from(match ty {
            FieldT::FBls12381 => FullFieldV::FBls12381(FBls12381::from(i)),
            FieldT::FBn254 => FullFieldV::FBn254(FBn254::from(i)),
            FieldT::IntField(m) => FullFieldV::IntField(IntField::new(i, m)),
        })
    }

    #[inline]
    fn new_ty<I>(i: I, ty: FieldT) -> Self
    where
        i64: From<I>,
    {
        let i: i64 = i.into();
        let bits = if i < 0 {
            65 - i.leading_ones()
        } else {
            65 - i.leading_zeros()
        };
        if bits < 64 - N_TAG_BITS as u32 {
            if let Some(t) = ty.inline_tag() {
                return Self::from(InlineFieldV(i, t));
            }
        }
        Self::from(match ty {
            FieldT::FBls12381 => FullFieldV::FBls12381(FBls12381::from(i)),
            FieldT::FBn254 => FullFieldV::FBn254(FBn254::from(i)),
            FieldT::IntField(m) => FullFieldV::IntField(IntField::new(Integer::from(i), m)),
        })
    }

    fn random(ty: FieldT, mut rng: impl rand::RngCore) -> Self {
        Self::from(match ty {
            FieldT::FBls12381 => FullFieldV::FBls12381(FBls12381::random(rng)),
            FieldT::FBn254 => FullFieldV::FBn254(FBn254::random(rng)),
            FieldT::IntField(m) => {
                let mut rug_rng = rug::rand::RandState::new_mersenne_twister();
                rug_rng.seed(&Integer::from(rng.next_u64()));
                let i = Integer::from(m.random_below_ref(&mut rug_rng));
                FullFieldV::IntField(IntField::new(i, m))
            }
        })
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

    /// Get this field element as an SMT-LIB string.
    #[inline]
    pub fn as_smtlib(&self) -> String {
        format!("#f{}m{}", self.signed_int(), self.ty().modulus())
    }

    /// Get this field element as a signed integer. No particular cut-off is guaranteed.
    #[inline]
    pub fn signed_int(&self) -> Integer {
        let mut i = self.i();
        if i.significant_bits() >= self.ty().modulus().significant_bits() - 1 {
            i -= self.ty().modulus();
        }
        i
    }

    /// Raise this element to a power.
    #[inline]
    pub fn pow(&self, u: u64) -> Self {
        if !self.is_full()
            && (self.inline().signed_bits() as u64).saturating_mul(u) < 64 - N_TAG_BITS as u64
        {
            let InlineFieldV(i, t) = self.inline();
            let i = i.pow(u as u32);
            assert!(InlineFieldV::i64_in_range(i));
            Self::from(InlineFieldV(i, t))
        } else {
            self.full_cow().pow(u).into()
        }
    }
}

impl Display for FieldV {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.signed_int())
    }
}

impl Debug for FieldV {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} (in {})", self.signed_int(), self.ty())
    }
}

impl Debug for FullFieldV {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{} (in {})", self.signed_int(), self.ty())
    }
}

impl DataSize for FieldV {
    const IS_DYNAMIC: bool = true;

    const STATIC_HEAP_SIZE: usize = 0;

    #[inline]
    fn estimate_heap_size(&self) -> usize {
        if self.is_full() {
            self.full_ref().estimate_heap_size() + std::mem::size_of::<FullFieldV>()
        } else {
            0
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

            impl [<$Trait Assign>]<FieldV> for FieldV {
                fn [<$fn _assign>](&mut self, other: FieldV) {
                    self.[<$fn _assign>](&other);
                }
            }

            impl [<$Trait Assign>]<&FullFieldV> for FullFieldV {
                fn [<$fn _assign>](&mut self, other: &FullFieldV) {
                    match (self, other) {
                        (Self::FBls12381(f1), Self::FBls12381(f2)) => f1.[<$fn _assign>](f2),
                        (Self::FBn254(f1), Self::FBn254(f2)) => f1.[<$fn _assign>](f2),
                        (Self::IntField(i1), Self::IntField(i2)) => i1.[<$fn _assign>](i2),
                        (s, o) => panic!("Operation [<$Trait Assign>] on {} and {}", s.ty(), o.ty()),
                    }
                }
            }

            impl [<$Trait Assign>]<i64> for FullFieldV {
                fn [<$fn _assign>](&mut self, other: i64) {
                    match self {
                        Self::FBls12381(f1) => f1.[<$fn _assign>](other),
                        Self::FBn254(f1) => f1.[<$fn _assign>](other),
                        Self::IntField(f1) => f1.[<$fn _assign>](other),
                    }
                }
            }

            impl [<$Trait Assign>]<InlineFieldV> for FullFieldV {
                fn [<$fn _assign>](&mut self, InlineFieldV(i, t): InlineFieldV) {
                    t.assert_matches(self);
                    self.[<$fn _assign>](i)
                }
            }

            impl [<$Trait Assign>]<&FieldV> for FieldV {
                fn [<$fn _assign>](&mut self, other: &FieldV) {
                    match (self.is_full(), other.is_full()) {
                        (false, false) => *self = self.inline().$fn(other.inline()),
                        (false, true) => self.promote().[<$fn _assign>](other.full_ref()),
                        (true, false) => self.full_mut().[<$fn _assign>](other.inline()),
                        (true, true) => self.full_mut().[<$fn _assign>](other.full_ref()),
                    }
                }
            }
        }
    }
}

arith_impl!(Add, add);
arith_impl!(Mul, mul);
arith_impl!(Sub, sub);

impl Add<InlineFieldV> for InlineFieldV {
    type Output = FieldV;

    fn add(self, rhs: InlineFieldV) -> Self::Output {
        assert_eq!(self.1, rhs.1);
        let x = self.0.add(rhs.0);
        if InlineFieldV::i64_in_range(x) {
            FieldV::from(InlineFieldV(x, self.1))
        } else {
            let mut this = FullFieldV::from(self);
            this.add_assign(rhs.0);
            FieldV::from(this)
        }
    }
}

impl Sub<InlineFieldV> for InlineFieldV {
    type Output = FieldV;

    fn sub(self, rhs: InlineFieldV) -> Self::Output {
        assert_eq!(self.1, rhs.1);
        let x = self.0.sub(rhs.0);
        if InlineFieldV::i64_in_range(x) {
            FieldV::from(InlineFieldV(x, self.1))
        } else {
            let mut this = FullFieldV::from(self);
            this.sub_assign(rhs.0);
            FieldV::from(this)
        }
    }
}

impl Mul<InlineFieldV> for InlineFieldV {
    type Output = FieldV;

    fn mul(self, rhs: InlineFieldV) -> Self::Output {
        assert_eq!(self.1, rhs.1);
        let x = self.0.checked_mul(rhs.0);
        if let Some(x) = x {
            if InlineFieldV::i64_in_range(x) {
                return FieldV::from(InlineFieldV(x, self.1));
            }
        }
        let mut this = FullFieldV::from(self);
        this.mul_assign(rhs.0);
        FieldV::from(this)
    }
}

impl Neg for FieldV {
    type Output = Self;
    fn neg(mut self) -> Self {
        if self.is_full() {
            match self.full_mut() {
                FullFieldV::FBls12381(pf) => Self::from(FullFieldV::FBls12381(pf.clone().neg())),
                FullFieldV::FBn254(pf) => Self::from(FullFieldV::FBn254(pf.clone().neg())),
                FullFieldV::IntField(i) => Self::from(FullFieldV::IntField(i.clone().neg())),
            }
        } else {
            let InlineFieldV(i, t) = self.inline();
            let ni = -i;
            if InlineFieldV::i64_in_range(ni) {
                Self::from(InlineFieldV(ni, t))
            } else {
                self.promote();
                self.neg()
            }
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<FullFieldV> for FBls12381 {
    fn into(self) -> FullFieldV {
        FullFieldV::FBls12381(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<FullFieldV> for FBn254 {
    fn into(self) -> FullFieldV {
        FullFieldV::FBn254(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<FullFieldV> for IntField {
    fn into(self) -> FullFieldV {
        FullFieldV::IntField(self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for FullFieldV {
    fn into(self) -> Integer {
        match self {
            FullFieldV::FBls12381(f) => Integer::from(&f),
            FullFieldV::FBn254(f) => Integer::from(&f),
            FullFieldV::IntField(i) => i.i,
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for &FullFieldV {
    fn into(self) -> Integer {
        match self {
            FullFieldV::FBls12381(f) => Integer::from(f),
            FullFieldV::FBn254(f) => Integer::from(f),
            FullFieldV::IntField(i) => i.i.clone(),
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for FieldV {
    fn into(self) -> Integer {
        Into::into(&self)
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for &FieldV {
    fn into(self) -> Integer {
        if self.is_full() {
            self.full_ref().into()
        } else {
            let i = self.inline().0;
            if i < 0 {
                Integer::from(i) + self.modulus()
            } else {
                Integer::from(i)
            }
        }
    }
}

#[cfg(test)]
mod test;
