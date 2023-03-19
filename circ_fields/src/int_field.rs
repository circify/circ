//! Integer-based fields for use in CirC
// based on Alex's original FieldElem impl

use datasize::DataSize;
use paste::paste;
use rug::{
    ops::{RemRounding, RemRoundingAssign},
    Integer,
};
use serde::{Deserialize, Serialize};
use std::fmt::{self, Display, Formatter};
use std::ops::Deref;
use std::sync::Arc;

#[derive(PartialEq, Eq, Clone, Debug, PartialOrd, Ord, Hash, Serialize, Deserialize, DataSize)]
pub struct IntField {
    #[data_size(with = super::size::estimate_heap_size_integer)]
    pub(crate) i: Integer,
    m: Arc<Integer>,
}

impl Display for IntField {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.i.significant_bits() + 1 < self.m.significant_bits() {
            write!(f, "#f{}m{}", self.i, self.m)
        } else {
            write!(f, "#f-{}m{}", self.m.deref().clone() - &self.i, self.m)
        }
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for IntField {
    fn into(self) -> Integer {
        self.i
    }
}

#[allow(clippy::from_over_into)]
impl Into<Integer> for &IntField {
    fn into(self) -> Integer {
        self.i.clone()
    }
}

impl IntField {
    #[track_caller]
    #[inline]
    /// Check value in-range (debug only)
    pub fn check(&self, location: &str) {
        debug_assert!(
            self.i >= 0,
            "Negative field elem: {}\nat {}",
            self,
            location
        );
        debug_assert!(
            self.i < *self.m,
            "Field elem too big: {}\nat {}",
            self,
            location
        );
    }

    /// Get a ref to the modulus
    pub fn modulus(&self) -> &Integer {
        &self.m
    }

    /// Get an Arc of the modulus
    pub fn modulus_arc(&self) -> Arc<Integer> {
        self.m.clone()
    }

    /// Invert mod p
    pub fn recip(self) -> Self {
        let r = Self {
            i: self.i.invert(&self.m).expect("no inverse!"),
            m: self.m,
        };
        r.check("recip");
        r
    }

    /// Construct a new IntField
    pub fn new(mut i: Integer, m: Arc<Integer>) -> Self {
        if i < 0 || i > *m {
            i.rem_floor_assign(&*m);
        }
        Self { i, m }
    }

    /// Check if this value is equal to zero
    pub fn is_zero(&self) -> bool {
        self.check("is_zero");
        self.i == 0
    }
}

macro_rules! arith_impl {
    ($Trait: ident, $fn: ident) => {
        impl $Trait for IntField {
            type Output = Self;
            fn $fn(self, other: Self) -> Self {
                assert_eq!(self.m, other.m);
                let r = Self {
                    i: (self.i.$fn(other.i)).rem_floor(&*self.m),
                    m: self.m,
                };
                r.check(std::stringify!($fn));
                r
            }
        }

        impl $Trait<&IntField> for IntField {
            type Output = Self;
            fn $fn(self, other: &Self) -> Self {
                assert_eq!(self.m, other.m);
                let r = Self {
                    i: (self.i.$fn(&other.i)).rem_floor(&*self.m),
                    m: self.m,
                };
                r.check(std::stringify!($fn));
                r
            }
        }

        impl $Trait<IntField> for &IntField {
            type Output = IntField;
            fn $fn(self, other: IntField) -> IntField {
                assert_eq!(self.m, other.m);
                let r = IntField {
                    i: ((&self.i).$fn(other.i)).rem_floor(&*self.m),
                    m: other.m,
                };
                r.check(std::stringify!($fn));
                r
            }
        }

        paste! {
            impl [<$Trait Assign>]<&IntField> for IntField {
                fn [<$fn _assign>](&mut self, other: &IntField) {
                    assert_eq!(self.m, other.m);
                    self.i.[<$fn _assign>](&other.i);
                    self.i.rem_floor_assign(&*self.m);
                }
            }
        }

        paste! {
            impl [<$Trait Assign>]<i64> for IntField {
                fn [<$fn _assign>](&mut self, other: i64) {
                    self.i.[<$fn _assign>](&other);
                    self.i.rem_floor_assign(&*self.m);
                }
            }
        }
    };
}

use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
arith_impl!(Add, add);
arith_impl!(Sub, sub);
arith_impl!(Mul, mul);

impl Neg for IntField {
    type Output = Self;
    fn neg(self) -> Self {
        let r = Self {
            i: (-self.i).rem_floor(&*self.m),
            m: self.m,
        };
        r.check("neg");
        r
    }
}
