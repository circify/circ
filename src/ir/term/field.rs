use rug::ops::RemRounding;
use rug::Integer;

use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

pub const TEST_FIELD: usize = 1014088787;

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FieldElem {
    i: Integer,
    modulus: Arc<Integer>,
}

impl Display for FieldElem {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.i.significant_bits() + 1 < self.modulus.significant_bits() {
            write!(f, "{}", self.i)
        } else {
            write!(f, "-{}", (*self.modulus).clone() - &self.i)
        }
    }
}
impl FieldElem {
    #[track_caller]
    #[inline]
    pub fn check(&self, location: &str) {
        debug_assert!(
            self.i >= 0,
            "Too small field elem: {}\n at {}",
            self,
            location
        );
        debug_assert!(
            &self.i <= &*self.modulus,
            "Too small field elem: {}\n at {}",
            self,
            location
        );
    }
    pub fn i(&self) -> &Integer {
        &self.i
    }
    pub fn modulus(&self) -> &Arc<Integer> {
        &self.modulus
    }
    pub fn recip(self) -> Self {
        let r = FieldElem {
            i: self.i.invert(&*self.modulus).expect("no inverse!"),
            modulus: self.modulus,
        };
        r.check("recip");
        r
    }
    #[track_caller]
    pub fn new(i: Integer, modulus: Arc<Integer>) -> FieldElem {
        let r = FieldElem { i, modulus };
        r.check("new");
        r
    }
}

macro_rules! pf_arith_impl {
    ($Trait:path, $fn:ident) => {
        impl $Trait for FieldElem {
            type Output = Self;
            fn $fn(self, other: Self) -> Self {
                assert_eq!(self.modulus, other.modulus);
                let r = FieldElem {
                    i: (self.i.$fn(other.i)).rem_floor(&*self.modulus),
                    modulus: self.modulus,
                };
                r.check(std::stringify!($fn));
                r
            }
        }
    };
}

pf_arith_impl!(std::ops::Add, add);
pf_arith_impl!(std::ops::Sub, sub);
pf_arith_impl!(std::ops::Mul, mul);

impl std::ops::Neg for FieldElem {
    type Output = Self;
    fn neg(self) -> Self {
        let r = FieldElem {
            i: (-self.i).rem_floor(&*self.modulus),
            modulus: self.modulus,
        };
        r.check("neg");
        r
    }
}
