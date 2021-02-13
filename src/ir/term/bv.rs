use rug::Integer;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct BitVector {
    uint: Integer,
    width: usize,
}

macro_rules! bv_arith_impl {
    ($Trait:path, $fn:ident) => {
        impl $Trait for BitVector {
            type Output = Self;
            fn $fn(self, other: Self) -> Self {
                assert_eq!(self.width, other.width);
                let r = BitVector {
                    uint: (self.uint.$fn(other.uint)).keep_bits(self.width as u32),
                    width: self.width,
                };
                r.check(std::stringify!($fn));
                r
            }
        }
    };
}

bv_arith_impl!(std::ops::Add, add);
bv_arith_impl!(std::ops::Sub, sub);
bv_arith_impl!(std::ops::Mul, mul);
//bv_arith_impl!(std::ops::Div, div);
//bv_arith_impl!(std::ops::Rem, rem);
bv_arith_impl!(std::ops::BitAnd, bitand);
bv_arith_impl!(std::ops::BitOr, bitor);
bv_arith_impl!(std::ops::BitXor, bitxor);

/// SMT-semantics implementation of unsigned division (udiv).
///
/// If the divisor is zero, returns the all-ones vector.
impl std::ops::Div<&BitVector> for BitVector {
    type Output = Self;
    fn div(self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.uint == 0 {
            let r = BitVector {
                uint: (Integer::from(1) << self.width as u32) - 1,
                width: self.width,
            };
            r.check("div");
            r
        } else {
            let r = BitVector {
                uint: self.uint / &other.uint,
                width: self.width,
            };
            r.check("div");
            r
        }
    }
}

/// SMT-semantics implementation of unsigned remainder (urem).
///
/// If the divisor is zero, returns the all-ones vector.
impl std::ops::Rem<&BitVector> for BitVector {
    type Output = Self;
    fn rem(self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        if other.uint == 0 {
            self
        } else {
            let r = BitVector {
                uint: self.uint % &other.uint,
                width: self.width,
            };
            r.check("rem");
            r
        }
    }
}

impl std::ops::Shl for BitVector {
    type Output = Self;
    fn shl(self, other: Self) -> Self {
        assert_eq!(self.width, other.width);
        let r = BitVector {
            uint: (self.uint.shl(other.uint.to_u32().unwrap())).keep_bits(self.width as u32),
            width: self.width,
        };
        r.check("shl");
        r
    }
}

impl std::ops::Neg for BitVector {
    type Output = Self;
    fn neg(self) -> Self {
        let r = BitVector {
            uint: ((Integer::from(1) << self.width as u32) - self.uint)
                .keep_bits(self.width as u32),
            width: self.width,
        };
        r.check("neg");
        r
    }
}

impl std::ops::Not for BitVector {
    type Output = Self;
    fn not(self) -> Self {
        let r = BitVector {
            uint: (Integer::from(1) << self.width as u32) - 1 - self.uint,
            width: self.width,
        };
        r.check("not");
        r
    }
}

impl BitVector {
    #[track_caller]
    #[inline]
    pub fn check(&self, location: &str) {
        debug_assert!(
            self.uint >= 0,
            "Too small bitvector: {:?}, {}\n at {}",
            self,
            self.uint.significant_bits(),
            location
        );
        debug_assert!(
            (self.uint.significant_bits() as usize) <= self.width,
            "Too big bitvector: {:?}, {}\n at {}",
            self,
            self.uint.significant_bits(),
            location
        );
    }
    pub fn ashr(mut self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        let n = other.uint.to_u32().unwrap();
        let b = self.uint.get_bit(self.width as u32 - 1);
        self.uint >>= n;
        for i in 0..n {
            self.uint.set_bit(self.width as u32 - 1 - i, b);
        }
        self.check("ashr");
        self
    }
    pub fn lshr(self, other: &Self) -> Self {
        assert_eq!(self.width, other.width);
        let r = BitVector {
            uint: (self.uint >> other.uint.to_u32().unwrap()).keep_bits(self.width as u32),
            width: self.width,
        };
        r.check("lshr");
        r
    }
    pub fn concat(self, other: Self) -> Self {
        let r = BitVector {
            uint: (self.uint << other.width as u32) | other.uint,
            width: self.width + other.width,
        };
        r.check("concat");
        r
    }
    pub fn extract(self, high: usize, low: usize) -> Self {
        let r = BitVector {
            uint: (self.uint >> low as u32).keep_bits((high - low + 1) as u32),
            width: high - low + 1,
        };
        r.check("extract");
        r
    }
    pub fn as_sint(&self) -> Integer {
        if self.uint.significant_bits() as usize == self.width {
            self.uint.clone() - (Integer::from(1) << self.width as u32)
        } else {
            self.uint.clone()
        }
    }
    pub fn uint(&self) -> &Integer {
        &self.uint
    }
    pub fn width(&self) -> usize {
        self.width
    }
    #[track_caller]
    pub fn new(uint: Integer, width: usize) -> BitVector {
        let r = BitVector { uint, width };
        r.check("new");
        r
    }
    pub fn bit(&self, i: usize) -> bool {
        self.uint.get_bit(i as u32)
    }
    pub fn ones(n: usize) -> BitVector {
        BitVector {
            uint: (Integer::from(1) << n as u32) - 1,
            width: n,
        }
    }
    pub fn zeros(n: usize) -> BitVector {
        BitVector {
            uint: Integer::from(0),
            width: n,
        }
    }
}

impl Display for BitVector {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "#b")?;
        for i in 0..self.width {
            write!(
                f,
                "{}",
                self.uint.get_bit((self.width - i - 1) as u32) as u8
            )?;
        }
        Ok(())
    }
}
