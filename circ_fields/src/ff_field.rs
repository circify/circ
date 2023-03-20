//! ff-based fields for use in CirC

use paste::paste;

macro_rules! i64_impl {
    ($Trait: ident, $fn: ident, $Ty: ident) => {
        impl $Trait<i64> for $Ty {
            fn $fn(&mut self, other: i64) {
                self.$fn($Ty::from(other));
            }
        }
    };
}

macro_rules! def_field {
    ($name: ident, $mod: literal, $gen: literal, $limbs: literal) => {
        paste! { pub use $name::Ft as [<$name:camel>]; }
        paste! { pub use $name::FMOD as [<$name:upper _FMOD>]; }
        paste! { pub use $name::FMOD_ARC as [<$name:upper _FMOD_ARC>]; }
        pub mod $name {
            #![allow(warnings, clippy::derive_hash_xor_eq)]
            use datasize::DataSize;
            use ff_derive::PrimeField;
            use ff_derive_num::Num;
            use serde::{Deserialize, Serialize};
            #[derive(PrimeField, Num, Deserialize, Serialize, Hash, DataSize)]
            #[PrimeFieldModulus = $mod]
            #[PrimeFieldGenerator = $gen]
            #[PrimeFieldReprEndianness = "little"]
            /// Field definition
            pub struct Ft([u64; $limbs]);

            use lazy_static::lazy_static;
            use rug::Integer;
            use std::sync::Arc;
            lazy_static! {
                /// Field modulus
                pub static ref FMOD: Integer = Integer::from_str_radix($mod, 10).unwrap();
                pub static ref FMOD_ARC: Arc<Integer> = Arc::new(FMOD.clone());
            }

            use rug::integer::Order;
            impl std::convert::From<&Ft> for Integer {
                fn from(f: &Ft) -> Self {
                    use ff::PrimeField;
                    Self::from_digits(f.to_repr().as_ref(), Order::Lsf)
                }
            }

            impl std::convert::TryFrom<&Integer> for Ft {
                type Error = &'static str;

                fn try_from(i: &Integer) -> Result<Self, Self::Error> {
                    use ff::PrimeField;
                    let len = 8 * $limbs;
                    if i.significant_digits::<u8>() > len {
                        return Err("Tried to convert un-reduced Integer to Ft");
                    }
                    let mut bytes = [0u8; 8 * $limbs];
                    i.write_digits(&mut bytes, Order::Lsf);
                    Self::from_repr_vartime(FtRepr(bytes))
                        .ok_or("Tried to convert un-reduced Integer to Ft")
                }
            }

            impl std::convert::From<Integer> for Ft {
                #[track_caller]
                fn from(mut i: Integer) -> Self {
                    use ff::PrimeField;
                    use rug::ops::RemRoundingAssign;
                    use std::cmp::Ordering::Less;

                    let len = 8 * $limbs;
                    let mut bytes = [0u8; 8 * $limbs];
                    if i.significant_digits::<u8>() > len || i.cmp0() == Less {
                        i.rem_floor_assign(&*FMOD);
                    }
                    i.write_digits(&mut bytes, Order::Lsf);
                    Self::from_repr_vartime(FtRepr(bytes)).unwrap()
                }
            }

            impl std::convert::From<i64> for Ft {
                #[track_caller]
                fn from(mut i: i64) -> Self {
                    let u = i.abs_diff(0);
                    let neg = i < 0;
                    if neg {
                        -Ft::from(u)
                    } else {
                        Ft::from(u)
                    }
                }
            }

            use std::ops::{AddAssign, MulAssign, SubAssign};
            i64_impl! { AddAssign, add_assign, Ft }
            i64_impl! { SubAssign, sub_assign, Ft }
            i64_impl! { MulAssign, mul_assign, Ft }

            #[cfg(test)]
            mod test {
                use super::{Ft, FMOD};
                use ff::Field;
                use rand::thread_rng;
                use rug::Integer;

                #[test]
                fn test_ff_roundtrip() {
                    let mut rng = thread_rng();
                    for _ in 0..1024 {
                        let a0 = Ft::random(&mut rng);
                        let a1 = Integer::from(&a0);
                        let a2 = Ft::try_from(&a1).unwrap();
                        assert_eq!(a0, a2);

                        let ainv0 = a0.invert().unwrap();
                        let ainv1 = Integer::from(a1.invert_ref(&*FMOD).unwrap());
                        let ainv2 = Ft::try_from(&ainv1).unwrap();
                        assert_eq!(ainv0, ainv2);

                        let a3 = Ft::from(a1);
                        assert_eq!(a0, a3);
                        let ainv3 = Ft::from(ainv1);
                        assert_eq!(ainv0, ainv3);
                    }
                }
            }
        }
    };
}

def_field!(
    f_bls12381,
    "52435875175126190479447740508185965837690552500527637822603658699938581184513",
    "7",
    4
);

def_field!(
    f_bn254,
    "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    "5",
    4
);
