//! Target circuit representations (and lowering passes)

#[cfg(feature = "aby")]
pub mod aby;
#[cfg(feature = "lp")]
pub mod ilp;
#[cfg(feature = "r1cs")]
pub mod r1cs;
#[cfg(feature = "smt")]
pub mod smt;

/// Returns the number of bits needed to hold `n`.
pub fn bitsize(mut n: usize) -> usize {
    let mut acc = 0;
    while n > 0 {
        n >>= 1;
        acc += 1;
    }
    acc
}
