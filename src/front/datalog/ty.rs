//! Types in our datalog variant

use std::fmt::{Display, Formatter, self};

/// A type
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Ty {
    /// Boolean
    Bool,
    /// Field element
    Field,
    /// unsigned, fixed-width integer
    Uint(u8),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            &Ty::Bool => write!(f, "bool"),
            &Ty::Field => write!(f, "field"),
            &Ty::Uint(w) => write!(f, "u{}", w),
        }
    }
}
