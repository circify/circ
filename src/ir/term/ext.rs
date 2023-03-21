//! IR extensions

use super::ty::TypeErrorReason;
use super::{Sort, Term, Value};
use circ_hc::Node;
use serde::{Deserialize, Serialize};

mod poly;
mod ram;
mod sort;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// An extension operator. Not externally supported.
///
/// Often evaluatable, but not compilable.
pub enum ExtOp {
    /// See [ram::eval]
    PersistentRamSplit,
    /// Given an array of tuples, returns a reordering such that the result is sorted.
    Sort,
    /// See [poly].
    UniqDeriGcd,
}

impl ExtOp {
    /// Its arity
    pub fn arity(&self) -> Option<usize> {
        match self {
            ExtOp::PersistentRamSplit => Some(2),
            ExtOp::Sort => Some(2),
            ExtOp::UniqDeriGcd => Some(1),
        }
    }
    /// Type-check, given argument sorts
    pub fn check(&self, arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
        match self {
            ExtOp::PersistentRamSplit => ram::check(arg_sorts),
            ExtOp::Sort => sort::check(arg_sorts),
            ExtOp::UniqDeriGcd => poly::check(arg_sorts),
        }
    }
    /// Evaluate, given argument values
    pub fn eval(&self, args: &[&Value]) -> Value {
        match self {
            ExtOp::PersistentRamSplit => ram::eval(args),
            ExtOp::Sort => sort::eval(args),
            ExtOp::UniqDeriGcd => poly::eval(args),
        }
    }
    /// Indicate which children of `t` must be typed to type `t`.
    pub fn check_dependencies(&self, t: &Term) -> Vec<Term> {
        t.cs().to_vec()
    }
    /// Parse, from bytes.
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        match bytes {
            b"persistent_ram_split" => Some(ExtOp::PersistentRamSplit),
            b"uniq_deri_gcd" => Some(ExtOp::UniqDeriGcd),
            b"sort" => Some(ExtOp::Sort),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test;
