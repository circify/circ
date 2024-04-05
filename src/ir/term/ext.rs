//! IR extensions

use super::ty::TypeErrorReason;
use super::{Sort, Term, Value};
use circ_hc::Node;
use serde::{Deserialize, Serialize};

mod haboeck;
mod map;
mod poly;
mod ram;
mod sort;
mod waksman;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
/// An extension operator. Not externally supported.
///
/// Often evaluatable, but not compilable.
pub enum ExtOp {
    /// See [haboeck].
    Haboeck,
    /// See [ram::eval]
    PersistentRamSplit,
    /// Given an array of tuples, returns a reordering such that the result is sorted.
    Sort,
    /// See [poly].
    UniqDeriGcd,
    /// See [waksman].
    Waksman,
    /// Array to map
    ArrayToMap,
    /// Select from map
    MapSelect,
    /// Does a map contain a key
    MapContainsKey,
    /// Flip keys and values; values maps to *first* key
    MapFlip,
}

impl ExtOp {
    /// Its arity
    pub fn arity(&self) -> Option<usize> {
        match self {
            ExtOp::Haboeck => Some(2),
            ExtOp::PersistentRamSplit => Some(2),
            ExtOp::Sort => Some(1),
            ExtOp::Waksman => Some(1),
            ExtOp::UniqDeriGcd => Some(1),
            ExtOp::ArrayToMap => Some(1),
            ExtOp::MapContainsKey => Some(2),
            ExtOp::MapSelect => Some(2),
            ExtOp::MapFlip => Some(2),
        }
    }
    /// Type-check, given argument sorts
    pub fn check(&self, arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
        match self {
            ExtOp::Haboeck => haboeck::check(arg_sorts),
            ExtOp::PersistentRamSplit => ram::check(arg_sorts),
            ExtOp::Sort => sort::check(arg_sorts),
            ExtOp::Waksman => waksman::check(arg_sorts),
            ExtOp::UniqDeriGcd => poly::check(arg_sorts),
            ExtOp::ArrayToMap => map::check_array_to_map(arg_sorts),
            ExtOp::MapContainsKey => map::check_map_contains_key(arg_sorts),
            ExtOp::MapSelect => map::check_map_select(arg_sorts),
            ExtOp::MapFlip => map::check_map_flip(arg_sorts),
        }
    }
    /// Evaluate, given argument values
    pub fn eval(&self, args: &[&Value]) -> Value {
        match self {
            ExtOp::Haboeck => haboeck::eval(args),
            ExtOp::PersistentRamSplit => ram::eval(args),
            ExtOp::Sort => sort::eval(args),
            ExtOp::Waksman => waksman::eval(args),
            ExtOp::UniqDeriGcd => poly::eval(args),
            ExtOp::ArrayToMap => map::eval_array_to_map(args),
            ExtOp::MapContainsKey => map::eval_map_contains_key(args),
            ExtOp::MapSelect => map::eval_map_select(args),
            ExtOp::MapFlip => map::eval_map_flip(args),
        }
    }
    /// Indicate which children of `t` must be typed to type `t`.
    pub fn check_dependencies(&self, t: &Term) -> Vec<Term> {
        t.cs().to_vec()
    }
    /// Parse, from bytes.
    pub fn parse(bytes: &[u8]) -> Option<Self> {
        match bytes {
            b"haboeck" => Some(ExtOp::Haboeck),
            b"persistent_ram_split" => Some(ExtOp::PersistentRamSplit),
            b"uniq_deri_gcd" => Some(ExtOp::UniqDeriGcd),
            b"sort" => Some(ExtOp::Sort),
            b"waksman" => Some(ExtOp::Waksman),
            b"array_to_map" => Some(ExtOp::ArrayToMap),
            b"map_contains_key" => Some(ExtOp::MapContainsKey),
            b"map_select" => Some(ExtOp::MapSelect),
            b"map_flip" => Some(ExtOp::MapFlip),
            _ => None,
        }
    }
    /// To string
    pub fn to_str(&self) -> &'static str {
        match self {
            ExtOp::Haboeck => "haboeck",
            ExtOp::PersistentRamSplit => "persistent_ram_split",
            ExtOp::UniqDeriGcd => "uniq_deri_gcd",
            ExtOp::Sort => "sort",
            ExtOp::Waksman => "waksman",
            ExtOp::ArrayToMap => "array_to_map",
            ExtOp::MapContainsKey => "map_contains_key",
            ExtOp::MapSelect => "map_select",
            ExtOp::MapFlip => "map_flip",
        }
    }
}

#[cfg(test)]
mod test;
