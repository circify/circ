//! C Types
use crate::front::c::term::CTermData;
use crate::front::c::term::CTermData::{CBool, CInt};

use crate::ir::term::*;

#[derive(Clone, PartialEq, Eq)]
pub enum Type {
    Bool,
    Uint(usize),
}

impl Type {
    fn default(&self) -> CTermData {
        match self {
            Self::Bool => CBool(leaf_term(Op::Const(Value::Bool(false)))),
            Self::Uint(w) => CInt(*w, bv_lit(0, *w)),
        }
    }
}
