//! C Types
use crate::front::c::term::CTerm;
use crate::front::c::term::CTermData;
use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Uint(usize),
}

impl Ty {
    pub fn default(&self) -> CTerm {
        match self {
            Self::Bool => CTerm {
                term: CTermData::CBool(leaf_term(Op::Const(Value::Bool(false)))),
                udef: false,
            },
            Self::Uint(w) => CTerm {
                term: CTermData::CInt(*w, bv_lit(0, *w)),
                udef: false,
            }
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Uint(w) => write!(f, "u{}", w),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}