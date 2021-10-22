//! C Types
use crate::front::c::term::CTerm;
use crate::front::c::term::CTermData;
use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int(bool, usize),
    Array(usize, Box<Ty>),
}

impl Ty {
    pub fn default(&self) -> CTerm {
        match self {
            Self::Bool => CTerm {
                term: CTermData::CBool(leaf_term(Op::Const(Value::Bool(false)))),
                udef: false,
            },
            Self::Int(s, w) => CTerm {
                term: CTermData::CInt(*s, *w, bv_lit(0, *w)),
                udef: false,
            },
            Self::Array(n, b) => CTerm {
                term: CTermData::CArray((**b).clone(), vec![b.default(); *n]),
                udef: false,
            },
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Int(s, w) => if *s { write!(f, "s{}", w) } else { write!(f, "u{}", w) },
            Ty::Array(n, b) => write!(f, "{}[{}]", b, n),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

pub fn is_arith_type(t: &CTerm) -> bool {
    let ty = t.term.type_();
    match ty {
        Ty::Int(_,_) | Ty::Bool => true,
        _ => false,
    }
}
