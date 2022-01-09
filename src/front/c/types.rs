//! C Types
use crate::front::c::term::CTerm;
use crate::front::c::term::CTermData;
use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int(bool, usize),
    Array(Option<usize>, Box<Ty>),
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
            Self::Array(_s, ty) => CTerm {
                term: CTermData::CArray(*ty.clone(), None),
                udef: false,
            },
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Int(s, w) => {
                if *s {
                    write!(f, "s{}", w)
                } else {
                    write!(f, "u{}", w)
                }
            }
            Ty::Array(_, b) => write!(f, "{}[]", b),
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
    matches!(ty, Ty::Int(_, _) | Ty::Bool)
}

pub fn is_signed_int(ty: Ty) -> bool {
    if let Ty::Int(s, w) = ty {
        if w == 8 || w == 16 || w == 32 || w == 64 {
            return s;
        }
        return false;
    }
    false
}

pub fn is_unsigned_int(ty: Ty) -> bool {
    if let Ty::Int(s, w) = ty {
        if !s && (w == 8 || w == 16 || w == 32 || w == 64) {
            return !s;
        }
        return s;
    }
    false
}

pub fn is_integer_type(ty: Ty) -> bool {
    is_signed_int(ty.clone()) || is_unsigned_int(ty)
}

pub fn int_conversion_rank(ty: Ty) -> usize {
    match ty {
        Ty::Int(_, w) => w,
        Ty::Bool => 1,
        _ => panic!("int_conversion_rank received a non-int type: {:#?}", ty),
    }
}

pub fn _total_num_bits(ty: Ty) -> usize {
    match ty {
        Ty::Int(_, w) => w,
        Ty::Bool => 1,
        Ty::Array(s, t) => s.unwrap() * num_bits(*t),
    }
}

pub fn num_bits(ty: Ty) -> usize {
    match ty {
        Ty::Int(_, w) => w,
        Ty::Bool => 1,
        Ty::Array(_, _) => 32,
    }
}

pub fn inner_ty(ty: Ty) -> Ty {
    match ty {
        Ty::Int(_, _) => ty,
        Ty::Bool => ty,
        Ty::Array(_, t) => *t,
    }
}
