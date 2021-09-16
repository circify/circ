//! C Terms
use crate::front::c::types::Type;
use crate::ir::term::*;
use std::fmt::{self, Display, Formatter};

pub enum CTermData {
    CBool(Term),
    CInt(usize, Term),
}

impl CTermData {
    pub fn type_(&self) -> Type {
        match self {
            Self::CBool(_) => Type::Bool,
            Self::CInt(w, _) => Type::Uint(*w),
        }
    }
}

impl Display for CTermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CTermData::CBool(x) => write!(f, "Bool({})", x),
            CTermData::CInt(_, x) => write!(f, "CInt({})", x),
        }
    }
}

pub struct CTerm {
    term: CTermData,
    udef: bool,
}

fn wrap_bin_op(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: CTerm,
    b: CTerm,
) -> Result<CTerm, String> {
    match (a.term, b.term, fu, fb) {
        (CTermData::CInt(na, a), CTermData::CInt(nb, b), Some(fu), _) if na == nb => Ok(CTerm {
            term: CTermData::CInt(na, fu(a, b)),
            udef: false,
        }),
        (CTermData::CBool(a), CTermData::CBool(b), _, Some(fb)) => Ok(CTerm {
            term: CTermData::CBool(fb(a, b)),
            udef: false,
        }),
        (x, y, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn add_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Add); a, b]
}

pub fn add(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_op("+", Some(add_uint), None, a, b)
}

// fn sub_uint(a: Term, b: Term) -> Term {
//     term![Op::BvBinOp(BvBinOp::Sub); a, b]
// }

// pub fn sub(a: Term, b: Term) -> Result<Term, String> {
//     wrap_bin_op("-", Some(sub_uint), None, a, b)
// }

// fn mul_uint(a: Term, b: Term) -> Term {
//     term![Op::BvNaryOp(BvNaryOp::Mul); a, b]
// }

// pub fn mul(a: Term, b: Term) -> Result<Term, String> {
//     wrap_bin_op("*", Some(mul_uint), None, a, b)
// }
