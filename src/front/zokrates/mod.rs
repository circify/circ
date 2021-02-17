#![allow(dead_code)]
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};

use rug::Integer;

use crate::ir::term::*;

#[derive(Clone, PartialEq, Eq)]
enum Ty {
    Uint(usize),
    Bool,
    Field,
    Struct(String, BTreeMap<String, Ty>),
    Array(usize, Box<Ty>),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Uint(w) => write!(f, "u{}", w),
            Ty::Field => write!(f, "field"),
            Ty::Struct(n, _) => write!(f, "{}", n),
            Ty::Array(n, b) => write!(f, "{}[{}]", b, n),
        }
    }
}

#[derive(Clone)]
enum T {
    Uint(usize, Term),
    Bool(Term),
    Field(Term),
    Array(Ty, usize, Term),
    Struct(String, BTreeMap<String, Term>),
}

impl Display for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            T::Bool(x) => write!(f, "{}", x),
            T::Uint(_, x) => write!(f, "{}", x),
            T::Field(x) => write!(f, "{}", x),
            T::Struct(_, _) => write!(f, "struct"),
            T::Array(_, _, _) => write!(f, "array"),
        }
    }
}

fn wrap_bin_op(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    ff: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: T,
    b: T,
) -> Result<T, String> {
    match (a, b, fu, ff, fb) {
        (T::Uint(na, a), T::Uint(nb, b), Some(fu), _, _) if na == nb => Ok(T::Uint(na, fu(a, b))),
        (T::Bool(a), T::Bool(b), _, _, Some(fb)) => Ok(T::Bool(fb(a, b))),
        (T::Field(a), T::Field(b), _, Some(ff), _) => Ok(T::Field(ff(a, b))),
        (x, y, _, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn wrap_bin_pred(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    ff: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: T,
    b: T,
) -> Result<T, String> {
    match (a, b, fu, ff, fb) {
        (T::Uint(na, a), T::Uint(nb, b), Some(fu), _, _) if na == nb => Ok(T::Bool(fu(a, b))),
        (T::Bool(a), T::Bool(b), _, _, Some(fb)) => Ok(T::Bool(fb(a, b))),
        (T::Field(a), T::Field(b), _, Some(ff), _) => Ok(T::Bool(ff(a, b))),
        (x, y, _, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn add_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Add); a, b]
}

fn add_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Add); a, b]
}

fn add(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("+", Some(add_uint), Some(add_field), None, a, b)
}

fn sub_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Sub); a, b]
}

fn sub_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Add); a, term![Op::PfUnOp(PfUnOp::Neg); b]]
}

fn sub(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("-", Some(sub_uint), Some(sub_field), None, a, b)
}

fn mul_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Mul); a, b]
}

fn mul_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Mul); a, b]
}

fn mul(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("*", Some(mul_uint), Some(mul_field), None, a, b)
}

fn div_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Udiv); a, b]
}

fn div_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Mul); a, term![Op::PfUnOp(PfUnOp::Recip); b]]
}

fn div(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("/", Some(div_uint), Some(div_field), None, a, b)
}

fn bitand_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::And); a, b]
}

fn bitand(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("&", Some(bitand_uint), None, None, a, b)
}

fn bitor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Or); a, b]
}

fn bitor(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("|", Some(bitor_uint), None, None, a, b)
}

fn bitxor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Xor); a, b]
}

fn bitxor(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("^", Some(bitxor_uint), None, None, a, b)
}

fn or_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::Or); a, b]
}

fn or(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("||", None, None, Some(or_bool), a, b)
}

fn and_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::And); a, b]
}

fn and(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("&&", None, None, Some(and_bool), a, b)
}

fn eq_base(a: Term, b: Term) -> Term {
    term![Op::Eq; a, b]
}

fn eq(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("==", Some(eq_base), Some(eq_base), Some(eq_base), a, b)
}

fn neq_base(a: Term, b: Term) -> Term {
    term![Op::Not; term![Op::Eq; a, b]]
}

fn neq(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("!=", Some(neq_base), Some(neq_base), Some(neq_base), a, b)
}

fn ult_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ult); a, b]
}

fn ult(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<", Some(ult_uint), None, None, a, b)
}

fn ule_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ule); a, b]
}

fn ule(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<=", Some(ule_uint), None, None, a, b)
}

fn ugt_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ugt); a, b]
}

fn ugt(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred(">", Some(ugt_uint), None, None, a, b)
}

fn uge_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Uge); a, b]
}

fn uge(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred(">=", Some(uge_uint), None, None, a, b)
}

fn wrap_un_op(
    name: &str,
    fu: Option<fn(Term) -> Term>,
    ff: Option<fn(Term) -> Term>,
    fb: Option<fn(Term) -> Term>,
    a: T,
) -> Result<T, String> {
    match (a, fu, ff, fb) {
        (T::Uint(na, a), Some(fu), _, _) => Ok(T::Uint(na, fu(a))),
        (T::Bool(a), _, _, Some(fb)) => Ok(T::Bool(fb(a))),
        (T::Field(a), _, Some(ff), _) => Ok(T::Field(ff(a))),
        (x, _, _, _) => Err(format!("Cannot perform op '{}' on {}", name, x)),
    }
}

fn neg_field(a: Term) -> Term {
    term![Op::PfUnOp(PfUnOp::Neg); a]
}

fn neg_uint(a: Term) -> Term {
    term![Op::BvUnOp(BvUnOp::Neg); a]
}

fn neg(a: T) -> Result<T, String> {
    wrap_un_op("unary-", Some(neg_uint), Some(neg_field), None, a)
}

fn not_bool(a: Term) -> Term {
    term![Op::Not; a]
}

fn not_uint(a: Term) -> Term {
    term![Op::BvUnOp(BvUnOp::Not); a]
}

fn not(a: T) -> Result<T, String> {
    wrap_un_op("!", Some(not_uint), None, Some(not_bool), a)
}

fn const_int(a: T) -> Result<Integer, String> {
    let s = match &a {
        T::Field(b) => match &b.op {
            Op::Const(Value::Field(f)) => Some(f.i().clone()),
            _ => None,
        },
        T::Uint(_, i) => match &i.op {
            Op::Const(Value::BitVector(f)) => Some(f.uint().clone()),
            _ => None,
        },
        _ => None,
    };
    s.ok_or_else(|| format!("{} is not a constant integer", a))
}

fn bool(a: T) -> Result<Term, String> {
    match a {
        T::Bool(b) => Ok(b),
        a => Err(format!("{} is not a boolean", a)),
    }
}

fn wrap_shift(name: &str, op: BvBinOp, a: T, b: T) -> Result<T, String> {
    let bc = const_int(b)?;
    match a {
        T::Uint(na, a) => Ok(T::Uint(na, term![Op::BvBinOp(op); a, bv_lit(bc, na)])),
        x => Err(format!("Cannot perform op '{}' on {} and {}", name, x, bc)),
    }
}

fn shl(a: T, b: T) -> Result<T, String> {
    wrap_shift("<<", BvBinOp::Shl, a, b)
}

fn shr(a: T, b: T) -> Result<T, String> {
    wrap_shift(">>", BvBinOp::Lshr, a, b)
}

fn ite(c: Term, a: T, b: T) -> Result<T, String> {
    match (a, b) {
        (T::Uint(na, a), T::Uint(nb, b)) if na == nb => Ok(T::Uint(na, term![Op::Ite; c, a, b])),
        (T::Bool(a), T::Bool(b)) => Ok(T::Bool(term![Op::Ite; c, a, b])),
        (T::Field(a), T::Field(b)) => Ok(T::Field(term![Op::Ite; c, a, b])),
        (T::Array(ta, na, a), T::Array(tb, nb, b)) if na == nb && ta == tb => {
            Ok(T::Array(ta.clone(), na, term![Op::Ite; c, a, b]))
        }
        (T::Struct(na, a), T::Struct(nb, b)) if na == nb => Ok(T::Struct(na.clone(), {
            a.into_iter()
                .zip(b.into_iter())
                .map(|((af, av), (bf, bv))| {
                    if af == bf {
                        Ok((af, term![Op::Ite; c.clone(), av, bv]))
                    } else {
                        Err(format!("Field mismatch: {} vs {}", af, bf))
                    }
                })
                .collect::<Result<BTreeMap<_, _>, String>>()?
        })),
        (x, y) => Err(format!("Cannot perform ITE on {} and {}", x, y)),
    }
}

fn cond(c: T, a: T, b: T) -> Result<T, String> {
    ite(bool(c)?, a, b)
}
