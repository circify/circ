//! Terms in our datalog variant

use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

use rug::Integer;
use thiserror::Error;

use super::ty::Ty;

use crate::circify::{CirCtx, Embeddable};
use crate::front::zokrates::ZOKRATES_MODULUS_ARC;
use crate::ir::term::*;

/// A term
#[derive(Debug, Clone)]
pub struct T {
    /// The IR term that backs this
    pub ir: Term,
    /// the type
    pub ty: Ty,
}

impl T {
    /// Create a new term, checking that the explicit type and IR type agree.
    pub fn new(ir: Term, ty: Ty) -> Self {
        let ir_ty = check(&ir);
        let res = Self { ir, ty: ty.clone() };
        match (ty, ir_ty) {
            (Ty::Bool, Sort::Bool) | (Ty::Field, Sort::Field(_)) => res,
            (Ty::Uint(w), Sort::BitVector(w2)) if w as usize == w2 => res,
            _ => panic!("IR {} doesn't match datalog type {}", res.ir, res.ty),
        }
    }

    /// Assert this is a boolean, and get it.
    #[track_caller]
    pub fn as_bool(&self) -> Term {
        match &self.ty {
            &Ty::Bool => self.ir.clone(),
            _ => panic!("{} is not a bool", self),
        }
    }
}

/// Initialize a prime field literal
pub fn pf_lit<I>(i: I) -> T
where
    Integer: From<I>,
{
    T::new(
        leaf_term(Op::Const(Value::Field(FieldElem::new(
            Integer::from(i),
            ZOKRATES_MODULUS_ARC.clone(),
        )))),
        Ty::Field,
    )
}

/// Initialize a boolean literal
pub fn bool_lit(b: bool) -> T {
    T::new(leaf_term(Op::Const(Value::Bool(b))), Ty::Bool)
}

/// Initialize an unsigned integer literal
pub fn uint_lit(v: u64, w: u8) -> T {
    T::new(bv_lit(v, w as usize), Ty::Uint(w))
}

impl Ty {
    fn default(&self) -> T {
        match self {
            Self::Bool => bool_lit(false),
            Self::Uint(w) => uint_lit(0, *w),
            Self::Field => pf_lit(0),
        }
    }
}
impl Display for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.ir, self.ty)
    }
}

#[derive(Error, Debug)]
/// An error in circuit translation
pub enum Error {
    #[error("Cannot apply operator '{0}' to '{1}'")]
    /// Cannot apply this operator to this term
    InvalidUnOp(String, T),
    #[error("Cannot apply operator '{0}' to\n\t{1}\nand\n\t{2}")]
    /// Cannot apply this operator to these terms
    InvalidBinOp(String, T, T),
}

/// Fallible value
pub type Result<T> = std::result::Result<T, Error>;

/// Operator unary-
pub fn neg(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Field => Ok(T::new(term![PF_NEG; t.ir.clone()], t.ty)),
        Ty::Uint(_) => Ok(T::new(term![BV_NEG; t.ir.clone()], t.ty)),
        _ => Err(Error::InvalidUnOp("unary-".into(), t.clone())),
    }
}

/// Operator unary!
pub fn not(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Bool => Ok(T::new(term![Op::Not; t.ir.clone()], t.ty)),
        _ => Err(Error::InvalidUnOp("unary!".into(), t.clone())),
    }
}

/// Operator unary~
pub fn bitnot(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Uint(_) => Ok(T::new(term![BV_NOT; t.ir.clone()], t.ty)),
        _ => Err(Error::InvalidUnOp("unary~".into(), t.clone())),
    }
}

/// Operator +
pub fn add(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_ADD; s.ir.clone(), t.ir.clone()], t.ty))
        }
        (Ty::Field, Ty::Field) => Ok(T::new(term![PF_ADD; s.ir.clone(), t.ir.clone()], t.ty)),
        _ => Err(Error::InvalidBinOp("+".into(), s.clone(), t.clone())),
    }
}

/// Operator -
pub fn sub(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_SUB; s.ir.clone(), t.ir.clone()], t.ty))
        }
        (Ty::Field, Ty::Field) => Ok(T::new(
            term![PF_ADD; s.ir.clone(), term![PF_NEG; t.ir.clone()]],
            t.ty,
        )),
        _ => Err(Error::InvalidBinOp("-".into(), s.clone(), t.clone())),
    }
}

/// Operator *
pub fn mul(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_MUL; s.ir.clone(), t.ir.clone()], t.ty))
        }
        (Ty::Field, Ty::Field) => Ok(T::new(term![PF_MUL; s.ir.clone(), t.ir.clone()], t.ty)),
        _ => Err(Error::InvalidBinOp("*".into(), s.clone(), t.clone())),
    }
}

/// Operator /
pub fn div(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UDIV; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("/".into(), s.clone(), t.clone())),
    }
}

/// Operator %
pub fn rem(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UREM; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("%".into(), s.clone(), t.clone())),
    }
}

/// Operator ==
pub fn eq(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![EQ; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        (Ty::Bool, Ty::Bool) | (Ty::Field, Ty::Field) => {
            Ok(T::new(term![EQ; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(Error::InvalidBinOp("=".into(), s.clone(), t.clone())),
    }
}

/// Operator <<
pub fn shl(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_SHL; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("<<".into(), s.clone(), t.clone())),
    }
}

/// Operator >>
pub fn shr(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_LSHR; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp(">>".into(), s.clone(), t.clone())),
    }
}

/// Operator <
pub fn lt(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_ULT; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(Error::InvalidBinOp("<".into(), s.clone(), t.clone())),
    }
}

/// Operator >
pub fn gt(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UGT; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(Error::InvalidBinOp(">".into(), s.clone(), t.clone())),
    }
}

/// Operator <=
pub fn lte(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_ULE; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(Error::InvalidBinOp("<=".into(), s.clone(), t.clone())),
    }
}

/// Operator >=
pub fn gte(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UGE; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(Error::InvalidBinOp(">=".into(), s.clone(), t.clone())),
    }
}

/// Operator |
pub fn bitor(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_OR; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("|".into(), s.clone(), t.clone())),
    }
}

/// Operator &
pub fn bitand(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_AND; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("&".into(), s.clone(), t.clone())),
    }
}

/// Operator ^
pub fn bitxor(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_XOR; s.ir.clone(), t.ir.clone()], t.ty))
        }
        _ => Err(Error::InvalidBinOp("^".into(), s.clone(), t.clone())),
    }
}

/// Operator &&
pub fn and(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Bool, Ty::Bool) => Ok(T::new(term![AND; s.ir.clone(), t.ir.clone()], Ty::Bool)),
        _ => Err(Error::InvalidBinOp("&&".into(), s.clone(), t.clone())),
    }
}

/// Operator ||
pub fn or(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Bool, Ty::Bool) => Ok(T::new(term![OR; s.ir.clone(), t.ir.clone()], Ty::Bool)),
        _ => Err(Error::InvalidBinOp("||".into(), s.clone(), t.clone())),
    }
}

/// Operator ||
pub fn uint_to_field(s: &T) -> Result<T> {
    match &s.ty {
        Ty::Uint(_) => Ok(T::new(term![BV_NEG; s.ir.clone()], s.ty)),
        _ => Err(Error::InvalidBinOp("||".into(), s.clone(), s.clone())),
    }
}

/// Datalog lang def
pub struct Datalog {
    modulus: Arc<Integer>,
}

impl Embeddable for Datalog {
    type T = T;
    type Ty = Ty;
    fn declare(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        raw_name: String,
        _user_name: Option<String>,
        visibility: Option<PartyId>,
    ) -> Self::T {
        let get_int_val = || -> Integer { panic!("No values in Datalog") };
        match ty {
            Ty::Bool => T::new(
                ctx.cs.borrow_mut().new_var(
                    &raw_name,
                    Sort::Bool,
                    || Value::Bool(get_int_val() != 0),
                    visibility,
                ),
                Ty::Bool,
            ),
            Ty::Field => T::new(
                ctx.cs.borrow_mut().new_var(
                    &raw_name,
                    Sort::Field(self.modulus.clone()),
                    || Value::Field(FieldElem::new(get_int_val(), self.modulus.clone())),
                    visibility,
                ),
                Ty::Field,
            ),
            Ty::Uint(w) => T::new(
                ctx.cs.borrow_mut().new_var(
                    &raw_name,
                    Sort::BitVector(*w as usize),
                    || Value::BitVector(BitVector::new(get_int_val(), *w as usize)),
                    visibility,
                ),
                *ty,
            ),
        }
    }
    fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        if t.ty == f.ty {
            T::new(
                term![Op::Ite; cond.clone(), t.ir.clone(), f.ir.clone()],
                t.ty,
            )
        } else {
            panic!("Cannot ITE {} and {}", t, f)
        }
    }
    fn assign(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        name: String,
        t: Self::T,
        visibility: Option<PartyId>,
    ) -> Self::T {
        assert!(&t.ty == ty);
        T::new(ctx.cs.borrow_mut().assign(&name, t.ir, visibility), *ty)
    }
    fn values(&self) -> bool {
        false
    }

    fn type_of(&self, term: &Self::T) -> Self::Ty {
        term.ty
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }
}

impl Datalog {
    /// Initialize the Datalog lang def
    pub fn new() -> Self {
        Self {
            modulus: ZOKRATES_MODULUS_ARC.clone(),
        }
    }
}
