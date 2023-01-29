//! Terms in our datalog variant

use std::fmt::{self, Display, Formatter};

use rug::Integer;

use super::error::ErrorKind;
use super::ty::Ty;

use crate::cfg::cfg;
use crate::circify::{CirCtx, Embeddable, Typed};
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
        let res = Self { ir, ty };
        Self::check_ty(&ir_ty, &res.ty);
        res
    }

    fn check_ty(ir: &Sort, ty: &Ty) {
        match (ty, ir) {
            (Ty::Bool, Sort::Bool) | (Ty::Field, Sort::Field(_)) => {}
            (Ty::Uint(w), Sort::BitVector(w2)) if *w as usize == *w2 => {}
            (Ty::Array(l, t), Sort::Array(_, t2, l2)) if l == l2 => Self::check_ty(t2, t),
            _ => panic!("IR sort {} doesn't match datalog type {}", ir, ty),
        }
    }

    /// Assert this is a boolean, and get it.
    #[track_caller]
    pub fn as_bool(&self) -> Term {
        match &self.ty {
            Ty::Bool => self.ir.clone(),
            _ => panic!("{} is not a bool", self),
        }
    }
}

/// A fallible result
pub type Result<T> = std::result::Result<T, ErrorKind>;

/// Initialize a prime field literal
pub fn pf_lit<I>(i: I) -> T
where
    Integer: From<I>,
{
    T::new(pf_ir_lit(i), Ty::Field)
}
/// Initialize a prime field literal
pub fn pf_ir_lit<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(cfg().field().new_v(i))))
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
    fn sort(&self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Uint(w) => Sort::BitVector(*w as usize),
            Self::Field => Sort::Field(cfg().field().clone()),
            Self::Array(n, b) => Sort::Array(
                Box::new(Sort::Field(cfg().field().clone())),
                Box::new(b.sort()),
                *n,
            ),
        }
    }
    fn default_ir_term(&self) -> Term {
        self.sort().default_term()
    }
    fn default(&self) -> T {
        T::new(self.default_ir_term(), self.clone())
    }
}
impl Display for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.ir, self.ty)
    }
}

/// Operator unary-
pub fn neg(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Field => Ok(T::new(term![PF_NEG; t.ir.clone()], t.ty.clone())),
        Ty::Uint(_) => Ok(T::new(term![BV_NEG; t.ir.clone()], t.ty.clone())),
        _ => Err(ErrorKind::InvalidUnOp("unary-".into(), t.clone())),
    }
}

/// Operator unary!
pub fn not(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Bool => Ok(T::new(term![Op::Not; t.ir.clone()], t.ty.clone())),
        _ => Err(ErrorKind::InvalidUnOp("unary!".into(), t.clone())),
    }
}

/// Operator unary~
pub fn bitnot(t: &T) -> Result<T> {
    match &t.ty {
        Ty::Uint(_) => Ok(T::new(term![BV_NOT; t.ir.clone()], t.ty.clone())),
        _ => Err(ErrorKind::InvalidUnOp("unary~".into(), t.clone())),
    }
}

/// Operator +
pub fn add(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_ADD; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        (Ty::Field, Ty::Field) => Ok(T::new(
            term![PF_ADD; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("+".into(), s.clone(), t.clone())),
    }
}

/// Operator -
pub fn sub(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_SUB; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        (Ty::Field, Ty::Field) => Ok(T::new(
            term![PF_ADD; s.ir.clone(), term![PF_NEG; t.ir.clone()]],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("-".into(), s.clone(), t.clone())),
    }
}

/// Operator *
pub fn mul(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_MUL; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        (Ty::Field, Ty::Field) => Ok(T::new(
            term![PF_MUL; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("*".into(), s.clone(), t.clone())),
    }
}

/// Operator /
pub fn div(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_UDIV; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("/".into(), s.clone(), t.clone())),
    }
}

/// Operator %
pub fn rem(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_UREM; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("%".into(), s.clone(), t.clone())),
    }
}

/// Operator ==
pub fn eq(s: &T, t: &T) -> Result<T> {
    if s.ty == t.ty {
        Ok(T::new(term![EQ; s.ir.clone(), t.ir.clone()], Ty::Bool))
    } else {
        Err(ErrorKind::InvalidBinOp("=".into(), s.clone(), t.clone()))
    }
}

/// Operator <<
pub fn shl(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_SHL; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("<<".into(), s.clone(), t.clone())),
    }
}

/// Operator >>
pub fn shr(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_LSHR; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp(">>".into(), s.clone(), t.clone())),
    }
}

/// Operator <
pub fn lt(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_ULT; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(ErrorKind::InvalidBinOp("<".into(), s.clone(), t.clone())),
    }
}

/// Operator >
pub fn gt(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UGT; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(ErrorKind::InvalidBinOp(">".into(), s.clone(), t.clone())),
    }
}

/// Operator <=
pub fn lte(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_ULE; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(ErrorKind::InvalidBinOp("<=".into(), s.clone(), t.clone())),
    }
}

/// Operator >=
pub fn gte(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => {
            Ok(T::new(term![BV_UGE; s.ir.clone(), t.ir.clone()], Ty::Bool))
        }
        _ => Err(ErrorKind::InvalidBinOp(">=".into(), s.clone(), t.clone())),
    }
}

/// Operator |
pub fn bitor(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_OR; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("|".into(), s.clone(), t.clone())),
    }
}

/// Operator &
pub fn bitand(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_AND; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("&".into(), s.clone(), t.clone())),
    }
}

/// Operator ^
pub fn bitxor(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Uint(w1), Ty::Uint(w2)) if w1 == w2 => Ok(T::new(
            term![BV_XOR; s.ir.clone(), t.ir.clone()],
            t.ty.clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp("^".into(), s.clone(), t.clone())),
    }
}

/// Operator &&
pub fn and(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Bool, Ty::Bool) => Ok(T::new(term![AND; s.ir.clone(), t.ir.clone()], Ty::Bool)),
        _ => Err(ErrorKind::InvalidBinOp("&&".into(), s.clone(), t.clone())),
    }
}

/// Operator ||
pub fn or(s: &T, t: &T) -> Result<T> {
    match (&s.ty, &t.ty) {
        (Ty::Bool, Ty::Bool) => Ok(T::new(term![OR; s.ir.clone(), t.ir.clone()], Ty::Bool)),
        _ => Err(ErrorKind::InvalidBinOp("||".into(), s.clone(), t.clone())),
    }
}

/// Uint to field
pub fn uint_to_field(s: &T) -> Result<T> {
    match &s.ty {
        Ty::Uint(_) => Ok(T::new(
            term![Op::UbvToPf(cfg().field().clone()); s.ir.clone()],
            Ty::Field,
        )),
        _ => Err(ErrorKind::InvalidUnOp("to_field".into(), s.clone())),
    }
}

/// Uint to field
pub fn array_idx(a: &T, i: &T) -> Result<T> {
    match (&a.ty, &i.ty) {
        (Ty::Array(_, elem_ty), &Ty::Field) => Ok(T::new(
            term![Op::Select; a.ir.clone(), i.ir.clone()],
            (**elem_ty).clone(),
        )),
        _ => Err(ErrorKind::InvalidBinOp(
            "array[idx]".into(),
            a.clone(),
            i.clone(),
        )),
    }
}

/// Datalog lang def
pub struct Datalog;

impl Typed<Ty> for T {
    fn type_(&self) -> Ty {
        self.ty.clone()
    }
}

impl Embeddable for Datalog {
    type T = T;
    type Ty = Ty;
    fn create_uninit(&self, _ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T {
        ty.default()
    }
    fn declare_input(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        name: String,
        visibility: Option<PartyId>,
        precompute: Option<T>,
    ) -> Self::T {
        T::new(
            ctx.cs
                .borrow_mut()
                .new_var(&name, ty.sort(), visibility, precompute.map(|v| v.ir)),
            ty.clone(),
        )
    }
    fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        if t.ty == f.ty {
            T::new(term![Op::Ite; cond, t.ir, f.ir], t.ty)
        } else {
            panic!("Cannot ITE {} and {}", t, f)
        }
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }
}

impl Default for Datalog {
    fn default() -> Self {
        Self::new()
    }
}

impl Datalog {
    /// Initialize the Datalog lang def
    pub fn new() -> Self {
        Self
    }
}
