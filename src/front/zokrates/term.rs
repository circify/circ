//! Symbolic ZoKrates terms
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Display, Formatter};
use std::sync::Arc;

use lazy_static::lazy_static;
use rug::Integer;

use crate::circify::{CirCtx, Embeddable};
use crate::ir::term::*;

lazy_static! {
    // TODO: handle this better
    /// The modulus for ZoKrates.
    pub static ref ZOKRATES_MODULUS: Integer = Integer::from_str_radix(
        "52435875175126190479447740508185965837690552500527637822603658699938581184513",
        10
    )
    .unwrap();
    /// The modulus for ZoKrates, as an ARC
    pub static ref ZOKRATES_MODULUS_ARC: Arc<Integer> = Arc::new(ZOKRATES_MODULUS.clone());
}

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
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

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Ty {
    fn default(&self) -> T {
        match self {
            Self::Bool => T::Bool(leaf_term(Op::Const(Value::Bool(false)))),
            Self::Uint(w) => T::Uint(*w, bv_lit(0, *w)),
            Self::Field => T::Field(pf_lit(0)),
            Self::Array(n, b) => T::Array((**b).clone(), vec![b.default(); *n]),
            Self::Struct(n, fs) => T::Struct(
                n.clone(),
                fs.iter()
                    .map(|(f_name, f_ty)| (f_name.to_owned(), f_ty.default()))
                    .collect(),
            ),
        }
    }
}

#[derive(Clone)]
pub enum T {
    Uint(usize, Term),
    Bool(Term),
    Field(Term),
    /// TODO: special case primitive arrays with Vec<T>.
    Array(Ty, Vec<T>),
    Struct(String, BTreeMap<String, T>),
}

impl T {
    pub fn type_(&self) -> Ty {
        match self {
            T::Uint(w, _) => Ty::Uint(*w),
            T::Bool(_) => Ty::Bool,
            T::Field(_) => Ty::Field,
            T::Array(b, v) => Ty::Array(v.len(), Box::new(b.clone())),
            T::Struct(name, map) => Ty::Struct(
                name.clone(),
                map.iter()
                    .map(|(f_name, f_term)| (f_name.clone(), f_term.type_()))
                    .collect(),
            ),
        }
    }
    /// Get all IR terms inside this value, as a list.
    pub fn terms(&self) -> Vec<Term> {
        let mut output: Vec<Term> = Vec::new();
        fn terms_tail(term: &T, output: &mut Vec<Term>) {
            match term {
                T::Bool(b) => output.push(b.clone()),
                T::Uint(_, b) => output.push(b.clone()),
                T::Field(b) => output.push(b.clone()),
                T::Array(_, v) => v.iter().for_each(|v| terms_tail(v, output)),
                T::Struct(_, map) => map.iter().for_each(|(_, v)| terms_tail(v, output)),
            }
        }
        terms_tail(self, &mut output);
        output
    }
    pub fn unwrap_array(self) -> Result<Vec<T>, String> {
        match self {
            T::Array(_, v) => Ok(v),
            s => Err(format!("Not an array: {}", s)),
        }
    }
    pub fn new_array(v: Vec<T>) -> Result<T, String> {
        array(v)
    }
}

impl Display for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            T::Bool(x) => write!(f, "Bool({})", x),
            T::Uint(_, x) => write!(f, "Uint({})", x),
            T::Field(x) => write!(f, "Field({})", x),
            T::Struct(_, _) => write!(f, "struct"),
            T::Array(_, _) => write!(f, "array"),
        }
    }
}

impl fmt::Debug for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
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

pub fn add(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("+", Some(add_uint), Some(add_field), None, a, b)
}

fn sub_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Sub); a, b]
}

fn sub_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Add); a, term![Op::PfUnOp(PfUnOp::Neg); b]]
}

pub fn sub(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("-", Some(sub_uint), Some(sub_field), None, a, b)
}

fn mul_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Mul); a, b]
}

fn mul_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Mul); a, b]
}

pub fn mul(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("*", Some(mul_uint), Some(mul_field), None, a, b)
}

fn div_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Udiv); a, b]
}

fn div_field(a: Term, b: Term) -> Term {
    term![Op::PfNaryOp(PfNaryOp::Mul); a, term![Op::PfUnOp(PfUnOp::Recip); b]]
}

pub fn div(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("/", Some(div_uint), Some(div_field), None, a, b)
}

fn rem_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Urem); a, b]
}

pub fn rem(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("%", Some(rem_uint), None, None, a, b)
}

fn bitand_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::And); a, b]
}

pub fn bitand(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("&", Some(bitand_uint), None, None, a, b)
}

fn bitor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Or); a, b]
}

pub fn bitor(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("|", Some(bitor_uint), None, None, a, b)
}

fn bitxor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Xor); a, b]
}

pub fn bitxor(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("^", Some(bitxor_uint), None, None, a, b)
}

fn or_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::Or); a, b]
}

pub fn or(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("||", None, None, Some(or_bool), a, b)
}

fn and_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::And); a, b]
}

pub fn and(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("&&", None, None, Some(and_bool), a, b)
}

fn eq_base(a: Term, b: Term) -> Term {
    term![Op::Eq; a, b]
}

pub fn eq(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("==", Some(eq_base), Some(eq_base), Some(eq_base), a, b)
}

fn neq_base(a: Term, b: Term) -> Term {
    term![Op::Not; term![Op::Eq; a, b]]
}

pub fn neq(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("!=", Some(neq_base), Some(neq_base), Some(neq_base), a, b)
}

fn ult_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ult); a, b]
}

pub fn ult(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<", Some(ult_uint), None, None, a, b)
}

fn ule_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ule); a, b]
}

pub fn ule(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<=", Some(ule_uint), None, None, a, b)
}

fn ugt_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ugt); a, b]
}

pub fn ugt(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred(">", Some(ugt_uint), None, None, a, b)
}

fn uge_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Uge); a, b]
}

pub fn uge(a: T, b: T) -> Result<T, String> {
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

#[allow(dead_code)]
// Missing from ZoKrates.
pub fn neg(a: T) -> Result<T, String> {
    wrap_un_op("unary-", Some(neg_uint), Some(neg_field), None, a)
}

fn not_bool(a: Term) -> Term {
    term![Op::Not; a]
}

fn not_uint(a: Term) -> Term {
    term![Op::BvUnOp(BvUnOp::Not); a]
}

pub fn not(a: T) -> Result<T, String> {
    wrap_un_op("!", Some(not_uint), None, Some(not_bool), a)
}

pub fn const_int(a: T) -> Result<Integer, String> {
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

pub fn bool(a: T) -> Result<Term, String> {
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

pub fn shl(a: T, b: T) -> Result<T, String> {
    wrap_shift("<<", BvBinOp::Shl, a, b)
}

pub fn shr(a: T, b: T) -> Result<T, String> {
    wrap_shift(">>", BvBinOp::Lshr, a, b)
}

fn ite(c: Term, a: T, b: T) -> Result<T, String> {
    match (a, b) {
        (T::Uint(na, a), T::Uint(nb, b)) if na == nb => Ok(T::Uint(na, term![Op::Ite; c, a, b])),
        (T::Bool(a), T::Bool(b)) => Ok(T::Bool(term![Op::Ite; c, a, b])),
        (T::Field(a), T::Field(b)) => Ok(T::Field(term![Op::Ite; c, a, b])),
        (T::Array(ta, a), T::Array(tb, b)) if a.len() == b.len() && ta == tb => Ok(T::Array(
            ta,
            a.into_iter()
                .zip(b.into_iter())
                .map(|(a_i, b_i)| ite(c.clone(), a_i, b_i))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        (T::Struct(na, a), T::Struct(nb, b)) if na == nb => Ok(T::Struct(na.clone(), {
            a.into_iter()
                .zip(b.into_iter())
                .map(|((af, av), (bf, bv))| {
                    if af == bf {
                        Ok((af, ite(c.clone(), av, bv)?))
                    } else {
                        Err(format!("Field mismatch: {} vs {}", af, bf))
                    }
                })
                .collect::<Result<BTreeMap<_, _>, String>>()?
        })),
        (x, y) => Err(format!("Cannot perform ITE on {} and {}", x, y)),
    }
}

pub fn cond(c: T, a: T, b: T) -> Result<T, String> {
    ite(bool(c)?, a, b)
}

pub fn pf_lit<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(Value::Field(FieldElem::new(
        Integer::from(i),
        ZOKRATES_MODULUS_ARC.clone(),
    ))))
}

pub fn slice(array: T, start: Option<usize>, end: Option<usize>) -> Result<T, String> {
    match array {
        T::Array(b, mut list) => {
            let start = start.unwrap_or(0);
            let end = end.unwrap_or(list.len());
            Ok(T::Array(b, list.drain(start..end).collect()))
        }
        a => Err(format!("Cannot slice {}", a)),
    }
}

pub fn field_select(struct_: &T, field: &str) -> Result<T, String> {
    match struct_ {
        T::Struct(_, map) => map
            .get(field)
            .cloned()
            .ok_or_else(|| format!("No field '{}'", field)),
        a => Err(format!("{} is not a struct", a)),
    }
}

pub fn field_store(struct_: T, field: &str, val: T) -> Result<T, String> {
    match struct_ {
        T::Struct(name, mut map) => Ok(T::Struct(name, {
            if map.insert(field.to_owned(), val).is_some() {
                map
            } else {
                return Err(format!("No '{}' field", field));
            }
        })),
        a => Err(format!("{} is not a struct", a)),
    }
}

pub fn array_select(array: T, idx: T) -> Result<T, String> {
    match (array, idx) {
        (T::Array(_, list), T::Field(idx)) => {
            let mut it = list.into_iter().enumerate();
            let first = it
                .next()
                .ok_or_else(|| format!("Cannot index empty array"))?;
            it.fold(Ok(first.1), |acc, (i, elem)| {
                ite(term![Op::Eq; pf_lit(i), idx.clone()], elem, acc?)
            })
        }
        (a, b) => Err(format!("Cannot index {} by {}", b, a)),
    }
}

pub fn array_store(array: T, idx: T, val: T) -> Result<T, String> {
    match (array, idx) {
        (T::Array(ty, list), T::Field(idx)) => Ok(T::Array(
            ty,
            list.into_iter()
                .enumerate()
                .map(|(i, elem)| ite(term![Op::Eq; pf_lit(i), idx.clone()], val.clone(), elem))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        (a, b) => Err(format!("Cannot index {} by {}", b, a)),
    }
}

fn array<I: IntoIterator<Item = T>>(elems: I) -> Result<T, String> {
    let v: Vec<T> = elems.into_iter().collect();
    if let Some(e) = v.first() {
        let ty = e.type_();
        if v.iter().skip(1).any(|a| a.type_() != ty) {
            Err(format!("Inconsistent types in array"))
        } else {
            Ok(T::Array(ty, v))
        }
    } else {
        Err(format!("Empty array"))
    }
}

pub fn uint_to_bits(u: T) -> Result<T, String> {
    match u {
        T::Uint(n, t) => Ok(T::Array(
            Ty::Bool,
            (0..n)
                .map(|i| T::Bool(term![Op::BvBit(i); t.clone()]))
                .collect(),
        )),
        u => Err(format!("Cannot do uint-to-bits on {}", u)),
    }
}

pub fn uint_from_bits(u: T) -> Result<T, String> {
    match u {
        T::Array(Ty::Bool, list) => match list.len() {
            8 | 16 | 32 => Ok(T::Uint(
                list.len(),
                term(
                    Op::BvConcat,
                    list.into_iter()
                        .map(|z: T| -> Result<Term, String> { Ok(term![Op::BoolToBv; bool(z)?]) })
                        .collect::<Result<Vec<_>, _>>()?,
                ),
            )),
            l => Err(format!("Cannot do uint-from-bits on len {} array", l,)),
        },
        u => Err(format!("Cannot do uint-from-bits on {}", u)),
    }
}

pub fn field_to_bits(f: T) -> Result<T, String> {
    match f {
        T::Field(t) => {
            let u = term![Op::PfToBv(254); t];
            Ok(T::Array(
                Ty::Bool,
                (0..254)
                    .map(|i| T::Bool(term![Op::BvBit(i); u.clone()]))
                    .collect(),
            ))
        }
        u => Err(format!("Cannot do field-to-bits on {}", u)),
    }
}

pub struct ZoKrates {
    values: Option<HashMap<String, Integer>>,
    modulus: Arc<Integer>,
}

fn field_name(struct_name: &str, field_name: &str) -> String {
    format!("{}.{}", struct_name, field_name)
}

fn idx_name(struct_name: &str, idx: usize) -> String {
    format!("{}.{}", struct_name, idx)
}

impl ZoKrates {
    pub fn new(values: Option<HashMap<String, Integer>>) -> Self {
        Self {
            values,
            modulus: ZOKRATES_MODULUS_ARC.clone(),
        }
    }
}

impl Embeddable for ZoKrates {
    type T = T;
    type Ty = Ty;
    fn declare(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        raw_name: String,
        user_name: Option<String>,
        visibility: Option<PartyId>,
    ) -> Self::T {
        let get_int_val = || -> Integer {
            self.values
                .as_ref()
                .and_then(|vs| {
                    user_name
                        .as_ref()
                        .and_then(|n| vs.get(n))
                        .or_else(|| vs.get(&raw_name))
                })
                .cloned()
                .unwrap_or_else(|| Integer::from(0))
        };
        match ty {
            Ty::Bool => T::Bool(ctx.cs.borrow_mut().new_var(
                &raw_name,
                Sort::Bool,
                || Value::Bool(get_int_val() != 0),
                visibility,
            )),
            Ty::Field => T::Field(ctx.cs.borrow_mut().new_var(
                &raw_name,
                Sort::Field(self.modulus.clone()),
                || Value::Field(FieldElem::new(get_int_val(), self.modulus.clone())),
                visibility,
            )),
            Ty::Uint(w) => T::Uint(
                *w,
                ctx.cs.borrow_mut().new_var(
                    &raw_name,
                    Sort::BitVector(*w),
                    || Value::BitVector(BitVector::new(get_int_val(), *w)),
                    visibility,
                ),
            ),
            Ty::Array(n, ty) => T::Array(
                (**ty).clone(),
                (0..*n)
                    .map(|i| {
                        self.declare(
                            ctx,
                            &*ty,
                            idx_name(&raw_name, i),
                            user_name.as_ref().map(|u| idx_name(u, i)),
                            visibility.clone(),
                        )
                    })
                    .collect(),
            ),
            Ty::Struct(n, fs) => T::Struct(
                n.clone(),
                fs.iter()
                    .map(|(f_name, f_ty)| {
                        (
                            f_name.clone(),
                            self.declare(
                                ctx,
                                f_ty,
                                field_name(&raw_name, f_name),
                                user_name.as_ref().map(|u| field_name(u, f_name)),
                                visibility.clone(),
                            ),
                        )
                    })
                    .collect(),
            ),
        }
    }
    fn ite(&self, ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        match (t, f) {
            (T::Bool(a), T::Bool(b)) => T::Bool(term![Op::Ite; cond, a, b]),
            (T::Uint(wa, a), T::Uint(wb, b)) if wa == wb => T::Uint(wa, term![Op::Ite; cond, a, b]),
            (T::Field(a), T::Field(b)) => T::Field(term![Op::Ite; cond, a, b]),
            (T::Array(a_ty, a), T::Array(b_ty, b)) if a_ty == b_ty => T::Array(
                a_ty,
                a.into_iter()
                    .zip(b.into_iter())
                    .map(|(a_i, b_i)| self.ite(ctx, cond.clone(), a_i, b_i))
                    .collect(),
            ),
            (T::Struct(a_nm, a), T::Struct(b_nm, b)) if a_nm == b_nm => T::Struct(
                a_nm,
                a.into_iter()
                    .zip(b.into_iter())
                    .map(|((a_f, a_i), (b_f, b_i))| {
                        if a_f == b_f {
                            (a_f, self.ite(ctx, cond.clone(), a_i, b_i))
                        } else {
                            panic!("Field mismatch: '{}' vs '{}'", a_f, b_f)
                        }
                    })
                    .collect(),
            ),
            (t, f) => panic!("Cannot ITE {} and {}", t, f),
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
        assert!(&t.type_() == ty);
        match (ty, t) {
            (_, T::Bool(b)) => T::Bool(ctx.cs.borrow_mut().assign(&name, b, visibility)),
            (_, T::Field(b)) => T::Field(ctx.cs.borrow_mut().assign(&name, b, visibility)),
            (_, T::Uint(w, b)) => T::Uint(w, ctx.cs.borrow_mut().assign(&name, b, visibility)),
            (_, T::Array(ety, list)) => T::Array(
                ety.clone(),
                list.into_iter()
                    .enumerate()
                    .map(|(i, elem)| {
                        self.assign(ctx, &ety, idx_name(&name, i), elem, visibility.clone())
                    })
                    .collect(),
            ),
            (Ty::Struct(_, tys), T::Struct(s_name, list)) => T::Struct(
                s_name,
                list.into_iter()
                    .zip(tys.into_iter())
                    .map(|((f_name, elem), (_, f_ty))| {
                        (
                            f_name.clone(),
                            self.assign(
                                ctx,
                                &f_ty,
                                field_name(&name, &f_name),
                                elem,
                                visibility.clone(),
                            ),
                        )
                    })
                    .collect(),
            ),
            _ => unimplemented!(),
        }
    }
    fn values(&self) -> bool {
        self.values.is_some()
    }

    fn type_of(&self, term: &Self::T) -> Self::Ty {
        term.type_()
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }
}
