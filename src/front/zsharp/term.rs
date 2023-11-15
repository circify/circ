//! Symbolic Z# terms
use std::collections::BTreeMap;
use std::fmt::{self, Display, Formatter};

use rug::Integer;

use crate::cfg::cfg;
use crate::circify::{CirCtx, Embeddable, Typed};
use crate::front::field_list::FieldList;
use crate::ir::opt::cfold::fold as constant_fold;
use crate::ir::term::*;

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
    Uint(usize),
    Bool,
    Field,
    Struct(String, FieldList<Ty>),
    Array(usize, Box<Ty>),
    MutArray(usize),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Uint(w) => write!(f, "u{w}"),
            Ty::Field => write!(f, "field"),
            Ty::Struct(n, fields) => {
                let mut o = f.debug_struct(n);
                for (f_name, f_ty) in fields.fields() {
                    o.field(f_name, f_ty);
                }
                o.finish()
            }
            Ty::Array(n, b) => {
                let mut dims = vec![n];
                let mut bb = b.as_ref();
                while let Ty::Array(n, b) = bb {
                    bb = b.as_ref();
                    dims.push(n);
                }
                write!(f, "{bb}")?;
                dims.iter().try_for_each(|d| write!(f, "[{d}]"))
            }
            Ty::MutArray(n) => write!(f, "MutArray({n})"),
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{self}")
    }
}

pub fn default_field() -> circ_fields::FieldT {
    cfg().field().clone()
}

fn default_field_sort() -> Sort {
    Sort::Field(default_field())
}

impl Ty {
    fn sort(&self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Uint(w) => Sort::BitVector(*w),
            Self::Field => default_field_sort(),
            Self::Array(n, b) => {
                Sort::Array(Box::new(default_field_sort()), Box::new(b.sort()), *n)
            }
            Self::MutArray(n) => Sort::Array(
                Box::new(default_field_sort()),
                Box::new(default_field_sort()),
                *n,
            ),
            Self::Struct(_name, fs) => {
                Sort::Tuple(fs.fields().map(|(_f_name, f_ty)| f_ty.sort()).collect())
            }
        }
    }
    fn default_ir_term(&self) -> Term {
        self.sort().default_term()
    }
    pub fn default(&self) -> T {
        T {
            ty: self.clone(),
            term: self.default_ir_term(),
        }
    }
    /// Creates a new structure type, sorting the keys.
    pub fn new_struct<I: IntoIterator<Item = (String, Ty)>>(name: String, fields: I) -> Self {
        Self::Struct(name, FieldList::new(fields.into_iter().collect()))
    }
    /// Array value type
    pub fn array_val_ty(&self) -> &Self {
        match self {
            Self::Array(_, b) => b,
            // TODO: MutArray?
            _ => panic!("Not an array type: {:?}", self),
        }
    }
    /// Is this an array?
    pub fn is_array(&self) -> bool {
        matches!(self, Self::Array(_, _) | Self::MutArray(_))
    }
}

#[derive(Clone, Debug)]
pub struct T {
    pub ty: Ty,
    pub term: Term,
}

impl T {
    pub fn new(ty: Ty, term: Term) -> Self {
        Self { ty, term }
    }
    pub fn type_(&self) -> &Ty {
        &self.ty
    }
    /// Get all IR terms inside this value, as a list.
    pub fn terms(&self) -> Vec<Term> {
        let mut output: Vec<Term> = Vec::new();
        fn terms_tail(term: &Term, output: &mut Vec<Term>) {
            match check(term) {
                Sort::Bool | Sort::BitVector(_) | Sort::Field(_) => output.push(term.clone()),
                Sort::Array(_k, _v, size) => {
                    for i in 0..size {
                        terms_tail(&term![Op::Select; term.clone(), pf_lit_ir(i)], output)
                    }
                }
                Sort::Tuple(sorts) => {
                    for i in 0..sorts.len() {
                        terms_tail(&term![Op::Field(i); term.clone()], output)
                    }
                }
                s => unreachable!("Unreachable IR sort {} in ZoK", s),
            }
        }
        terms_tail(&self.term, &mut output);
        output
    }
    fn unwrap_array_ir(self) -> Result<Vec<Term>, String> {
        match &self.ty {
            Ty::Array(size, _sort) => Ok((0..*size)
                .map(|i| term![Op::Select; self.term.clone(), pf_lit_ir(i)])
                .collect()),
            Ty::MutArray(size) => Ok((0..*size)
                .map(|i| term![Op::Select; self.term.clone(), pf_lit_ir(i)])
                .collect()),
            s => Err(format!("Not an array: {s}")),
        }
    }
    pub fn unwrap_array(self) -> Result<Vec<T>, String> {
        match &self.ty {
            Ty::Array(_size, sort) => {
                let sort = (**sort).clone();
                Ok(self
                    .unwrap_array_ir()?
                    .into_iter()
                    .map(|t| T::new(sort.clone(), t))
                    .collect())
            }
            Ty::MutArray(_size) => Ok(self
                .unwrap_array_ir()?
                .into_iter()
                .map(|t| T::new(Ty::Field, t))
                .collect()),
            s => Err(format!("Not an array: {s}")),
        }
    }
    pub fn new_array(v: Vec<T>) -> Result<T, String> {
        array(v)
    }

    pub fn new_struct(name: String, fields: Vec<(String, T)>) -> T {
        let (field_tys, ir_terms): (Vec<_>, Vec<_>) = fields
            .into_iter()
            .map(|(name, t)| ((name.clone(), t.ty), (name, t.term)))
            .unzip();
        let field_ty_list = FieldList::new(field_tys);
        let ir_term = term(Op::Tuple, {
            let with_indices: BTreeMap<usize, Term> = ir_terms
                .into_iter()
                .map(|(name, t)| (field_ty_list.search(&name).unwrap().0, t))
                .collect();
            with_indices.into_values().collect()
        });
        T::new(Ty::Struct(name, field_ty_list), ir_term)
    }

    // XXX(rsw) hrm is there a nicer way to do this?
    pub fn new_field<I>(v: I) -> Self
    where
        Integer: From<I>,
    {
        T::new(Ty::Field, pf_lit_ir(v))
    }

    pub fn new_u8<I>(v: I) -> Self
    where
        Integer: From<I>,
    {
        T::new(Ty::Uint(8), bv_lit(v, 8))
    }

    pub fn new_u16<I>(v: I) -> Self
    where
        Integer: From<I>,
    {
        T::new(Ty::Uint(16), bv_lit(v, 16))
    }

    pub fn new_u32<I>(v: I) -> Self
    where
        Integer: From<I>,
    {
        T::new(Ty::Uint(32), bv_lit(v, 32))
    }

    pub fn new_u64<I>(v: I) -> Self
    where
        Integer: From<I>,
    {
        T::new(Ty::Uint(64), bv_lit(v, 64))
    }

    pub fn pretty<W: std::io::Write>(&self, f: &mut W) -> Result<(), std::io::Error> {
        use std::io::{Error, ErrorKind};
        let val = match &self.term.op() {
            Op::Const(v) => Ok(v),
            _ => Err(Error::new(ErrorKind::Other, "not a const val")),
        }?;
        match val {
            Value::Bool(b) => write!(f, "{b}"),
            Value::Field(fe) => write!(f, "{}f", fe.i()),
            Value::BitVector(bv) => match bv.width() {
                8 => write!(f, "0x{:02x}", bv.uint()),
                16 => write!(f, "0x{:04x}", bv.uint()),
                32 => write!(f, "0x{:08x}", bv.uint()),
                64 => write!(f, "0x{:016x}", bv.uint()),
                _ => unreachable!(),
            },
            Value::Tuple(vs) => {
                let (n, fl) = if let Ty::Struct(n, fl) = &self.ty {
                    Ok((n, fl))
                } else {
                    Err(Error::new(
                        ErrorKind::Other,
                        "expected struct, got something else",
                    ))
                }?;
                write!(f, "{n} {{ ")?;
                fl.fields().zip(vs.iter()).try_for_each(|((n, ty), v)| {
                    write!(f, "{n}: ")?;
                    T::new(ty.clone(), leaf_term(Op::Const(v.clone()))).pretty(f)?;
                    write!(f, ", ")
                })?;
                write!(f, "}}")
            }
            Value::Array(arr) => {
                let inner_ty = if let Ty::Array(_, ty) = &self.ty {
                    Ok(ty)
                } else {
                    Err(Error::new(
                        ErrorKind::Other,
                        "expected array, got something else",
                    ))
                }?;
                write!(f, "[")?;
                arr.key_sort
                    .elems_iter()
                    .take(arr.size)
                    .try_for_each(|idx| {
                        T::new(
                            *inner_ty.clone(),
                            leaf_term(Op::Const(arr.select(idx.as_value_opt().unwrap()))),
                        )
                        .pretty(f)?;
                        write!(f, ", ")
                    })?;
                write!(f, "]")
            }
            _ => unreachable!(),
        }
    }
}

impl Display for T {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.term)
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
    match (&a.ty, &b.ty, fu, ff, fb) {
        (Ty::Uint(na), Ty::Uint(nb), Some(fu), _, _) if na == nb => {
            Ok(T::new(Ty::Uint(*na), fu(a.term.clone(), b.term.clone())))
        }
        (Ty::Bool, Ty::Bool, _, _, Some(fb)) => {
            Ok(T::new(Ty::Bool, fb(a.term.clone(), b.term.clone())))
        }
        (Ty::Field, Ty::Field, _, Some(ff), _) => {
            Ok(T::new(Ty::Field, ff(a.term.clone(), b.term.clone())))
        }
        (x, y, _, _, _) => Err(format!("Cannot perform op '{name}' on {x} and {y}")),
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
    match (&a.ty, &b.ty, fu, ff, fb) {
        (Ty::Uint(na), Ty::Uint(nb), Some(fu), _, _) if na == nb => {
            Ok(T::new(Ty::Bool, fu(a.term.clone(), b.term.clone())))
        }
        (Ty::Bool, Ty::Bool, _, _, Some(fb)) => {
            Ok(T::new(Ty::Bool, fb(a.term.clone(), b.term.clone())))
        }
        (Ty::Field, Ty::Field, _, Some(ff), _) => {
            Ok(T::new(Ty::Bool, ff(a.term.clone(), b.term.clone())))
        }
        (x, y, _, _, _) => Err(format!("Cannot perform op '{name}' on {x} and {y}")),
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

fn rem_field(a: Term, b: Term) -> Term {
    let len = cfg().field().modulus().significant_bits() as usize;
    let a_bv = term![Op::PfToBv(len); a];
    let b_bv = term![Op::PfToBv(len); b];
    term![Op::UbvToPf(default_field()); term![Op::BvBinOp(BvBinOp::Urem); a_bv, b_bv]]
}

fn rem_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Urem); a, b]
}

pub fn rem(a: T, b: T) -> Result<T, String> {
    wrap_bin_op("%", Some(rem_uint), Some(rem_field), None, a, b)
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

fn eq_base(a: T, b: T) -> Result<Term, String> {
    if a.ty != b.ty {
        Err(format!(
            "Cannot '==' dissimilar types {} and {}",
            a.type_(),
            b.type_()
        ))
    } else {
        Ok(term![Op::Eq; a.term, b.term])
    }
}

pub fn eq(a: T, b: T) -> Result<T, String> {
    Ok(T::new(Ty::Bool, eq_base(a, b)?))
}

pub fn neq(a: T, b: T) -> Result<T, String> {
    Ok(T::new(Ty::Bool, not_bool(eq_base(a, b)?)))
}

fn ult_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ult); a, b]
}

// XXX(constr_opt) see TODO file - only need to expand to MIN of two bit-lengths if done right
// XXX(constr_opt) do this using subtraction instead?
fn field_comp(a: Term, b: Term, op: BvBinPred) -> Term {
    let len = cfg().field().modulus().significant_bits() as usize;
    let a_bv = term![Op::PfToBv(len); a];
    let b_bv = term![Op::PfToBv(len); b];
    term![Op::BvBinPred(op); a_bv, b_bv]
}

fn ult_field(a: Term, b: Term) -> Term {
    field_comp(a, b, BvBinPred::Ult)
}

pub fn ult(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<", Some(ult_uint), Some(ult_field), None, a, b)
}

fn ule_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ule); a, b]
}

fn ule_field(a: Term, b: Term) -> Term {
    field_comp(a, b, BvBinPred::Ule)
}

pub fn ule(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred("<=", Some(ule_uint), Some(ule_field), None, a, b)
}

fn ugt_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ugt); a, b]
}

fn ugt_field(a: Term, b: Term) -> Term {
    field_comp(a, b, BvBinPred::Ugt)
}

pub fn ugt(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred(">", Some(ugt_uint), Some(ugt_field), None, a, b)
}

fn uge_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Uge); a, b]
}

fn uge_field(a: Term, b: Term) -> Term {
    field_comp(a, b, BvBinPred::Uge)
}

pub fn uge(a: T, b: T) -> Result<T, String> {
    wrap_bin_pred(">=", Some(uge_uint), Some(uge_field), None, a, b)
}

pub fn pow(a: T, b: T) -> Result<T, String> {
    if a.ty != Ty::Field || b.ty != Ty::Uint(32) {
        return Err(format!("Cannot compute {a} ** {b} : must be Field ** U32"));
    }

    let a = a.term;
    let b = const_int(b)?;
    if b == 0 {
        return Ok(field_lit(1));
    }

    let res = (0..b.significant_bits() - 1)
        .rev()
        .fold(a.clone(), |acc, ix| {
            let acc = mul_field(acc.clone(), acc);
            if b.get_bit(ix) {
                mul_field(acc, a.clone())
            } else {
                acc
            }
        });
    Ok(T::new(Ty::Field, res))
}

fn wrap_un_op(
    name: &str,
    fu: Option<fn(Term) -> Term>,
    ff: Option<fn(Term) -> Term>,
    fb: Option<fn(Term) -> Term>,
    a: T,
) -> Result<T, String> {
    match (&a.ty, fu, ff, fb) {
        (Ty::Uint(_), Some(fu), _, _) => Ok(T::new(a.ty.clone(), fu(a.term.clone()))),
        (Ty::Bool, _, _, Some(fb)) => Ok(T::new(Ty::Bool, fb(a.term.clone()))),
        (Ty::Field, _, Some(ff), _) => Ok(T::new(Ty::Field, ff(a.term.clone()))),
        (x, _, _, _) => Err(format!("Cannot perform op '{name}' on {x}")),
    }
}

fn neg_field(a: Term) -> Term {
    term![Op::PfUnOp(PfUnOp::Neg); a]
}

fn neg_uint(a: Term) -> Term {
    term![Op::BvUnOp(BvUnOp::Neg); a]
}

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
    match const_value(&a.term) {
        Some(Value::Field(f)) => Ok(f.i()),
        Some(Value::BitVector(f)) => Ok(f.uint().clone()),
        _ => Err(format!("{a} is not a constant integer")),
    }
}

pub fn const_bool(a: T) -> Option<bool> {
    match const_value(&a.term) {
        Some(Value::Bool(b)) => Some(b),
        _ => None,
    }
}

pub fn const_val(a: T) -> Result<T, String> {
    match const_value(&a.term) {
        Some(v) => Ok(T::new(a.ty, leaf_term(Op::Const(v)))),
        _ => Err(format!("{} is not a constant value", &a)),
    }
}

fn const_value(t: &Term) -> Option<Value> {
    let folded = constant_fold(t, &[]);
    match &folded.op() {
        Op::Const(v) => Some(v.clone()),
        _ => None,
    }
}

pub fn bool(a: T) -> Result<Term, String> {
    match &a.ty {
        Ty::Bool => Ok(a.term),
        a => Err(format!("{a} is not a boolean")),
    }
}

fn wrap_shift(name: &str, op: BvBinOp, a: T, b: T) -> Result<T, String> {
    let bc = const_int(b)?;
    match &a.ty {
        &Ty::Uint(na) => Ok(T::new(a.ty, term![Op::BvBinOp(op); a.term, bv_lit(bc, na)])),
        x => Err(format!("Cannot perform op '{name}' on {x} and {bc}")),
    }
}

pub fn shl(a: T, b: T) -> Result<T, String> {
    wrap_shift("<<", BvBinOp::Shl, a, b)
}

pub fn shr(a: T, b: T) -> Result<T, String> {
    wrap_shift(">>", BvBinOp::Lshr, a, b)
}

fn ite(c: Term, a: T, b: T) -> Result<T, String> {
    if a.ty != b.ty {
        Err(format!("Cannot perform ITE on {a} and {b}"))
    } else {
        Ok(T::new(a.ty.clone(), term![Op::Ite; c, a.term, b.term]))
    }
}

pub fn cond(c: T, a: T, b: T) -> Result<T, String> {
    ite(bool(c)?, a, b)
}

pub fn pf_lit_ir<I>(i: I) -> Term
where
    Integer: From<I>,
{
    leaf_term(Op::Const(pf_val(i)))
}

fn pf_val<I>(i: I) -> Value
where
    Integer: From<I>,
{
    Value::Field(cfg().field().new_v(i))
}

pub fn field_lit<I>(i: I) -> T
where
    Integer: From<I>,
{
    T::new(Ty::Field, pf_lit_ir(i))
}

pub fn z_bool_lit(v: bool) -> T {
    T::new(Ty::Bool, leaf_term(Op::Const(Value::Bool(v))))
}

pub fn uint_lit<I>(v: I, bits: usize) -> T
where
    Integer: From<I>,
{
    T::new(Ty::Uint(bits), bv_lit(v, bits))
}

pub fn slice(arr: T, start: Option<usize>, end: Option<usize>) -> Result<T, String> {
    match &arr.ty {
        Ty::Array(size, _) => {
            let start = start.unwrap_or(0);
            let end = end.unwrap_or(*size);
            array(arr.unwrap_array()?.drain(start..end))
        }
        Ty::MutArray(size) => {
            let start = start.unwrap_or(0);
            let end = end.unwrap_or(*size);
            array(arr.unwrap_array()?.drain(start..end))
        }
        a => Err(format!("Cannot slice {a}")),
    }
}

pub fn field_select(struct_: &T, field: &str) -> Result<T, String> {
    match &struct_.ty {
        Ty::Struct(_, map) => {
            if let Some((idx, ty)) = map.search(field) {
                Ok(T::new(
                    ty.clone(),
                    term![Op::Field(idx); struct_.term.clone()],
                ))
            } else {
                Err(format!("No field '{field}'"))
            }
        }
        a => Err(format!("{a} is not a struct")),
    }
}

pub fn field_store(struct_: T, field: &str, val: T) -> Result<T, String> {
    match &struct_.ty {
        Ty::Struct(_, map) => {
            if let Some((idx, ty)) = map.search(field) {
                if ty == &val.ty {
                    Ok(T::new(
                        struct_.ty.clone(),
                        term![Op::Update(idx); struct_.term.clone(), val.term],
                    ))
                } else {
                    Err(format!(
                        "term {val} assigned to field {field} of type {}",
                        map.get(idx).1
                    ))
                }
            } else {
                Err(format!("No field '{field}'"))
            }
        }
        a => Err(format!("{a} is not a struct")),
    }
}

fn coerce_to_field(i: T) -> Result<Term, String> {
    match &i.ty {
        Ty::Uint(_) => Ok(term![Op::UbvToPf(default_field()); i.term]),
        Ty::Field => Ok(i.term),
        _ => Err(format!("Cannot coerce {} to a field element", &i)),
    }
}

pub fn array_select(array: T, idx: T) -> Result<T, String> {
    match array.ty {
        Ty::Array(_, elem_ty) if matches!(idx.ty, Ty::Uint(_) | Ty::Field) => {
            let iterm = coerce_to_field(idx).unwrap();
            Ok(T::new(*elem_ty, term![Op::Select; array.term, iterm]))
        }
        Ty::MutArray(_) if matches!(idx.ty, Ty::Uint(_) | Ty::Field) => {
            let iterm = coerce_to_field(idx).unwrap();
            Ok(T::new(Ty::Field, term![Op::Select; array.term, iterm]))
        }
        _ => Err(format!("Cannot index {} using {}", &array.ty, &idx.ty)),
    }
}

pub fn mut_array_store(array: T, idx: T, val: T, cond: Term) -> Result<T, String> {
    if !matches!(array.ty, Ty::MutArray(_) | Ty::Array(..)) {
        return Err(format!(
            "Can only call mut_array_store on arrays, not {array}"
        ));
    }
    let i = coerce_to_field(idx).map_err(|s| format!("{s}: mutable array index"))?;
    let v = coerce_to_field(val).map_err(|s| format!("{s}: mutable array value"))?;
    Ok(T::new(array.ty, term![Op::CStore; array.term, i, v, cond]))
}

pub fn array_store(array: T, idx: T, val: T) -> Result<T, String> {
    if matches!(&array.ty, Ty::Array(_, _)) && matches!(&idx.ty, Ty::Uint(_) | Ty::Field) {
        // XXX(q) typecheck here?
        let iterm = if matches!(idx.ty, Ty::Uint(_)) {
            term![Op::UbvToPf(default_field()); idx.term]
        } else {
            idx.term
        };
        Ok(T::new(
            array.ty,
            term![Op::Store; array.term, iterm, val.term],
        ))
    } else {
        Err(format!("Cannot index {} using {}", &array.ty, &idx.ty))
    }
}

fn ir_array<I: IntoIterator<Item = Term>>(value_sort: Sort, elems: I) -> Term {
    let key_sort = Sort::Field(cfg().field().clone());
    term(Op::Array(key_sort, value_sort), elems.into_iter().collect())
}

pub fn fill_array(value: T, size: usize) -> Result<T, String> {
    Ok(T::new(
        Ty::Array(size, Box::new(value.ty)),
        term![Op::Fill(default_field_sort(), size); value.term],
    ))
}
pub fn array<I: IntoIterator<Item = T>>(elems: I) -> Result<T, String> {
    let v: Vec<T> = elems.into_iter().collect();
    if let Some(e) = v.first() {
        let ty = e.type_();
        if v.iter().skip(1).any(|a| a.type_() != ty) {
            Err("Inconsistent types in array".to_string())
        } else {
            let sort = check(&e.term);
            Ok(T::new(
                Ty::Array(v.len(), Box::new(ty.clone())),
                ir_array(sort, v.into_iter().map(|t| t.term)),
            ))
        }
    } else {
        Err("Empty array".to_string())
    }
}

pub fn uint_to_field(u: T) -> Result<T, String> {
    match &u.ty {
        Ty::Uint(_) => Ok(T::new(
            Ty::Field,
            term![Op::UbvToPf(default_field()); u.term],
        )),
        u => Err(format!("Cannot do uint-to-field on {u}")),
    }
}

pub fn uint_to_uint(u: T, w: usize) -> Result<T, String> {
    match &u.ty {
        Ty::Uint(n) if *n <= w => Ok(T::new(Ty::Uint(w), term![Op::BvUext(w - n); u.term])),
        Ty::Uint(n) => Err(format!("Tried narrowing uint{n}-to-uint{w} attempted")),
        u => Err(format!("Cannot do uint-to-uint on {u}")),
    }
}

pub fn uint_to_bits(u: T) -> Result<T, String> {
    match &u.ty {
        Ty::Uint(n) => Ok(T::new(
            Ty::Array(*n, Box::new(Ty::Bool)),
            ir_array(
                Sort::Bool,
                (0..*n).rev().map(|i| term![Op::BvBit(i); u.term.clone()]),
            ),
        )),
        u => Err(format!("Cannot do uint-to-bits on {u}")),
    }
}

// XXX(rsw) is it correct to enforce length here, vs. in (say) builtin_call in mod.rs?
pub fn uint_from_bits(u: T) -> Result<T, String> {
    match &u.ty {
        Ty::Array(bits, elem_ty) if **elem_ty == Ty::Bool => match bits {
            8 | 16 | 32 | 64 => Ok(T::new(
                Ty::Uint(*bits),
                term(
                    Op::BvConcat,
                    u.unwrap_array_ir()?
                        .into_iter()
                        .map(|z: Term| -> Term { term![Op::BoolToBv; z] })
                        .collect(),
                ),
            )),
            l => Err(format!("Cannot do uint-from-bits on len {l} array")),
        },
        u => Err(format!("Cannot do uint-from-bits on {u}")),
    }
}

pub fn field_to_bits(f: T, n: usize) -> Result<T, String> {
    match &f.ty {
        Ty::Field => uint_to_bits(T::new(Ty::Uint(n), term![Op::PfToBv(n); f.term])),
        u => Err(format!("Cannot do uint-to-bits on {u}")),
    }
}

fn bv_from_bits(barr: Term, size: usize) -> Term {
    term(
        Op::BvConcat,
        (0..size)
            .map(|i| term![Op::BoolToBv; term![Op::Select; barr.clone(), pf_lit_ir(i)]])
            .collect(),
    )
}

pub fn bit_array_le(a: T, b: T, n: usize) -> Result<T, String> {
    match (&a.ty, &b.ty) {
        (Ty::Array(la, ta), Ty::Array(lb, tb)) => {
            if **ta != Ty::Bool || **tb != Ty::Bool {
                Err("bit-array-le must be called on arrays of Bools".to_string())
            } else if la != lb {
                Err(format!(
                    "bit-array-le called on arrays with lengths {la} != {lb}"
                ))
            } else if *la != n {
                Err(format!(
                    "bit-array-le::<{n}> called on arrays with length {la}"
                ))
            } else {
                Ok(())
            }
        }
        _ => Err(format!("Cannot do bit-array-le on ({}, {})", &a.ty, &b.ty)),
    }?;

    let at = bv_from_bits(a.term, n);
    let bt = bv_from_bits(b.term, n);
    Ok(T::new(
        Ty::Bool,
        term![Op::BvBinPred(BvBinPred::Ule); at, bt],
    ))
}

pub fn sample_challenge(a: T, number: usize) -> Result<T, String> {
    if let Ty::Array(_, ta) = &a.ty {
        if let Ty::Field = &**ta {
            Ok(T::new(
                Ty::Field,
                term(
                    Op::PfChallenge(format!("zx_chall_{number}"), default_field()),
                    a.unwrap_array_ir()?,
                ),
            ))
        } else {
            Err(format!("sample_challenge called on non-field array {a}"))
        }
    } else {
        Err(format!("sample_challenge called on non-array {a}"))
    }
}

pub struct ZSharp {}

fn field_name(struct_name: &str, field_name: &str) -> String {
    format!("{struct_name}.{field_name}")
}

fn idx_name(struct_name: &str, idx: usize) -> String {
    format!("{struct_name}.{idx}")
}

impl ZSharp {
    pub fn new() -> Self {
        Self {}
    }
}

impl Typed<Ty> for T {
    fn type_(&self) -> Ty {
        self.ty.clone()
    }
}

impl Embeddable for ZSharp {
    type T = T;
    type Ty = Ty;
    fn declare_input(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        name: String,
        visibility: Option<PartyId>,
        precompute: Option<T>,
    ) -> Self::T {
        match ty {
            Ty::Bool => T::new(
                Ty::Bool,
                ctx.cs.borrow_mut().new_var(
                    &name,
                    Sort::Bool,
                    visibility,
                    precompute.map(|p| p.term),
                ),
            ),
            Ty::Field => T::new(
                Ty::Field,
                ctx.cs.borrow_mut().new_var(
                    &name,
                    default_field_sort(),
                    visibility,
                    precompute.map(|p| p.term),
                ),
            ),
            Ty::Uint(w) => T::new(
                Ty::Uint(*w),
                ctx.cs.borrow_mut().new_var(
                    &name,
                    Sort::BitVector(*w),
                    visibility,
                    precompute.map(|p| p.term),
                ),
            ),
            Ty::Array(n, ty) => {
                let ps: Vec<Option<T>> = match precompute.map(|p| p.unwrap_array()) {
                    Some(Ok(v)) => v.into_iter().map(Some).collect(),
                    Some(Err(e)) => panic!("{}", e),
                    None => std::iter::repeat(None).take(*n).collect(),
                };
                debug_assert_eq!(*n, ps.len());
                array(
                    ps.into_iter().enumerate().map(|(i, p)| {
                        self.declare_input(ctx, ty, idx_name(&name, i), visibility, p)
                    }),
                )
                .unwrap()
            }
            Ty::MutArray(n) => {
                let ps: Vec<Option<T>> = match precompute.map(|p| p.unwrap_array()) {
                    Some(Ok(v)) => v.into_iter().map(Some).collect(),
                    Some(Err(e)) => panic!("{}", e),
                    None => std::iter::repeat(None).take(*n).collect(),
                };
                debug_assert_eq!(*n, ps.len());
                array(
                    ps.into_iter().enumerate().map(|(i, p)| {
                        self.declare_input(ctx, &Ty::Field, idx_name(&name, i), visibility, p)
                    }),
                )
                .unwrap()
            }
            Ty::Struct(n, fs) => T::new_struct(
                n.clone(),
                fs.fields()
                    .map(|(f_name, f_ty)| {
                        (
                            f_name.clone(),
                            self.declare_input(
                                ctx,
                                f_ty,
                                field_name(&name, f_name),
                                visibility,
                                precompute.as_ref().map(|_| unimplemented!("precomputations for declared inputs that are Z# structures")),
                            ),
                        )
                    })
                    .collect(),
            ),
        }
    }
    fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        ite(cond, t, f).unwrap()
    }
    fn create_uninit(&self, _ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T {
        ty.default()
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }

    fn wrap_persistent_array(&self, t: Term) -> Self::T {
        let size = check(&t).as_array().2;
        T::new(Ty::MutArray(size), t)
    }
}
