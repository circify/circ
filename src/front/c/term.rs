//! C Terms
use crate::circify::mem::AllocId;
use crate::circify::{CirCtx, Embeddable, Typed};
use crate::front::c::types::*;
use crate::front::c::Circify;
use crate::ir::term::*;
use rug::Integer;
use std::fmt::{self, Display, Formatter};

#[allow(clippy::enum_variant_names)]
#[derive(Clone)]
pub enum CTermData {
    CBool(Term),
    CInt(bool, usize, Term),
    CArray(Ty, Option<AllocId>),
}

impl CTermData {
    pub fn type_(&self) -> Ty {
        match self {
            Self::CBool(_) => Ty::Bool,
            Self::CInt(s, w, _) => Ty::Int(*s, *w),
            Self::CArray(b, _) => Ty::Array(None, Box::new(b.clone())),
        }
    }
    /// Get all IR terms inside this value, as a list.
    pub fn terms(&self) -> Vec<Term> {
        let mut output: Vec<Term> = Vec::new();
        fn terms_tail(term: &CTermData, output: &mut Vec<Term>) {
            match term {
                CTermData::CBool(b) => output.push(b.clone()),
                CTermData::CInt(_, _, b) => output.push(b.clone()),
                _ => unimplemented!("Term: {} not implemented yet", term),
            }
        }
        terms_tail(self, &mut output);
        output
    }
    pub fn simple_term(&self) -> Term {
        match self {
            CTermData::CBool(b) => b.clone(),
            CTermData::CInt(_, _, b) => b.clone(),
            _ => panic!(),
        }
    }
    pub fn term(&self, circ: &Circify<Ct>) -> Term {
        match self {
            CTermData::CBool(b) => b.clone(),
            CTermData::CInt(_, _, b) => b.clone(),
            CTermData::CArray(_, b) => {
                // TODO: load all of the array
                let i = b.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", self));
                circ.load(i, bv_lit(0, 32))
            }
        }
    }
}

impl Display for CTermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CTermData::CBool(x) => write!(f, "Bool({})", x),
            CTermData::CInt(_, _, x) => write!(f, "Int({})", x),
            CTermData::CArray(_, v) => write!(f, "Array({:#?})", v),
        }
    }
}

impl fmt::Debug for CTermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, Debug)]
pub struct CTerm {
    pub term: CTermData,
    pub udef: bool,
}

impl Display for CTerm {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Term: {:#?},\nudef: {}", self.term, self.udef)
    }
}

pub fn cterm(data: CTermData) -> CTerm {
    CTerm {
        term: data,
        udef: false,
    }
}

pub fn cast(to_ty: Option<Ty>, t: CTerm) -> CTerm {
    let ty = t.term.type_();
    match t.term {
        CTermData::CBool(ref term) => match to_ty {
            Some(Ty::Int(s, w)) => CTerm {
                term: CTermData::CInt(
                    s,
                    w,
                    term![Op::Not; term![Op::Eq; bv_lit(0, w), term.clone()]],
                ),
                udef: t.udef,
            },
            Some(Ty::Bool) => t.clone(),
            _ => panic!("Bad cast from {} to {:?}", ty, to_ty),
        },
        CTermData::CInt(_, w, ref term) => match to_ty {
            Some(Ty::Bool) => CTerm {
                term: CTermData::CBool(term![Op::Not; term![Op::Eq; bv_lit(0, w), term.clone()]]),
                udef: t.udef,
            },
            Some(Ty::Int(_, _)) => t.clone(),
            _ => panic!("Bad cast from {} to {:?}", ty, to_ty),
        },
        CTermData::CArray(_, ref ty) => match to_ty {
            Some(Ty::Array(_, _)) => t.clone(),
            _ => panic!("Bad cast from {:#?} to {:?}", ty, to_ty),
        },
    }
}

/// Implementation of integer promotion (C11, 6.3.1.1.3)
fn int_promotion(t: &CTerm) -> CTerm {
    let ty = t.term.type_();
    if (ty.is_integer_type() || Ty::Bool == ty) && ty.int_conversion_rank() < 32 {
        match &t.term {
            // "If an int can represent all values ... converted to an int ...
            // otherwise an unsigned int"
            CTermData::CInt(s, w, v) => {
                let width = w - if *s { 1 } else { 0 };
                let max_val: u32 = u32::pow(2, width as u32) - 1;
                let signed = max_val < u32::pow(2u32, 31u32) - 1;
                CTerm {
                    term: CTermData::CInt(signed, 32, v.clone()),
                    udef: t.udef,
                }
            }
            CTermData::CBool(v) => CTerm {
                term: CTermData::CInt(false, 32, v.clone()),
                udef: t.udef,
            },
            _ => t.clone(),
        }
    } else {
        t.clone()
    }
}

fn inner_usual_arith_conversions(a: &CTerm, b: &CTerm) -> (CTerm, CTerm) {
    let _a_ty = a.term.type_();
    let _b_ty = b.term.type_();
    let a_prom = int_promotion(a);
    let b_prom = int_promotion(b);
    let a_prom_ty = a_prom.term.type_();
    let b_prom_ty = b_prom.term.type_();

    if a_prom_ty == b_prom_ty {
        (a_prom, b_prom)
    } else if a_prom_ty.is_signed_int() == b_prom_ty.is_signed_int() {
        if a_prom_ty.int_conversion_rank() < b_prom_ty.int_conversion_rank() {
            (cast(Some(b_prom_ty), a_prom), b_prom)
        } else {
            (a_prom, cast(Some(a_prom_ty), b_prom))
        }
    } else {
        unimplemented!("Not implemented case in iUAC");
    }
}

fn usual_arith_conversions(a: CTerm, b: CTerm) -> (CTerm, CTerm) {
    if a.term.type_().is_arith_type() && b.term.type_().is_arith_type() {
        let (a_, b_) = inner_usual_arith_conversions(&a, &b);
        if a_.term.type_() == b_.term.type_() {
            (a_, b_)
        } else {
            panic!(
                "UAC failed: {:#?}, {:#?} to non-equal {:#?}, {:#?}",
                a, b, a_, b_
            );
        }
    } else {
        (a, b)
    }
}

fn wrap_bin_arith(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: CTerm,
    b: CTerm,
) -> Result<CTerm, String> {
    let (a_arith, b_arith) = usual_arith_conversions(a, b);
    match (a_arith.term, b_arith.term, fu, fb) {
        (CTermData::CInt(sx, nx, x), CTermData::CInt(sy, ny, y), Some(fu), _) if nx == ny => {
            Ok(CTerm {
                term: CTermData::CInt(sx && sy, nx, fu(x, y)),
                udef: false,
            })
        }
        (CTermData::CBool(x), CTermData::CBool(y), _, Some(fb)) => Ok(CTerm {
            term: CTermData::CBool(fb(x, y)),
            udef: false,
        }),
        (x, y, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn add_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Add); a, b]
}

pub fn add(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("+", Some(add_uint), None, a, b)
}

fn sub_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Sub); a, b]
}

pub fn sub(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("-", Some(sub_uint), None, a, b)
}

fn mul_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Mul); a, b]
}

pub fn mul(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("*", Some(mul_uint), None, a, b)
}

fn div_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Udiv); a, b]
}

pub fn div(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("/", Some(div_uint), None, a, b)
}

fn rem_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinOp(BvBinOp::Urem); a, b]
}

pub fn rem(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("%", Some(rem_uint), None, a, b)
}

fn bitand_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::And); a, b]
}

pub fn bitand(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("&", Some(bitand_uint), None, a, b)
}

fn bitor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Or); a, b]
}

pub fn bitor(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("|", Some(bitor_uint), None, a, b)
}

fn bitxor_uint(a: Term, b: Term) -> Term {
    term![Op::BvNaryOp(BvNaryOp::Xor); a, b]
}

pub fn bitxor(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_arith("^", Some(bitxor_uint), None, a, b)
}

fn wrap_bin_logical(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: CTerm,
    b: CTerm,
) -> Result<CTerm, String> {
    let a_bool = cast(Some(Ty::Bool), a);
    let b_bool = cast(Some(Ty::Bool), b);
    match (a_bool.term, b_bool.term, fu, fb) {
        (CTermData::CBool(a), CTermData::CBool(b), _, Some(fb)) => Ok(CTerm {
            term: CTermData::CBool(fb(a, b)),
            udef: false,
        }),
        (x, y, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn or_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::Or); a, b]
}

pub fn or(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_logical("||", None, Some(or_bool), a, b)
}

fn and_bool(a: Term, b: Term) -> Term {
    term![Op::BoolNaryOp(BoolNaryOp::And); a, b]
}

pub fn and(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_logical("&&", None, Some(and_bool), a, b)
}

fn wrap_bin_cmp(
    name: &str,
    fu: Option<fn(Term, Term) -> Term>,
    fb: Option<fn(Term, Term) -> Term>,
    a: CTerm,
    b: CTerm,
) -> Result<CTerm, String> {
    let (a_arith, b_arith) = usual_arith_conversions(a, b);
    match (a_arith.term, b_arith.term, fu, fb) {
        (CTermData::CInt(_, nx, x), CTermData::CInt(_, ny, y), Some(fu), _) if nx == ny => {
            Ok(CTerm {
                term: CTermData::CBool(fu(x, y)),
                udef: false,
            })
        }
        (CTermData::CBool(x), CTermData::CBool(y), _, Some(fb)) => Ok(CTerm {
            term: CTermData::CBool(fb(x, y)),
            udef: false,
        }),
        (x, y, _, _) => Err(format!("Cannot perform op '{}' on {} and {}", name, x, y)),
    }
}

fn eq_base(a: Term, b: Term) -> Term {
    term![Op::Eq; a, b]
}

pub fn eq(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp("==", Some(eq_base), Some(eq_base), a, b)
}

fn ult_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ult); a, b]
}

pub fn ult(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp("<", Some(ult_uint), None, a, b)
}

fn ule_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ule); a, b]
}

pub fn ule(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp("<=", Some(ule_uint), None, a, b)
}

fn ugt_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Ugt); a, b]
}

pub fn ugt(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp(">", Some(ugt_uint), None, a, b)
}

fn uge_uint(a: Term, b: Term) -> Term {
    term![Op::BvBinPred(BvBinPred::Uge); a, b]
}

pub fn uge(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp(">=", Some(uge_uint), None, a, b)
}

pub fn const_int(a: CTerm) -> Result<Integer, String> {
    let s = match &a.term {
        CTermData::CInt(s, _, i) => match &i.op {
            Op::Const(Value::BitVector(f)) => {
                if *s {
                    Some(f.as_sint())
                } else {
                    Some(f.uint().clone())
                }
            }
            _ => None,
        },
        _ => None,
    };
    s.ok_or_else(|| format!("{} is not a constant integer", a))
}

fn wrap_shift(name: &str, op: BvBinOp, a: CTerm, b: CTerm) -> Result<CTerm, String> {
    let bc = const_int(b)?;
    match &a.term {
        CTermData::CInt(s, na, a) => Ok(CTerm {
            term: CTermData::CInt(*s, *na, term![Op::BvBinOp(op); a.clone(), bv_lit(bc, *na)]),
            udef: false,
        }),
        x => Err(format!("Cannot perform op '{}' on {} and {}", name, x, bc)),
    }
}

pub fn shl(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_shift("<<", BvBinOp::Shl, a, b)
}

pub fn shr(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_shift(">>", BvBinOp::Lshr, a, b)
}

fn _ite(c: Term, a: CTerm, b: CTerm) -> Result<CTerm, String> {
    match (a.term, b.term) {
        (CTermData::CInt(sa, na, a), CTermData::CInt(sb, nb, b)) if na == nb => Ok(CTerm {
            term: CTermData::CInt(sa && sb, na, term![Op::Ite; c, a, b]),
            udef: false,
        }),
        (CTermData::CBool(a), CTermData::CBool(b)) => Ok(CTerm {
            term: CTermData::CBool(term![Op::Ite; c, a, b]),
            udef: false,
        }),
        (x, y) => Err(format!("Cannot perform ITE on {} and {}", x, y)),
    }
}

// fn array<I: IntoIterator<Item = CTerm>>(elems: I) -> Result<CTerm, String> {
//     let v: Vec<CTerm> = elems.into_iter().collect();
//     if let Some(e) = v.first() {
//         let ty = e.term.type_();
//         if v.iter().skip(1).any(|a| a.term.type_() != ty) {
//             Err(format!("Inconsistent types in array"))
//         } else {
//             Ok(CTerm {
//                 term: CTermData::CArray(ty),
//                 udef: false,
//             })
//         }
//     } else {
//         Err(format!("Empty array"))
//     }
// }

pub struct Ct {}

fn idx_name(struct_name: &str, idx: usize) -> String {
    format!("{}.{}", struct_name, idx)
}

impl Ct {
    pub fn new() -> Self {
        Self {}
    }
}

impl Typed<Ty> for CTerm {
    fn type_(&self) -> Ty {
        self.term.type_()
    }
}

impl Embeddable for Ct {
    type T = CTerm;
    type Ty = Ty;
    fn declare_input(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        name: String,
        visibility: Option<PartyId>,
        precompute: Option<Self::T>,
    ) -> Self::T {
        match ty {
            Ty::Bool => Self::T {
                term: CTermData::CBool(ctx.cs.borrow_mut().new_var(
                    &name,
                    Sort::Bool,
                    visibility,
                    precompute.map(|p| p.term.simple_term()),
                )),
                udef: false,
            },
            Ty::Int(s, w) => Self::T {
                term: CTermData::CInt(
                    *s,
                    *w,
                    ctx.cs.borrow_mut().new_var(
                        &name,
                        Sort::BitVector(*w),
                        visibility,
                        precompute.map(|p| p.term.simple_term()),
                    ),
                ),
                udef: false,
            },
            Ty::Array(n, ty) => {
                assert!(precompute.is_none());
                let v: Vec<Self::T> = (0..n.unwrap())
                    .map(|i| self.declare_input(ctx, &*ty, idx_name(&name, i), visibility, None))
                    .collect();
                let mut mem = ctx.mem.borrow_mut();
                let id = mem.zero_allocate(n.unwrap(), 32, ty.num_bits());
                let arr = Self::T {
                    term: CTermData::CArray(*ty.clone(), Some(id)),
                    udef: false,
                };
                for (i, t) in v.iter().enumerate() {
                    let val = t.term.terms()[0].clone();
                    let t_term = leaf_term(Op::Const(Value::Bool(true)));
                    mem.store(id, bv_lit(i, 32), val, t_term);
                }
                arr
            }
        }
    }
    fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        match (t.term, f.term) {
            (CTermData::CBool(a), CTermData::CBool(b)) => Self::T {
                term: CTermData::CBool(term![Op::Ite; cond, a, b]),
                udef: false,
            },
            (CTermData::CInt(sa, wa, a), CTermData::CInt(sb, wb, b)) if wa == wb => Self::T {
                term: CTermData::CInt(sa && sb, wa, term![Op::Ite; cond, a, b]),
                udef: false,
            },
            // (CTermData::CArray(a_ty, a), CTermData::CArray(b_ty, b)) if a_ty == b_ty => Self::T {
            //     term: CTermData::CArray(
            //         a_ty,
            //         a.into_iter()
            //             .zip(b.into_iter())
            //             .map(|(a_i, b_i)| self.ite(ctx, cond.clone(), a_i, b_i))
            //             .collect(),
            //     ),
            //     udef: false,
            // },
            (t, f) => panic!("Cannot ITE {} and {}", t, f),
        }
    }

    fn create_uninit(&self, ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T {
        match ty {
            Ty::Bool | Ty::Int(..) => ty.default(),
            Ty::Array(n, ty) => {
                let mut mem = ctx.mem.borrow_mut();
                let id = mem.zero_allocate(n.unwrap(), 32, ty.num_bits());
                Self::T {
                    term: CTermData::CArray(*ty.clone(), Some(id)),
                    udef: false,
                }
            }
        }
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }
}
