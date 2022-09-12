//! C Terms
use crate::circify::mem::AllocId;
use crate::circify::{CirCtx, Embeddable, Typed};
use crate::front::c::types::*;
use crate::front::field_list::FieldList;
use crate::ir::term::*;
use rug::Integer;
use std::fmt::{self, Display, Formatter};

#[derive(Clone)]
#[allow(clippy::enum_variant_names)]
pub enum CTermData {
    CBool(Term),
    CInt(bool, usize, Term),
    CArray(Ty, Option<AllocId>),
    CStackPtr(Ty, Term, Option<AllocId>),
    CStruct(Ty, FieldList<CTerm>),
}

impl CTermData {
    pub fn type_(&self) -> Ty {
        match self {
            Self::CBool(_) => Ty::Bool,
            Self::CInt(s, w, _) => Ty::Int(*s, *w),
            Self::CArray(t, _) => t.clone(),
            Self::CStackPtr(t, _o, _) => t.clone(),
            Self::CStruct(ty, _) => ty.clone(),
        }
    }
    /// Get all IR terms inside this value, as a list.
    pub fn terms(&self, ctx: &CirCtx) -> Vec<Term> {
        let mut output: Vec<Term> = Vec::new();
        fn terms_tail(term_: &CTermData, output: &mut Vec<Term>, inner_ctx: &CirCtx) {
            match term_ {
                CTermData::CBool(t) => output.push(t.clone()),
                CTermData::CInt(_, _, t) => output.push(t.clone()),
                CTermData::CArray(t, a) => {
                    let alloc_id = a.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", a));
                    if let Ty::Array(l, _, _) = t {
                        for i in 0..*l {
                            let offset = bv_lit(i, 32);
                            let idx_term = inner_ctx.mem.borrow_mut().load(alloc_id, offset);
                            output.push(idx_term);
                        }
                    }
                }
                CTermData::CStackPtr(t, _o, a) => {
                    let alloc_id = a.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", a));
                    if let Ty::Array(l, _, _) = t {
                        for i in 0..*l {
                            let offset = bv_lit(i, 32);
                            let idx_term = inner_ctx.mem.borrow_mut().load(alloc_id, offset);
                            output.push(idx_term);
                        }
                    } else {
                        panic!("Unsupported type for stack pointer: {:#?}", t);
                    }
                }
                CTermData::CStruct(_, fs) => {
                    for (_name, ct) in fs.fields() {
                        let mut ts = ct.term.terms(inner_ctx);
                        output.append(&mut ts);
                    }
                }
            }
        }
        terms_tail(self, &mut output, ctx);
        output
    }

    pub fn term(&self, ctx: &CirCtx) -> Term {
        let ts = self.terms(ctx);
        assert!(ts.len() == 1);
        ts.get(0).unwrap().clone()
    }

    pub fn simple_term(&self) -> Term {
        match self {
            CTermData::CBool(b) => b.clone(),
            CTermData::CInt(_, _, b) => b.clone(),
            _ => panic!(),
        }
    }

    // pub fn term(&self, circ: &Circify<Ct>) -> Term {
    //     match self {
    //         CTermData::CBool(b) => b.clone(),
    //         CTermData::CInt(_, _, b) => b.clone(),
    //         CTermData::CArray(_, b) => {
    //             // TODO: load all of the array
    //             let i = b.unwrap_or_else(|| panic!("Unknown AllocID: {:#?}", self));
    //             circ.load(i, bv_lit(0, 32))
    //         }
    //     }
    // }
}

impl Display for CTermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CTermData::CBool(x) => write!(f, "Bool({})", x),
            CTermData::CInt(_, _, x) => write!(f, "Int({})", x),
            CTermData::CArray(t, _) => write!(f, "Array({:#?})", t),
            CTermData::CStackPtr(t, s, _) => write!(f, "Ptr{:#?}({:#?})", s, t),
            CTermData::CStruct(t, _) => write!(f, "Struct({})", t),
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

fn field_name(struct_name: &str, field_name: &str) -> String {
    format!("{}.{}", struct_name, field_name)
}

pub fn cterm(data: CTermData) -> CTerm {
    CTerm {
        term: data,
        udef: false,
    }
}

// pub fn int_resize(from_s: bool, from_w: usize, to_s: bool, to_w: usize, t: Term) -> Term {
//     if from_w < to_w {
//         if from_s {
//             println!("int resize 1");
//             return term![Op::BvShl, vec![to_w, from_w, t]];
//         } else {
//             println!("int resize 2");
//             CTermData::CInt(false, to_w, t)
//         }
//     } else if from_w == to_w {
//         println!("int resize 3");
//         CTermData::CInt(from_s, from_w, t)
//     } else {
//         println!("int resize 4");
//         CTermData::CInt(from_s, from_w, term![Op::BvExtract(0, to_w); t])
//     }

//     // let from_w = if from_s { 1 } else { 0 };
//     // let from_w = bv_lit(from_w, 1);
//     // let to_w = bv_lit(to_w, 1);
//     // let to_w = term(Op::BvShl, vec![to_w, from_w, t]);
//     // term(Op::BvSrl, vec![to_w, from_w, t])
// }

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
        CTermData::CInt(_s, w, ref term) => match to_ty {
            Some(Ty::Bool) => CTerm {
                term: CTermData::CBool(term![Op::Not; term![Op::Eq; bv_lit(0, w), term.clone()]]),
                udef: t.udef,
            },
            Some(Ty::Int(to_s, to_w)) => {
                // TODO: add udef check
                // TODO: add int resize
                // let term_ = int_resize(s, w, to_s, to_w, term.clone());
                CTerm {
                    term: CTermData::CInt(to_s, to_w, term.clone()),
                    udef: t.udef,
                }
            }
            _ => panic!("Bad cast from {} to {:?}", ty, to_ty),
        },
        CTermData::CArray(ref ty, id) => match to_ty {
            Some(Ty::Ptr(_, _)) => {
                let offset = bv_lit(0, 32);
                CTerm {
                    term: CTermData::CStackPtr(ty.clone(), offset, id),
                    udef: t.udef,
                }
            }
            Some(Ty::Array(_, _, _)) => t.clone(),
            _ => panic!("Bad cast from {:#?} to {:?}", ty, to_ty),
        },
        CTermData::CStruct(ref ty, ref _term) => match to_ty {
            Some(Ty::Struct(_, _)) => t.clone(),
            _ => panic!("Bad cast from {:#?} to {:?}", ty, to_ty),
        },
        CTermData::CStackPtr(ref ty, _, id) => match to_ty {
            Some(Ty::Ptr(_, _)) => t.clone(),
            Some(Ty::Array(_, _, a_ty)) => CTerm {
                term: CTermData::CArray(*a_ty, id),
                udef: t.udef,
            },
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
        let signed_first = a_prom_ty.is_signed_int();
        let (s, u) = if signed_first {
            (a_prom, b_prom)
        } else {
            (b_prom, a_prom)
        };
        let (s_ty, u_ty) = (s.term.type_(), u.term.type_());
        let (s_r, u_r) = (s_ty.int_conversion_rank(), u_ty.int_conversion_rank());
        let (s_, u_) = if u_r >= s_r {
            (cast(Some(u_ty), s), u)
        } else if s_ty.num_bits() > u_ty.num_bits() {
            (s, cast(Some(s_ty), u))
        } else {
            let ty = Ty::Int(false, s_ty.num_bits());
            (cast(Some(ty.clone()), s), cast(Some(ty), u))
        };
        if signed_first {
            (s_, u_)
        } else {
            (u_, s_)
        }
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
        (CTermData::CArray(ty, aid), CTermData::CInt(_, _, y), Some(fu), _) => Ok(CTerm {
            term: CTermData::CStackPtr(ty, fu(bv_lit(0, 32), y), aid),
            udef: false,
        }),
        (CTermData::CStackPtr(ty, offset, aid), CTermData::CInt(_, _, y), Some(fu), _) => {
            Ok(CTerm {
                term: CTermData::CStackPtr(ty, fu(offset, y), aid),
                udef: false,
            })
        }

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

fn neq_base(a: Term, b: Term) -> Term {
    term![Op::Not; term![Op::Eq; a, b]]
}

pub fn neq(a: CTerm, b: CTerm) -> Result<CTerm, String> {
    wrap_bin_cmp("!=", Some(neq_base), Some(neq_base), a, b)
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

pub fn const_int(a: CTerm) -> Integer {
    let s = match &a.term {
        CTermData::CInt(s, _, i) => match &i.op {
            Op::Const(Value::BitVector(f)) => {
                if *s {
                    f.as_sint()
                } else {
                    f.uint().clone()
                }
            }
            _ => {
                panic!("Expected a constant integer")
            }
        },
        _ => panic!("Not CInt"),
    };
    s
}

fn wrap_shift(name: &str, op: BvBinOp, a: CTerm, b: CTerm) -> Result<CTerm, String> {
    let bc = const_int(b);
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
            Ty::Array(n, _, ty) => {
                assert!(precompute.is_none());
                let v: Vec<Self::T> = (0..*n)
                    .map(|i| self.declare_input(ctx, ty, idx_name(&name, i), visibility, None))
                    .collect();
                let mut mem = ctx.mem.borrow_mut();
                let id = mem.zero_allocate(*n, 32, ty.num_bits());
                let arr = Self::T {
                    term: CTermData::CArray(*ty.clone(), Some(id)),
                    udef: false,
                };
                for (i, t) in v.iter().enumerate() {
                    let val = t.term.term(ctx);
                    let t_term = leaf_term(Op::Const(Value::Bool(true)));
                    mem.store(id, bv_lit(i, 32), val, t_term);
                }
                arr
            }
            Ty::Struct(n, fs) => {
                let fields: Vec<(String, CTerm)> = fs
                    .fields()
                    .map(|(f_name, f_ty)| {
                        (
                            f_name.clone(),
                            self.declare_input(
                                ctx,
                                f_ty,
                                field_name(&name, f_name),
                                visibility,
                                None,
                            ),
                        )
                    })
                    .collect();

                cterm(CTermData::CStruct(
                    Ty::Struct(n.to_string(), fs.clone()),
                    FieldList::new(fields),
                ))
            }
            _ => unimplemented!("Unimplemented declare: {}", ty),
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
            (CTermData::CStruct(ta, fa), CTermData::CStruct(tb, fb)) if ta == tb => {
                let fields: Vec<(String, CTerm)> = fa
                    .fields()
                    .zip(fb.fields())
                    .map(|((a_name, a_term), (_b_name, b_term))| {
                        (
                            a_name.clone(),
                            self.ite(_ctx, cond.clone(), a_term.clone(), b_term.clone()),
                        )
                    })
                    .collect();

                Self::T {
                    term: CTermData::CStruct(ta, FieldList::new(fields)),
                    udef: false,
                }
            }
            (t, f) => panic!("Cannot ITE {} and {}", t, f),
        }
    }

    fn create_uninit(&self, ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T {
        ty.default(ctx)
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        match ty {
            Ty::Bool => CTerm {
                term: CTermData::CBool(Sort::Bool.default_term()),
                udef: false,
            },
            Ty::Int(s, w) => CTerm {
                term: CTermData::CInt(*s, *w, Sort::BitVector(*w).default_term()),
                udef: false,
            },
            Ty::Array(_s, _, ty) => CTerm {
                term: CTermData::CArray(*ty.clone(), None),
                udef: false,
            },
            Ty::Struct(_name, fs) => {
                let fields: Vec<(String, CTerm)> = fs
                    .fields()
                    .map(|(f_name, f_ty)| (f_name.clone(), self.initialize_return(f_ty, f_name)))
                    .collect();
                CTerm {
                    term: CTermData::CStruct(ty.clone(), FieldList::new(fields)),
                    udef: false,
                }
            }
            Ty::Ptr(size, ty) => CTerm {
                term: CTermData::CStackPtr(
                    *ty.clone(),
                    Sort::BitVector(*size).default_term(),
                    None,
                ),
                udef: false,
            },
        }
    }
}
