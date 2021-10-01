//! C Terms
use crate::circify::{CirCtx, Embeddable};
use crate::front::c::types::*;
use crate::ir::term::*;
use rug::Integer;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};


#[derive(Clone)]
pub enum CTermData {
    CBool(Term),
    CInt(usize, Term),
}

impl CTermData {
    pub fn type_(&self) -> Ty {
        match self {
            Self::CBool(_) => Ty::Bool,
            Self::CInt(w, _) => Ty::Uint(*w),
        }
    }
    /// Get all IR terms inside this value, as a list.
    pub fn terms(&self) -> Vec<Term> {
        let mut output: Vec<Term> = Vec::new();
        fn terms_tail(term: &CTermData, output: &mut Vec<Term>) {
            match term {
                CTermData::CBool(b) => output.push(b.clone()),
                CTermData::CInt(_, b) => output.push(b.clone()),
            }
        }
        terms_tail(self, &mut output);
        output
    }

    pub fn term(&self) -> Term {
        match self {
            CTermData::CBool(b) => b.clone(),
            CTermData::CInt(_, b) => b.clone(),
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

pub fn cast(to_ty: Option<Ty>, t: CTerm) -> CTerm {
    let ty = t.term.type_();
    match t.term {
        CTermData::CBool(ref term) => {
            match to_ty {
                Some(Ty::Uint(_)) => {    
                    CTerm {
                        // THIS IS BROKEN PLS CAST CORRECTLY
                        term: CTermData::CInt(32, term.clone()),
                        udef: t.udef
                    }
                }
                Some(Ty::Bool) => {
                    t.clone()
                }
                None => panic!("Bad cast from {} to {:?}", ty, to_ty)
            }
        }   
        CTermData::CInt(w, ref term) => {
            match to_ty {
                Some(Ty::Bool) => {
                    CTerm {
                        term: CTermData::CBool(term![Op::Not; term![Op::Eq; bv_lit(0, w), term.clone()]]),
                        udef: t.udef
                    }
                }
                Some(Ty::Uint(_)) => {
                    t.clone()
                }
                None => panic!("Bad cast from {} to {:?}", ty, to_ty)
            }
        }
        // _ => panic!("Bad cast from {} to {}", ty, to_ty)
    }
}

fn int_promotion(t: &CTerm) -> CTerm {
    match &t.term {
        CTermData::CBool(term) => {
            CTerm {
                term: CTermData::CInt(32, term.clone()),
                udef: t.udef
            }
        }
        CTermData::CInt(_, _) => {
            t.clone()
        }
    }
}

fn inner_usual_arith_conversions(a: &CTerm, b: &CTerm) -> (CTerm, CTerm) {
    // let a_ty = a.term.type_();
    // let b_ty = b.term.type_();
    let a_prom = int_promotion(a);
    let b_prom = int_promotion(b);
    let a_prom_ty = a_prom.term.type_();
    let b_prom_ty = b_prom.term.type_();
    
    if a_prom_ty == b_prom_ty {
        return (a_prom, b_prom);
    }

    unimplemented!("Not implemented case in iUAC");
}

fn usual_arith_conversions(a: CTerm, b: CTerm) -> (CTerm, CTerm) {
    if is_arith_type(&a) && is_arith_type(&b) {
        let (a_, b_) = inner_usual_arith_conversions(&a, &b);
        if a_.term.type_() == b_.term.type_() {
            (a_, b_)
        } else {
            panic!("UAC failed: {:#?}, {:#?} to non-equal {:#?}, {:#?}", a, b, a_, b_);
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
        (CTermData::CInt(nx, x), CTermData::CInt(ny, y), Some(fu), _) if nx == ny => Ok(CTerm {
            term: CTermData::CInt(nx, fu(x, y)),
            udef: false,
        }),
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
    b: CTerm
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
    b: CTerm
) -> Result<CTerm, String> {
    let (a_arith, b_arith) = usual_arith_conversions(a, b);
    match (a_arith.term, b_arith.term, fu, fb) {
        (CTermData::CInt(nx, x), CTermData::CInt(ny, y), Some(fu), _) if nx == ny => Ok(CTerm {
            term: CTermData::CBool(fu(x, y)),
            udef: false,
        }),
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
        CTermData::CInt(_, i) => match &i.op {
            Op::Const(Value::BitVector(f)) => Some(f.uint().clone()),
            _ => None,
        },
        _ => None,
    };
    s.ok_or_else(|| format!("{} is not a constant integer", a))
}

pub fn bool(a: CTerm) -> Result<Term, String> {
    match a.term {
        CTermData::CBool(b) => Ok(b),
        a => Err(format!("{} is not a boolean", a)),
    }
}

fn ite(c: Term, a: CTerm, b: CTerm) -> Result<CTerm, String> {
    match (a.term, b.term) {
        (CTermData::CInt(na, a), CTermData::CInt(nb, b)) if na == nb => Ok(
            CTerm {
                term: CTermData::CInt(na, term![Op::Ite; c, a, b]),
                udef: false,
            }
        ),
        (CTermData::CBool(a), CTermData::CBool(b)) => Ok(
            CTerm {
                term: CTermData::CBool(term![Op::Ite; c, a, b]),
                udef: false,
            }
        ),
        (x, y) => Err(format!("Cannot perform ITE on {} and {}", x, y)),
    }
}

pub fn cond(c: CTerm, a: CTerm, b: CTerm) -> Result<CTerm, String> {
    ite(bool(c)?, a, b)
}

pub struct Ct {
    values: Option<HashMap<String, Integer>>,
}

impl Ct {
    pub fn new(values: Option<HashMap<String, Integer>>) -> Self {
        Self {
            values,
        }
    }
}

impl Embeddable for Ct {
    type T = CTerm;
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
            Ty::Bool => {
                Self::T {
                    term: CTermData::CBool(
                            ctx.cs.borrow_mut().new_var(
                            &raw_name,
                            Sort::Bool,
                            || Value::Bool(get_int_val() != 0),
                            visibility,
                        )
                    ),
                    udef: false,
                }
            },
            Ty::Uint(w) => {
                Self::T {
                    term: CTermData::CInt(
                            *w,
                            ctx.cs.borrow_mut().new_var(
                            &raw_name,
                            Sort::BitVector(*w),
                            || Value::BitVector(BitVector::new(get_int_val(), *w)),
                            visibility,
                        ),
                    ),
                    udef: false,
                }
            }
        }
    }
    fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
        match (t.term, f.term) {
            (CTermData::CBool(a), CTermData::CBool(b)) => {
                Self::T {
                    term: CTermData::CBool(term![Op::Ite; cond, a, b]),
                    udef: false,
                }
            }
            (CTermData::CInt(wa, a), CTermData::CInt(wb, b)) if wa == wb => {
                Self::T {
                    term: CTermData::CInt(wa, term![Op::Ite; cond, a, b]),
                    udef: false,
                }
            }
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
        assert!(&t.term.type_() == ty);
        match (ty, t.term) {
            (_, CTermData::CBool(b)) => {
                Self::T {
                    term: CTermData::CBool(ctx.cs.borrow_mut().assign(&name, b, visibility)),
                    udef: false,
                }
            }
            (_, CTermData::CInt(w, b)) => {
                Self::T {
                    term: CTermData::CInt(w, ctx.cs.borrow_mut().assign(&name, b, visibility)),
                    udef: false,
                }
            }
        }
    }

    fn values(&self) -> bool {
        self.values.is_some()
    }

    fn type_of(&self, cterm: &Self::T) -> Self::Ty {
        cterm.term.type_()
    }

    fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &String) -> Self::T {
        ty.default()
    }
}