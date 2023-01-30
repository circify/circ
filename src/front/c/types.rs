//! C Types
use crate::circify::CirCtx;
use crate::front::c::term::CTerm;
use crate::front::c::term::CTermData;
use crate::front::field_list::FieldList;
use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, Eq)]
pub enum Ty {
    Void,
    Bool,
    Int(bool, usize),
    Struct(String, FieldList<Ty>),
    Array(usize, Vec<usize>, Box<Ty>),
    Ptr(usize, Box<Ty>),
}

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        use Ty::*;
        match (self, other) {
            (Void, Void) => true,
            (Bool, Bool) => true,
            (Int(a, a_size), Int(b, b_size)) => a == b && a_size == b_size,
            (Struct(_, a_list), Struct(_, b_list)) => a_list == b_list,
            (Array(a_len, a_dims, a_ty), Array(b_len, b_dims, b_ty)) => {
                a_len == b_len && a_dims == b_dims && *a_ty == *b_ty
            }
            (Ptr(a_size, a_ty), Ptr(b_size, b_ty)) => a_size == b_size && *a_ty == *b_ty,
            _ => false,
        }
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Void => write!(f, "void"),
            Ty::Bool => write!(f, "bool"),
            Ty::Int(s, w) => {
                if *s {
                    write!(f, "s{w}")
                } else {
                    write!(f, "u{w}")
                }
            }
            Ty::Struct(n, fields) => {
                let mut o = f.debug_struct(n);
                for (f_name, f_ty) in fields.fields() {
                    o.field(f_name, f_ty);
                }
                o.finish()
            }
            Ty::Array(n, _, b) => {
                let mut dims = vec![n];
                let mut bb = b.as_ref();
                while let Ty::Array(n, _, b) = bb {
                    bb = b.as_ref();
                    dims.push(n);
                }
                write!(f, "{bb}")?;
                dims.iter().try_for_each(|d| write!(f, "[{d}]"))
            }
            Ty::Ptr(s, t) => {
                write!(f, "ptr{s}({t})")
            }
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{self}")
    }
}

impl Ty {
    pub fn sort(&self) -> Sort {
        match self {
            Self::Void => Sort::Bool,
            Self::Bool => Sort::Bool,
            Self::Int(_s, w) => Sort::BitVector(*w),
            Self::Array(n, _, b) => {
                Sort::Array(Box::new(Sort::BitVector(32)), Box::new(b.sort()), *n)
            }
            Self::Struct(_name, fs) => {
                Sort::Tuple(fs.fields().map(|(_f_name, f_ty)| f_ty.sort()).collect())
            }
            Self::Ptr(_, _) => panic!("Ptrs don't have a CirC sort"),
        }
    }

    fn default_ir_term(&self) -> Term {
        self.sort().default_term()
    }

    pub fn default(&self, ctx: &CirCtx) -> CTerm {
        match self {
            Self::Void => {
                unimplemented!("Void not implemented");
            }
            Self::Bool => CTerm {
                term: CTermData::Bool(self.default_ir_term()),
                udef: bool_lit(false),
            },
            Self::Int(s, w) => CTerm {
                term: CTermData::Int(*s, *w, self.default_ir_term()),
                udef: bool_lit(false),
            },
            Self::Array(s, _, ty) => {
                let mut mem = ctx.mem.borrow_mut();
                let id = mem.zero_allocate(*s, 32, ty.num_bits());
                CTerm {
                    term: CTermData::Array(self.clone(), Some(id)),
                    udef: bool_lit(false),
                }
            }
            Self::Ptr(s, ty) => {
                let mut mem = ctx.mem.borrow_mut();
                let id = mem.zero_allocate(*s, 32, ty.num_bits());
                CTerm {
                    term: CTermData::StackPtr(*ty.clone(), bv_lit(0, *s), Some(id)),
                    udef: bool_lit(false),
                }
            }
            Self::Struct(_name, fs) => {
                let fields: Vec<(String, CTerm)> = fs
                    .fields()
                    .map(|(f_name, f_ty)| (f_name.clone(), f_ty.default(ctx)))
                    .collect();
                CTerm {
                    term: CTermData::Struct(self.clone(), FieldList::new(fields)),
                    udef: bool_lit(false),
                }
            }
        }
    }

    pub fn is_arith_type(&self) -> bool {
        matches!(self, Ty::Int(_, _) | Ty::Bool)
    }

    pub fn is_signed_int(&self) -> bool {
        if let Ty::Int(s, w) = self {
            if *w == 8 || *w == 16 || *w == 32 || *w == 64 {
                return *s;
            }
            return false;
        }
        false
    }

    pub fn is_unsigned_int(&self) -> bool {
        if let Ty::Int(s, w) = self {
            if !*s && (*w == 8 || *w == 16 || *w == 32 || *w == 64) {
                return !*s;
            }
            return *s;
        }
        false
    }

    pub fn is_integer_type(&self) -> bool {
        self.is_signed_int() || self.is_unsigned_int()
    }

    pub fn int_conversion_rank(&self) -> usize {
        match self {
            Ty::Int(_, w) => *w,
            Ty::Bool => 1,
            _ => panic!("int_conversion_rank received a non-int type: {:#?}", self),
        }
    }

    pub fn total_num_bits(&self) -> usize {
        match self {
            Ty::Void => 0,
            Ty::Int(_, w) => *w,
            Ty::Bool => 1,
            Ty::Array(s, _, t) => s * t.num_bits(),
            Ty::Ptr(s, t) => s * t.num_bits(),
            Ty::Struct(_, fs) => fs.fields().fold(0, |sum, (_, ty)| sum + ty.num_bits()),
        }
    }

    pub fn num_bits(&self) -> usize {
        match self {
            Ty::Void => 0,
            Ty::Int(_, w) => *w,
            Ty::Bool => 1,
            Ty::Array(_, _, _) => 32,
            Ty::Ptr(s, _) => *s,
            Ty::Struct(_, fs) => fs.fields().fold(0, |sum, (_, ty)| sum + ty.num_bits()),
        }
    }

    pub fn inner_ty(self) -> Ty {
        match self {
            Ty::Void => self,
            Ty::Int(_, _) => self,
            Ty::Bool => self,
            Ty::Array(_, _, t) => *t,
            Ty::Ptr(_, t) => *t,
            Ty::Struct(_, _) => unimplemented!("Struct does not have an inner type"),
        }
    }
}
