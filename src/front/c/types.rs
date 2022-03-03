//! C Types
use crate::front::c::term::CTerm;
use crate::front::c::term::CTermData;
use crate::front::c::Circify;
use crate::front::c::Ct;
use crate::front::field_list::FieldList;
use crate::ir::term::*;

use std::fmt::{self, Display, Formatter};

#[derive(Clone, PartialEq, Eq)]
pub enum Ty {
    Bool,
    Int(bool, usize),
    Struct(String, FieldList<Ty>),
    Array(usize, Box<Ty>),
}

impl Display for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Ty::Bool => write!(f, "bool"),
            Ty::Int(s, w) => {
                if *s {
                    write!(f, "s{}", w)
                } else {
                    write!(f, "u{}", w)
                }
            }
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
                write!(f, "{}", bb)?;
                dims.iter().try_for_each(|d| write!(f, "[{}]", d))
            }
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Ty {
    fn sort(&self) -> Sort {
        match self {
            Self::Bool => Sort::Bool,
            Self::Int(_s, w) => Sort::BitVector(*w),
            Self::Array(n, b) => Sort::Array(Box::new(Sort::BitVector(32)), Box::new(b.sort()), *n),
            Self::Struct(_name, fs) => {
                Sort::Tuple(fs.fields().map(|(_f_name, f_ty)| f_ty.sort()).collect())
            }
        }
    }
    fn default_ir_term(&self) -> Term {
        self.sort().default_term()
    }
    pub fn default(&self, circ: &mut Circify<Ct>) -> CTerm {
        match self {
            Self::Bool => CTerm {
                term: CTermData::CBool(self.default_ir_term()),
                udef: false,
            },
            Self::Int(s, w) => CTerm {
                term: CTermData::CInt(*s, *w, self.default_ir_term()),
                udef: false,
            },
            Self::Array(s, ty) => {
                let id = circ.zero_allocate(*s, 32, ty.num_bits());
                CTerm {
                    term: CTermData::CArray(*ty.clone(), Some(id)),
                    udef: false,
                }
            }
            Self::Struct(_name, fs) => {
                let fields: Vec<(String, CTerm)> = fs
                    .fields()
                    .map(|(f_name, f_ty)| (f_name.clone(), f_ty.default(circ)))
                    .collect();
                CTerm {
                    term: CTermData::CStruct(self.clone(), FieldList::new(fields)),
                    udef: false,
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

    pub fn _total_num_bits(&self, ty: Ty) -> usize {
        match ty {
            Ty::Int(_, w) => w,
            Ty::Bool => 1,
            Ty::Array(s, t) => s * t.num_bits(),
            Ty::Struct(_, fs) => fs.fields().fold(0, |sum, (_, ty)| sum + ty.num_bits()),
        }
    }

    pub fn num_bits(&self) -> usize {
        match self {
            Ty::Int(_, w) => *w,
            Ty::Bool => 1,
            Ty::Array(_, _) => 32,
            Ty::Struct(_, fs) => fs.fields().fold(0, |sum, (_, ty)| sum + ty.num_bits()),
        }
    }

    pub fn inner_ty(self) -> Ty {
        match self {
            Ty::Int(_, _) => self,
            Ty::Bool => self,
            Ty::Array(_, t) => *t,
            Ty::Struct(_, _) => unimplemented!("Struct does not have an inner type"),
        }
    }
}
