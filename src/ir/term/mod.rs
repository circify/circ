//! IR term definition
//!
//! Generally based on SMT-LIB, and its theories.
use crate::util::once::OnceQueue;
use ahash::{AHashMap, AHashSet};
use hashconsing::{HConsed, WHConsed};
use lazy_static::lazy_static;
use log::debug;
use rug::Integer;
use std::collections::BTreeMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::sync::{Arc, RwLock};

pub mod bv;
pub mod dist;
pub mod extras;
pub mod field;
pub mod ty;

pub use bv::BitVector;
pub use field::FieldElem;
pub use ty::{check, check_rec, TypeError, TypeErrorReason};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// An operator
pub enum Op {
    /// a variable
    Var(String, Sort),
    /// a constant
    Const(Value),

    /// if-then-else: ternary
    Ite,
    /// equality
    Eq,

    /// bit-vector binary operator
    BvBinOp(BvBinOp),
    /// bit-vector binary predicate
    BvBinPred(BvBinPred),
    /// bit-vector n-ary operator
    BvNaryOp(BvNaryOp),
    /// bit-vector unary operator
    BvUnOp(BvUnOp),
    /// single-bit bit-vector from a boolean
    BoolToBv,
    /// Get bits (high) through (low) from the underlying bit-vector.
    ///
    /// Zero-indexed and inclusive.
    BvExtract(usize, usize),
    /// bit-vector concatenation. n-ary. Low-index arguements map to high-order bits
    BvConcat,
    /// add this many zero bits
    BvUext(usize),
    /// add this many sign-extend bits
    BvSext(usize),
    /// translate a prime-field element into a certain-width bit-vector.
    PfToBv(usize),

    /// boolean implication (binary)
    Implies,
    /// boolean n-ary operator
    BoolNaryOp(BoolNaryOp),
    /// boolean not
    Not,
    /// get this index bit from an input bit-vector
    BvBit(usize),
    // Ternary majority operator.
    /// boolean majority (ternary)
    BoolMaj,

    /// floating-point binary operator
    FpBinOp(FpBinOp),
    /// floating-point binary predicate
    FpBinPred(FpBinPred),
    /// floating-point unary predicate
    FpUnPred(FpBinPred),
    /// floating-point unary operator
    FpUnOp(FpUnOp),
    //FpFma,
    /// cast bit-vector to floating-point, as bits
    BvToFp,
    /// translate the (unsigned) bit-vector number represented by the argument to a floating-point
    /// value of this width.
    UbvToFp(usize),
    /// translate the (signed) bit-vector number represented by the argument to a floating-point
    /// value of this width.
    SbvToFp(usize),
    // dest width
    /// translate the number represented by the argument to a floating-point value of this width.
    FpToFp(usize),

    /// Prime-field unary operator
    PfUnOp(PfUnOp),
    /// Prime-field n-ary operator
    PfNaryOp(PfNaryOp),

    // key sort, size
    /// A unary operator.
    ///
    /// Make an array from keys of the given sort, which is equal to the provided argument at all
    /// places.
    ///
    /// Has space for the provided number of elements. Note that this assumes an order and starting
    /// point for keys.
    ConstArray(Sort, usize),

    /// Binary operator, with arguments (array, index).
    ///
    /// Gets the value at index in array.
    Select,
    /// Ternary operator, with arguments (array, index, value).
    ///
    /// Makes an array equal to `array`, but with `value` at `index`.
    Store,

    /// Assemble n things into a tuple
    Tuple,
    /// Get the n'th element of a tuple
    Field(usize),
}

/// Boolean AND
pub const AND: Op = Op::BoolNaryOp(BoolNaryOp::And);
/// Boolean OR
pub const OR: Op = Op::BoolNaryOp(BoolNaryOp::Or);
/// Boolean XOR
pub const XOR: Op = Op::BoolNaryOp(BoolNaryOp::Xor);
/// Boolean NOT
pub const NOT: Op = Op::Not;
/// Equal to
pub const EQ: Op = Op::Eq;
/// If-then-else
pub const ITE: Op = Op::Ite;
/// Boolean implication
pub const IMPLIES: Op = Op::Implies;
/// Bit-vector AND
pub const BV_AND: Op = Op::BvNaryOp(BvNaryOp::And);
/// Bit-vector OR
pub const BV_OR: Op = Op::BvNaryOp(BvNaryOp::Or);
/// Bit-vector XOR
pub const BV_XOR: Op = Op::BvNaryOp(BvNaryOp::Xor);
/// Bit-vector multiplication
pub const BV_MUL: Op = Op::BvNaryOp(BvNaryOp::Mul);
/// Bit-vector addition
pub const BV_ADD: Op = Op::BvNaryOp(BvNaryOp::Add);
/// Bit-vector subtraction
pub const BV_SUB: Op = Op::BvBinOp(BvBinOp::Sub);
/// Bit-vector unsigned division
pub const BV_UDIV: Op = Op::BvBinOp(BvBinOp::Udiv);
/// Bit-vector unsigned remainder
pub const BV_UREM: Op = Op::BvBinOp(BvBinOp::Urem);
/// Bit-vector shift left
pub const BV_SHL: Op = Op::BvBinOp(BvBinOp::Shl);
/// Bit-vector logical shift right
pub const BV_LSHR: Op = Op::BvBinOp(BvBinOp::Lshr);
/// Bit-vector arithmetic shift right
pub const BV_ASHR: Op = Op::BvBinOp(BvBinOp::Ashr);
/// Bit-vector negation
pub const BV_NEG: Op = Op::BvUnOp(BvUnOp::Neg);
/// Bit-vector not
pub const BV_NOT: Op = Op::BvUnOp(BvUnOp::Not);
/// Bit-vector unsigned less than
pub const BV_ULT: Op = Op::BvBinPred(BvBinPred::Ult);
/// Bit-vector unsigned greater than
pub const BV_UGT: Op = Op::BvBinPred(BvBinPred::Ugt);
/// Bit-vector unsigned less than or equal
pub const BV_ULE: Op = Op::BvBinPred(BvBinPred::Ule);
/// Bit-vector unsigned greater than or equal
pub const BV_UGE: Op = Op::BvBinPred(BvBinPred::Uge);
/// Bit-vector signed less than
pub const BV_SLT: Op = Op::BvBinPred(BvBinPred::Slt);
/// Bit-vector signed greater than
pub const BV_SGT: Op = Op::BvBinPred(BvBinPred::Sgt);
/// Bit-vector signed less than or equal
pub const BV_SLE: Op = Op::BvBinPred(BvBinPred::Sle);
/// Bit-vector signed greater than or equal
pub const BV_SGE: Op = Op::BvBinPred(BvBinPred::Sge);
/// Bit-vector of length one, from boolean
pub const BOOL_TO_BV: Op = Op::BoolToBv;
/// Bit-vector concatenation (high || low). N-ary.
pub const BV_CONCAT: Op = Op::BvConcat;
/// prime-field negation
pub const PF_NEG: Op = Op::PfUnOp(PfUnOp::Neg);
/// prime-field reciprocal
pub const PF_RECIP: Op = Op::PfUnOp(PfUnOp::Recip);
/// prime-field addition
pub const PF_ADD: Op = Op::PfNaryOp(PfNaryOp::Add);
/// prime-field multiplication
pub const PF_MUL: Op = Op::PfNaryOp(PfNaryOp::Mul);

impl Op {
    /// Number of arguments for this operator. `None` if n-ary.
    pub fn arity(&self) -> Option<usize> {
        match self {
            Op::Ite => Some(3),
            Op::Eq => Some(2),
            Op::Var(_, _) => Some(0),
            Op::Const(_) => Some(0),
            Op::BvBinOp(_) => Some(2),
            Op::BvBinPred(_) => Some(2),
            Op::BvNaryOp(_) => None,
            Op::BvUnOp(_) => Some(1),
            Op::BoolToBv => Some(1),
            Op::BvExtract(_, _) => Some(1),
            Op::BvConcat => None,
            Op::BvUext(_) => Some(1),
            Op::BvSext(_) => Some(1),
            Op::PfToBv(_) => Some(1),
            Op::Implies => Some(2),
            Op::BoolNaryOp(_) => None,
            Op::Not => Some(1),
            Op::BvBit(_) => Some(1),
            Op::BoolMaj => Some(3),
            Op::FpBinOp(_) => Some(2),
            Op::FpBinPred(_) => Some(2),
            Op::FpUnPred(_) => Some(1),
            Op::FpUnOp(_) => Some(1),
            Op::BvToFp => Some(1),
            Op::UbvToFp(_) => Some(1),
            Op::SbvToFp(_) => Some(1),
            Op::FpToFp(_) => Some(1),
            Op::PfUnOp(_) => Some(1),
            Op::PfNaryOp(_) => None,
            Op::ConstArray(_, _) => Some(1),
            Op::Select => Some(2),
            Op::Store => Some(3),
            Op::Tuple => None,
            Op::Field(_) => Some(1),
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Op::Ite => write!(f, "ite"),
            Op::Eq => write!(f, "="),
            Op::Var(n, _) => write!(f, "{}", n),
            Op::Const(c) => write!(f, "{}", c),
            Op::BvBinOp(a) => write!(f, "{}", a),
            Op::BvBinPred(a) => write!(f, "{}", a),
            Op::BvNaryOp(a) => write!(f, "{}", a),
            Op::BvUnOp(a) => write!(f, "{}", a),
            Op::BoolToBv => write!(f, "bool2bv"),
            Op::BvExtract(a, b) => write!(f, "extract {} {}", a, b),
            Op::BvConcat => write!(f, "concat"),
            Op::BvUext(a) => write!(f, "uext {}", a),
            Op::BvSext(a) => write!(f, "sext {}", a),
            Op::PfToBv(a) => write!(f, "pf2bv {}", a),
            Op::Implies => write!(f, "=>"),
            Op::BoolNaryOp(a) => write!(f, "{}", a),
            Op::Not => write!(f, "not"),
            Op::BvBit(a) => write!(f, "bit {}", a),
            Op::BoolMaj => write!(f, "maj"),
            Op::FpBinOp(a) => write!(f, "{}", a),
            Op::FpBinPred(a) => write!(f, "{}", a),
            Op::FpUnPred(a) => write!(f, "{}", a),
            Op::FpUnOp(a) => write!(f, "{}", a),
            Op::BvToFp => write!(f, "bv2fp"),
            Op::UbvToFp(a) => write!(f, "ubv2fp {}", a),
            Op::SbvToFp(a) => write!(f, "sbv2fp {}", a),
            Op::FpToFp(a) => write!(f, "fp2fp {}", a),
            Op::PfUnOp(a) => write!(f, "{}", a),
            Op::PfNaryOp(a) => write!(f, "{}", a),
            Op::ConstArray(_, s) => write!(f, "const-array {}", s),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
            Op::Tuple => write!(f, "tuple"),
            Op::Field(i) => write!(f, "field{}", i),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Boolean n-ary operator
pub enum BoolNaryOp {
    /// Boolean AND
    And,
    /// Boolean XOR
    Xor,
    /// Boolean OR
    Or,
}

impl Display for BoolNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BoolNaryOp::And => write!(f, "and"),
            BoolNaryOp::Or => write!(f, "or"),
            BoolNaryOp::Xor => write!(f, "xor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector binary operator
pub enum BvBinOp {
    /// Bit-vector (-)
    Sub,
    /// Bit-vector (/)
    Udiv,
    /// Bit-vector (%)
    Urem,
    /// Bit-vector (<<)
    Shl,
    /// Bit-vector arithmetic (sign extend) (>>)
    Ashr,
    /// Bit-vector logical (zero fill) (>>)
    Lshr,
}

impl Display for BvBinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvBinOp::Sub => write!(f, "bvsub"),
            BvBinOp::Udiv => write!(f, "bvudiv"),
            BvBinOp::Urem => write!(f, "bvurem"),
            BvBinOp::Shl => write!(f, "bvshl"),
            BvBinOp::Ashr => write!(f, "bvashr"),
            BvBinOp::Lshr => write!(f, "bvlshr"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector binary predicate
pub enum BvBinPred {
    // TODO: add overflow predicates.
    /// Bit-vector unsigned (<)
    Ult,
    /// Bit-vector unsigned (>)
    Ugt,
    /// Bit-vector unsigned (<=)
    Ule,
    /// Bit-vector unsigned (>=)
    Uge,
    /// Bit-vector signed (<)
    Slt,
    /// Bit-vector signed (>)
    Sgt,
    /// Bit-vector signed (<=)
    Sle,
    /// Bit-vector signed (>=)
    Sge,
}

impl Display for BvBinPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvBinPred::Ult => write!(f, "bvult"),
            BvBinPred::Ugt => write!(f, "bvugt"),
            BvBinPred::Ule => write!(f, "bvule"),
            BvBinPred::Uge => write!(f, "bvuge"),
            BvBinPred::Slt => write!(f, "bvslt"),
            BvBinPred::Sgt => write!(f, "bvsgt"),
            BvBinPred::Sle => write!(f, "bvsle"),
            BvBinPred::Sge => write!(f, "bvsge"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector n-ary operator
pub enum BvNaryOp {
    /// Bit-vector (+)
    Add,
    /// Bit-vector (*)
    Mul,
    /// Bit-vector bitwise OR
    Or,
    /// Bit-vector bitwise AND
    And,
    /// Bit-vector bitwise XOR
    Xor,
}

impl Display for BvNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvNaryOp::Add => write!(f, "bvadd"),
            BvNaryOp::Mul => write!(f, "bvmul"),
            BvNaryOp::Or => write!(f, "bvor"),
            BvNaryOp::And => write!(f, "bvand"),
            BvNaryOp::Xor => write!(f, "bvxor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Bit-vector unary operator
pub enum BvUnOp {
    /// Bit-vector bitwise not
    Not,
    /// Bit-vector two's complement negation
    Neg,
}

impl Display for BvUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BvUnOp::Not => write!(f, "bvnot"),
            BvUnOp::Neg => write!(f, "bvneg"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point binary operator
pub enum FpBinOp {
    /// Floating-point (+)
    Add,
    /// Floating-point (*)
    Mul,
    /// Floating-point (-)
    Sub,
    /// Floating-point (/)
    Div,
    /// Floating-point (%)
    Rem,
    /// Floating-point max
    Max,
    /// Floating-point min
    Min,
}

impl Display for FpBinOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpBinOp::Add => write!(f, "fpadd"),
            FpBinOp::Mul => write!(f, "fpmul"),
            FpBinOp::Sub => write!(f, "fpsub"),
            FpBinOp::Div => write!(f, "fpdiv"),
            FpBinOp::Rem => write!(f, "fprem"),
            FpBinOp::Max => write!(f, "fpmax"),
            FpBinOp::Min => write!(f, "fpmin"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point unary operator
pub enum FpUnOp {
    /// Floating-point unary negation
    Neg,
    /// Floating-point absolute value
    Abs,
    /// Floating-point square root
    Sqrt,
    /// Floating-point round
    Round,
}

impl Display for FpUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpUnOp::Neg => write!(f, "fpneg"),
            FpUnOp::Abs => write!(f, "fpabs"),
            FpUnOp::Sqrt => write!(f, "fpsqrt"),
            FpUnOp::Round => write!(f, "fpround"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point binary predicate
pub enum FpBinPred {
    /// Floating-point (<=)
    Le,
    /// Floating-point (<)
    Lt,
    /// Floating-point (=)
    Eq,
    /// Floating-point (>=)
    Ge,
    /// Floating-point (>)
    Gt,
}

impl Display for FpBinPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpBinPred::Le => write!(f, "fple"),
            FpBinPred::Lt => write!(f, "fplt"),
            FpBinPred::Eq => write!(f, "fpeq"),
            FpBinPred::Ge => write!(f, "fpge"),
            FpBinPred::Gt => write!(f, "fpgt"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Floating-point unary predicate
pub enum FpUnPred {
    /// Is this normal?
    Normal,
    /// Is this subnormal?
    Subnormal,
    /// Is this zero (or negative zero)?
    Zero,
    /// Is this infinite?
    Infinite,
    /// Is this not-a-number?
    Nan,
    /// Is this negative?
    Negative,
    /// Is this positive?
    Positive,
}

impl Display for FpUnPred {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            FpUnPred::Normal => write!(f, "fpnormal"),
            FpUnPred::Subnormal => write!(f, "fpsubnormal"),
            FpUnPred::Zero => write!(f, "fpzero"),
            FpUnPred::Infinite => write!(f, "fpinfinite"),
            FpUnPred::Nan => write!(f, "fpnan"),
            FpUnPred::Negative => write!(f, "fpnegative"),
            FpUnPred::Positive => write!(f, "fppositive"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Finite field n-ary operator
pub enum PfNaryOp {
    /// Finite field (+)
    Add,
    /// Finite field (*)
    Mul,
}

impl Display for PfNaryOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PfNaryOp::Add => write!(f, "+"),
            PfNaryOp::Mul => write!(f, "*"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// Finite field n-ary operator
pub enum PfUnOp {
    /// Finite field negation
    Neg,
    /// Finite field reciprocal
    Recip,
}

impl Display for PfUnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            PfUnOp::Neg => write!(f, "-"),
            PfUnOp::Recip => write!(f, "pfrecip"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
/// A term: an operator applied to arguements
pub struct TermData {
    /// the operator
    pub op: Op,
    /// the arguments
    pub cs: Vec<Term>,
}

impl Display for TermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.op.arity() == Some(0) {
            write!(f, "{}", self.op)
        } else {
            write!(f, "({}", self.op)?;
            for c in &self.cs {
                write!(f, " {}", c)?;
            }
            write!(f, ")")
        }
    }
}

impl Debug for TermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

#[derive(Clone, PartialEq, Debug, PartialOrd)]
/// An IR value (aka literal)
pub enum Value {
    /// Bit-vector
    BitVector(BitVector),
    /// f32
    F32(f32),
    /// f64
    F64(f64),
    /// Arbitrary-precision integer
    Int(Integer),
    /// Finite field element
    Field(FieldElem),
    /// Boolean
    Bool(bool),
    /// Array
    Array(Sort, Box<Value>, BTreeMap<Value, Value>, usize),
    /// Tuple
    Tuple(Vec<Value>),
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Value::Bool(b) => write!(f, "{}", b),
            Value::F32(b) => write!(f, "{}", b),
            Value::F64(b) => write!(f, "{}", b),
            Value::Int(b) => write!(f, "{}", b),
            Value::Field(b) => write!(f, "{}", b),
            Value::BitVector(b) => write!(f, "{}", b),
            Value::Tuple(fields) => {
                write!(f, "(tuple")?;
                for field in fields {
                    write!(f, " {}", field)?;
                }
                write!(f, ")")
            }
            Value::Array(_s, d, map, size) => {
                write!(f, "(map default:{} size:{} {:?})", d, size, map)
            }
        }
    }
}

impl std::cmp::Eq for Value {}
impl std::cmp::Ord for Value {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.partial_cmp(o).expect("broken Value cmp")
    }
}
impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Value::BitVector(bv) => bv.hash(state),
            Value::F32(bv) => bv.to_bits().hash(state),
            Value::F64(bv) => bv.to_bits().hash(state),
            Value::Int(bv) => bv.hash(state),
            Value::Field(bv) => bv.hash(state),
            Value::Bool(bv) => bv.hash(state),
            Value::Array(s, d, a, size) => {
                s.hash(state);
                d.hash(state);
                a.hash(state);
                size.hash(state);
            }
            Value::Tuple(s) => {
                s.hash(state);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
/// The "type" of an IR term
pub enum Sort {
    /// bit-vectors of this width
    BitVector(usize),
    /// f32s
    F32,
    /// f64s
    F64,
    /// arbitrary-precision integer
    Int,
    /// prime field, integers mod this modulus
    Field(Arc<Integer>),
    /// boolean
    Bool,
    /// Array from one sort to another, of fixed size.
    ///
    /// size presumes an order, and a zero, for the key sort.
    Array(Box<Sort>, Box<Sort>, usize),
    /// A tuple
    Tuple(Vec<Sort>),
}

impl Sort {
    #[track_caller]
    /// Unwrap the bitsize of this bit-vector, panicking otherwise.
    pub fn as_bv(&self) -> usize {
        if let Sort::BitVector(w) = self {
            *w
        } else {
            panic!("{} is not a bit-vector", self)
        }
    }

    #[track_caller]
    /// Unwrap the modulus of this prime field, panicking otherwise.
    pub fn as_pf(&self) -> Arc<Integer> {
        if let Sort::Field(w) = self {
            w.clone()
        } else {
            panic!("{} is not a field", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent sorts of this tuple, panicking otherwise.
    pub fn as_tuple(&self) -> &Vec<Sort> {
        if let Sort::Tuple(w) = self {
            &w
        } else {
            panic!("{} is not a tuple", self)
        }
    }

    /// An iterator over the elements of this sort.
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn elems_iter(&self) -> Box<dyn Iterator<Item = Term>> {
        match self {
            Sort::Bool => Box::new(
                vec![false, true]
                    .into_iter()
                    .map(|b| leaf_term(Op::Const(Value::Bool(b)))),
            ),
            Sort::BitVector(w) => {
                let w = *w;
                let lim = Integer::from(1) << w as u32;
                Box::new(
                    std::iter::successors(Some(Integer::from(0)), move |p| {
                        let q = p.clone() + 1;
                        if q < lim {
                            Some(q)
                        } else {
                            None
                        }
                    })
                    .map(move |i| bv_lit(i, w)),
                )
            }
            Sort::Field(m) => {
                let m = m.clone();
                let m2 = m.clone();
                Box::new(
                    std::iter::successors(Some(Integer::from(0)), move |p| {
                        let q = p.clone() + 1;
                        if &q < &*m {
                            Some(q)
                        } else {
                            None
                        }
                    })
                    .map(move |i| {
                        leaf_term(Op::Const(Value::Field(FieldElem::new(i, m2.clone()))))
                    }),
                )
            }
            _ => panic!("Cannot iterate over {}", self),
        }
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Sort::Bool => write!(f, "bool"),
            Sort::BitVector(n) => write!(f, "(bv {})", n),
            Sort::Int => write!(f, "int"),
            Sort::F32 => write!(f, "f32"),
            Sort::F64 => write!(f, "f64"),
            Sort::Field(i) => write!(f, "(mod {})", i),
            Sort::Array(k, v, n) => write!(f, "(array {} {} {})", k, v, n),
            Sort::Tuple(fields) => {
                write!(f, "(tuple")?;
                for field in fields {
                    write!(f, " {}", field)?;
                }
                write!(f, ")")
            }
        }
    }
}

/// A (perfectly shared) pointer to a term
pub type Term = HConsed<TermData>;
// "Temporary" terms.
/// A weak (perfectly shared) pointer to a term
pub type TTerm = WHConsed<TermData>;

struct TermTable {
    map: AHashMap<TermData, TTerm>,
    count: u64,
}

impl TermTable {
    fn get(&self, key: &TermData) -> Option<Term> {
        if let Some(old) = self.map.get(key) {
            old.to_hconsed()
        } else {
            None
        }
    }
    fn mk(&mut self, elm: TermData) -> Term {
        // If the element is known and upgradable return it.
        if let Some(hconsed) = self.get(&elm) {
            //debug_assert!(*hconsed.elm == elm);
            return hconsed;
        }
        // Otherwise build hconsed version.
        let hconsed = HConsed {
            elm: Arc::new(elm.clone()),
            uid: self.count,
        };
        // Increment uid count.
        self.count += 1;
        // ...add weak version to the table...
        self.map.insert(elm, hconsed.to_weak());
        // ...and return consed version.
        hconsed
    }
    fn collect(&mut self) {
        let old_size = self.map.len();
        let mut to_check: OnceQueue<Term> = OnceQueue::new();
        self.map.retain(|key, val| {
            if val.elm.upgrade().is_some() {
                true
            } else {
                to_check.extend(key.cs.iter().map(|i| i.clone()));
                false
            }
        });
        while let Some(t) = to_check.pop() {
            let data: TermData = (*t).clone();
            std::mem::drop(t);
            match self.map.entry(data) {
                std::collections::hash_map::Entry::Occupied(e) => {
                    if e.get().elm.upgrade().is_none() {
                        let (key, _val) = e.remove_entry();
                        to_check.extend(key.cs.iter().map(|i| i.clone()));
                    }
                }
                _ => {}
            }
        }
        let new_size = self.map.len();
        for (k, v) in self.map.iter() {
            assert!(v.elm.upgrade().is_some(), "Can not upgrade: {:?}", k)
        }
        debug!(target: "ir::term::gc", "{} of {} terms collected", old_size - new_size, old_size);
    }
}

lazy_static! {
    static ref TERMS: RwLock<TermTable> = RwLock::new(TermTable {
        map: AHashMap::new(),
        count: 0,
    });
}

fn mk(elm: TermData) -> Term {
    let mut slf = TERMS.write().unwrap();
    slf.mk(elm)
}

/// Scans the term database and the type database and removes dead terms.
pub fn garbage_collect() {
    collect_terms();
    collect_types();
}

fn collect_terms() {
    TERMS.write().unwrap().collect();
}
fn collect_types() {
    let mut ty_map = ty::TERM_TYPES.write().unwrap();
    let old_size = ty_map.len();
    ty_map.retain(|term, _| term.to_hconsed().is_some());
    let new_size = ty_map.len();
    debug!(target: "ir::term::gc", "{} of {} types collected", old_size - new_size, old_size);
}

impl TermData {
    /// Get the underlying boolean constant, if possible.
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Op::Const(Value::Bool(b)) = &self.op {
            Some(*b)
        } else {
            None
        }
    }
    /// Get the underlying bit-vector constant, if possible.
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Op::Const(Value::BitVector(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf_opt(&self) -> Option<&FieldElem> {
        if let Op::Const(Value::Field(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }
    /// Is this a variable?
    pub fn is_var(&self) -> bool {
        if let Op::Var(..) = &self.op {
            true
        } else {
            false
        }
    }
}

impl Value {
    /// Compute the sort of this value
    pub fn sort(&self) -> Sort {
        match &self {
            Value::Bool(_) => Sort::Bool,
            Value::Field(f) => Sort::Field(f.modulus().clone()),
            Value::Int(_) => Sort::Int,
            Value::F64(_) => Sort::F64,
            Value::F32(_) => Sort::F32,
            Value::BitVector(b) => Sort::BitVector(b.width()),
            Value::Array(s, _, _, _) => s.clone(),
            Value::Tuple(v) => Sort::Tuple(v.iter().map(Value::sort).collect()),
        }
    }
    #[track_caller]
    /// Get the underlying boolean constant, or panic!
    pub fn as_bool(&self) -> bool {
        if let Value::Bool(b) = self {
            *b
        } else {
            panic!("Not a bool: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying bit-vector constant, or panic!
    pub fn as_bv(&self) -> &BitVector {
        if let Value::BitVector(b) = self {
            b
        } else {
            panic!("Not a bit-vec: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf(&self) -> &FieldElem {
        if let Value::Field(b) = self {
            b
        } else {
            panic!("Not a field-elem: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying tuple's constituent values, if possible.
    pub fn as_tuple(&self) -> &Vec<Value> {
        if let Value::Tuple(b) = self {
            b
        } else {
            panic!("Not a tuple: {}", self)
        }
    }

    /// Get the underlying boolean constant, if possible.
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Value::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }
    /// Get the underlying bit-vector constant, if possible.
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Value::BitVector(b) = self {
            Some(b)
        } else {
            None
        }
    }
}

/// Evaluate the term `t`, using variable values in `h`.
pub fn eval(t: &Term, h: &AHashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::new();
    for c in PostOrderIter::new(t.clone()) {
        let v = match &c.op {
            Op::Var(n, _) => h.get(n).unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, h)).clone(),
            Op::Eq => Value::Bool(vs.get(&c.cs[0]).unwrap() == vs.get(&c.cs[1]).unwrap()),
            Op::Not => Value::Bool(!vs.get(&c.cs[0]).unwrap().as_bool()),
            Op::Implies => Value::Bool(
                !vs.get(&c.cs[0]).unwrap().as_bool() || vs.get(&c.cs[1]).unwrap().as_bool(),
            ),
            Op::BoolNaryOp(BoolNaryOp::Or) => {
                Value::Bool(c.cs.iter().any(|c| vs.get(c).unwrap().as_bool()))
            }
            Op::BoolNaryOp(BoolNaryOp::And) => {
                Value::Bool(c.cs.iter().all(|c| vs.get(c).unwrap().as_bool()))
            }
            Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
                c.cs.iter()
                    .map(|c| vs.get(c).unwrap().as_bool())
                    .fold(false, std::ops::BitXor::bitxor),
            ),
            Op::BvBit(i) => {
                Value::Bool(vs.get(&c.cs[0]).unwrap().as_bv().uint().get_bit(*i as u32))
            }
            Op::BoolMaj => {
                let c0 = vs.get(&c.cs[0]).unwrap().as_bool() as u8;
                let c1 = vs.get(&c.cs[1]).unwrap().as_bool() as u8;
                let c2 = vs.get(&c.cs[2]).unwrap().as_bool() as u8;
                Value::Bool(c0 + c1 + c2 > 1)
            }
            Op::BvConcat => Value::BitVector({
                let mut it = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
                let f = it.next().unwrap();
                it.fold(f, BitVector::concat)
            }),
            Op::BvExtract(h, l) => {
                Value::BitVector(vs.get(&c.cs[0]).unwrap().as_bv().clone().extract(*h, *l))
            }
            Op::Const(v) => v.clone(),
            Op::BvBinOp(o) => Value::BitVector({
                let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
                let b = vs.get(&c.cs[1]).unwrap().as_bv().clone();
                match o {
                    BvBinOp::Udiv => a / &b,
                    BvBinOp::Urem => a % &b,
                    BvBinOp::Sub => a - b,
                    BvBinOp::Ashr => a.ashr(&b),
                    BvBinOp::Lshr => a.lshr(&b),
                    BvBinOp::Shl => a << b,
                }
            }),
            Op::BvUnOp(o) => Value::BitVector({
                let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
                match o {
                    BvUnOp::Not => !a,
                    BvUnOp::Neg => -a,
                }
            }),
            Op::BvNaryOp(o) => Value::BitVector({
                let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_bv().clone());
                let f = xs.next().unwrap();
                xs.fold(
                    f,
                    match o {
                        BvNaryOp::Add => std::ops::Add::add,
                        BvNaryOp::Mul => std::ops::Mul::mul,
                        BvNaryOp::Xor => std::ops::BitXor::bitxor,
                        BvNaryOp::Or => std::ops::BitOr::bitor,
                        BvNaryOp::And => std::ops::BitAnd::bitand,
                    },
                )
            }),
            Op::BvSext(w) => Value::BitVector({
                let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
                let mask = ((Integer::from(1) << *w as u32) - 1)
                    * Integer::from(a.uint().get_bit(a.width() as u32 - 1));
                BitVector::new(a.uint() | (mask << a.width() as u32), a.width() + w)
            }),
            Op::PfToBv(w) => Value::BitVector({
                let a = vs.get(&c.cs[0]).unwrap().as_pf().clone();
                assert!(a.i() < &(Integer::from(1) << 1));
                BitVector::new(a.i().clone(), *w)
            }),
            Op::BvUext(w) => Value::BitVector({
                let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
                BitVector::new(a.uint().clone(), a.width() + w)
            }),
            Op::Ite => if vs.get(&c.cs[0]).unwrap().as_bool() {
                vs.get(&c.cs[1])
            } else {
                vs.get(&c.cs[2])
            }
            .unwrap()
            .clone(),
            Op::BvBinPred(o) => Value::Bool({
                let a = vs.get(&c.cs[0]).unwrap().as_bv();
                let b = vs.get(&c.cs[1]).unwrap().as_bv();
                match o {
                    BvBinPred::Sge => a.as_sint() >= b.as_sint(),
                    BvBinPred::Sgt => a.as_sint() > b.as_sint(),
                    BvBinPred::Sle => a.as_sint() <= b.as_sint(),
                    BvBinPred::Slt => a.as_sint() < b.as_sint(),
                    BvBinPred::Uge => a.uint() >= b.uint(),
                    BvBinPred::Ugt => a.uint() > b.uint(),
                    BvBinPred::Ule => a.uint() <= b.uint(),
                    BvBinPred::Ult => a.uint() < b.uint(),
                }
            }),
            Op::BoolToBv => Value::BitVector(BitVector::new(
                Integer::from(vs.get(&c.cs[0]).unwrap().as_bool()),
                1,
            )),
            Op::PfUnOp(o) => Value::Field({
                let a = vs.get(&c.cs[0]).unwrap().as_pf().clone();
                match o {
                    PfUnOp::Recip => a.recip(),
                    PfUnOp::Neg => -a,
                }
            }),
            Op::PfNaryOp(o) => Value::Field({
                let mut xs = c.cs.iter().map(|c| vs.get(c).unwrap().as_pf().clone());
                let f = xs.next().unwrap();
                xs.fold(
                    f,
                    match o {
                        PfNaryOp::Add => std::ops::Add::add,
                        PfNaryOp::Mul => std::ops::Mul::mul,
                    },
                )
            }),
            Op::Tuple => Value::Tuple(c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect()),
            Op::Field(i) => {
                let t = vs.get(&c.cs[0]).unwrap().as_tuple();
                assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
                t[*i].clone()
            }
            o => unimplemented!("eval: {:?}", o),
        };
        //println!("Eval {}\nAs   {}", c, v);
        vs.insert(c.clone(), v);
    }
    vs.get(t).unwrap().clone()
}

/// Make a term with no arguments, just an operator.
pub fn leaf_term(op: Op) -> Term {
    term(op, Vec::new())
}

/// Make a term with arguments.
pub fn term(op: Op, cs: Vec<Term>) -> Term {
    mk(TermData { op, cs })
}

/// Make a bit-vector constant term.
pub fn bv_lit<T>(uint: T, width: usize) -> Term
where
    Integer: From<T>,
{
    leaf_term(Op::Const(Value::BitVector(BitVector::new(
        uint.into(),
        width,
    ))))
}

#[macro_export]
/// Make a term.
///
/// Syntax: `term![OP; ARG0, ARG1, ... ]`. Note the semi-colon.
macro_rules! term {
    ($x:expr; $($y:expr),+) => {
        term($x, vec![$($y),+])
    };
}

/// Map from terms
pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;
/// Set of terms
pub type TermSet = hashconsing::coll::HConSet<Term>;

/// Iterator over descendents in child-first order.
pub struct PostOrderIter {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::new(),
        }
    }
}

impl std::iter::Iterator for PostOrderIter {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(&t) {
                self.stack.pop();
            } else if !children_pushed {
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs.iter().map(|c| (false, c.clone())));
            } else {
                break;
            }
        }
        self.stack.pop().map(|(_, t)| {
            self.visited.insert(t.clone());
            t
        })
    }
}

#[derive(Clone, Debug)]
/// An IR constraint system.
pub struct Constraints {
    /// The assertions.
    pub(super) assertions: Vec<Term>,
    /// The public inputs to the system.
    pub(super) public_inputs: AHashSet<String>,
    /// The values of variables in the system.
    pub(super) values: Option<AHashMap<String, Value>>,
}

impl std::default::Default for Constraints {
    fn default() -> Self {
        Self {
            assertions: Vec::new(),
            public_inputs: AHashSet::new(),
            values: None,
        }
    }
}

impl Constraints {
    /// Create a new variable, `name: s`, where `val_fn` can be called to get the concrete value,
    /// and `public` indicates whether this variable is public in the constraint system.
    pub fn new_var<F: FnOnce() -> Value>(
        &mut self,
        name: &str,
        s: Sort,
        val_fn: F,
        public: bool,
    ) -> Term {
        debug!("Var: {} (public: {})", name, public);
        if public {
            assert!(
                self.public_inputs.insert(name.to_owned()),
                "{} already a public input",
                name
            );
        }
        if let Some(vs) = self.values.as_mut() {
            let val = val_fn();
            debug!("  val = {}", val);
            if let Some(v) = vs.insert(name.to_owned(), val) {
                panic!("{} already had a value: {}", name, v);
            }
        }
        leaf_term(Op::Var(name.to_string(), s))
    }
    /// Create a new variable, `name` in the constraint system, and set it equal to `term`.
    /// `public` indicates whether this variable is public in the constraint system.
    pub fn assign(&mut self, name: &str, term: Term, public: bool) -> Term {
        let val = self.eval(&term);
        let sort = check(&term);
        let var = self.new_var(name, sort, || val.unwrap(), public);
        self.assert(term![Op::Eq; var.clone(), term]);
        var
    }
    /// Assert `s` in the system.
    pub fn assert(&mut self, s: Term) {
        assert!(check(&s) == Sort::Bool);
        debug!("Assert: {}", s);
        self.assertions.push(s);
    }
    /// If tracking values, evaluate `term`, and set the result to `name`.
    pub fn eval_and_save(&mut self, name: &str, term: &Term) {
        if let Some(vs) = self.values.as_mut() {
            let v = eval(term, vs);
            vs.insert(name.to_owned(), v);
        }
    }
    /// Evaluate `term`, if values are being tracked.
    pub fn eval(&self, term: &Term) -> Option<Value> {
        self.values.as_ref().map(|vs| eval(term, vs))
    }
    /// Create a new system, which tracks values iff `values`.
    pub fn new(values: bool) -> Self {
        Self {
            assertions: Vec::new(),
            public_inputs: AHashSet::new(),
            values: if values { Some(AHashMap::new()) } else { None },
        }
    }
    /// Make `s` a public input.
    pub fn publicize(&mut self, s: String) {
        self.public_inputs.insert(s);
    }
    /// Get the assertions in the system.
    pub fn assertions(&self) -> &Vec<Term> {
        &self.assertions
    }
    /// Consume this system, yielding its parts: (assertions, public inputs, values)
    pub fn consume(self) -> (Vec<Term>, AHashSet<String>, Option<AHashMap<String, Value>>) {
        (self.assertions, self.public_inputs, self.values)
    }
    /// Build a system from its parts: (assertions, public inputs, values)
    pub fn from_parts(
        assertions: Vec<Term>,
        public_inputs: AHashSet<String>,
        values: Option<AHashMap<String, Value>>,
    ) -> Self {
        Self {
            assertions,
            public_inputs,
            values,
        }
    }
    /// Get the term, (AND all assertions)
    pub fn assertions_as_term(&self) -> Term {
        term(Op::BoolNaryOp(BoolNaryOp::And), self.assertions.clone())
    }
    /// How many total (unique) terms are there?
    pub fn terms(&self) -> usize {
        let mut terms = AHashSet::<Term>::new();
        for a in &self.assertions {
            for s in PostOrderIter::new(a.clone()) {
                terms.insert(s);
            }
        }
        terms.len()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eq() {
        let v = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
        let u = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
        let w = leaf_term(Op::Var("b".to_owned(), Sort::Bool));
        assert_eq!(v, u);
        assert!(v != w);
        assert!(u != w);
    }

    mod type_ {
        use super::*;

        fn t() -> Term {
            let v = leaf_term(Op::Var("b".to_owned(), Sort::BitVector(4)));
            term![
                Op::BvBit(4);
                term![
                    Op::BvConcat;
                    v,
                    term![Op::BoolToBv; leaf_term(Op::Var("c".to_owned(), Sort::Bool))]
                ]
            ]
        }

        #[test]
        fn vars() {
            let v = leaf_term(Op::Var("a".to_owned(), Sort::Bool));
            assert_eq!(check(&v), Sort::Bool);
            let v = leaf_term(Op::Var("b".to_owned(), Sort::BitVector(4)));
            assert_eq!(check(&v), Sort::BitVector(4));
            let v = t();
            assert_eq!(check(&v), Sort::Bool);
        }

        #[test]
        fn traversal() {
            let tt = t();
            assert_eq!(
                vec![
                    Op::Var("c".to_owned(), Sort::Bool),
                    Op::BoolToBv,
                    Op::Var("b".to_owned(), Sort::BitVector(4)),
                    Op::BvConcat,
                    Op::BvBit(4),
                ],
                PostOrderIter::new(tt)
                    .map(|t| t.op.clone())
                    .collect::<Vec<_>>()
            );
        }
    }
}
