//! IR term definition
//!
//! Generally based on SMT-LIB, and its theories.
//!
//! The most important types and functions are:
//!
//!    * Term structure
//!       * [Term]: perfectly-shared terms. Think of them as shared pointers to
//!       * [Op]: an operator
//!    * Term types
//!       * [Sort]: the type of a term
//!       * [check]: get the type of a term
//!    * Term construction
//!       * [term!]: from an operator and a syntactic list of children
//!       * [leaf_term]: from an operator alone
//!       * [term()]: from an operator and vector of children
//!    * Term data-structures and algorithms
//!       * [TermMap], [TermSet]: maps from and sets of terms
//!       * [PostOrderIter]: an iterator over the descendents of a term. Children-first.
//!    * [Computation]: a collection of variables and assertions about them
//!    * [Value]: a variable-free (and evaluated) term
//!
use crate::cfg::cfg_or_default as cfg;

use circ_fields::{FieldT, FieldV};
pub use circ_hc::{Node, Table, Weak};
use circ_opt::FieldToBv;
use fxhash::{FxHashMap, FxHashSet};
use log::{debug, trace};
use rug::Integer;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::borrow::Borrow;
use std::cell::Cell;
use std::collections::BTreeMap;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

pub mod bv;
pub mod dist;
pub mod ext;
pub mod extras;
pub mod fmt;
pub mod lin;
pub mod precomp;
pub mod serde_mods;
pub mod text;
pub mod ty;

pub use bv::BitVector;
pub use ext::ExtOp;
pub use ty::{check, check_rec, TypeError, TypeErrorReason};

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
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
    FpUnPred(FpUnPred),
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
    /// Unsigned bit-vector to prime-field
    ///
    /// Takes the modulus.
    UbvToPf(FieldT),
    /// A random value, sampled uniformly and independently of its arguments.
    ///
    /// Takes a name (if deterministically sampled, challenges of different names are sampled
    /// differentely) and a field to sample from.
    ///
    /// In IR evaluation, we sample deterministically based on a hash of the name.
    PfChallenge(String, FieldT),
    /// Requires the input pf element to fit in this many (unsigned) bits.
    PfFitsInBits(usize),
    /// Prime-field division
    PfDiv,

    /// Integer n-ary operator
    IntNaryOp(IntNaryOp),
    /// Integer comparison operator
    IntBinPred(IntBinPred),

    /// Binary operator, with arguments (array, index).
    ///
    /// Gets the value at index in array.
    Select,
    /// Ternary operator, with arguments (array, index, value).
    ///
    /// Makes an array equal to `array`, but with `value` at `index`.
    Store,
    /// Quad-operator, with arguments (array, index, value, cond).
    ///
    /// If `cond`, outputs an array equal to `array`, but with `value` at `index`.
    /// Otherwise, oupputs `array`.
    CStore,
    /// Makes an array of the indicated key sort with the indicated size, filled with the argument.
    Fill(Sort, usize),
    /// Create an array from (contiguous) values.
    Array(Sort, Sort),

    /// Assemble n things into a tuple
    Tuple,
    /// Get the n'th element of a tuple
    Field(usize),
    /// Update (tuple, element)
    Update(usize),

    /// Map (operation)
    Map(Box<Op>),

    /// Call a function (name, argument sorts, return sort)
    Call(String, Vec<Sort>, Sort),

    /// Cyclic right rotation of an array
    /// i.e. (Rot(1) [1,2,3,4]) --> ([4,1,2,3])
    Rot(usize),

    /// Assume that the field element is 0 or 1, and treat it as a boolean.
    PfToBoolTrusted,

    /// Extension operators. Used in compilation, but not externally supported
    ExtOp(ext::ExtOp),
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
/// prime-field division
pub const PF_DIV: Op = Op::PfDiv;
/// prime-field addition
pub const PF_ADD: Op = Op::PfNaryOp(PfNaryOp::Add);
/// prime-field multiplication
pub const PF_MUL: Op = Op::PfNaryOp(PfNaryOp::Mul);
/// integer addition
pub const INT_ADD: Op = Op::IntNaryOp(IntNaryOp::Add);
/// integer multiplication
pub const INT_MUL: Op = Op::IntNaryOp(IntNaryOp::Mul);
/// integer less than
pub const INT_LT: Op = Op::IntBinPred(IntBinPred::Lt);
/// integer less than or equal
pub const INT_LE: Op = Op::IntBinPred(IntBinPred::Le);
/// integer greater than
pub const INT_GT: Op = Op::IntBinPred(IntBinPred::Gt);
/// integer greater than or equal
pub const INT_GE: Op = Op::IntBinPred(IntBinPred::Ge);

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
            Op::PfDiv => Some(2),
            Op::PfNaryOp(_) => None,
            Op::PfChallenge(_, _) => None,
            Op::PfFitsInBits(..) => Some(1),
            Op::IntNaryOp(_) => None,
            Op::IntBinPred(_) => Some(2),
            Op::UbvToPf(_) => Some(1),
            Op::Select => Some(2),
            Op::Store => Some(3),
            Op::CStore => Some(4),
            Op::Fill(..) => Some(1),
            Op::Array(..) => None,
            Op::Tuple => None,
            Op::Field(_) => Some(1),
            Op::Update(_) => Some(2),
            Op::Map(op) => op.arity(),
            Op::Call(_, args, _) => Some(args.len()),
            Op::Rot(_) => Some(1),
            Op::ExtOp(o) => o.arity(),
            Op::PfToBoolTrusted => Some(1),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            BoolNaryOp::And => write!(f, "and"),
            BoolNaryOp::Or => write!(f, "or"),
            BoolNaryOp::Xor => write!(f, "xor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
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

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
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

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            BvNaryOp::Add => write!(f, "bvadd"),
            BvNaryOp::Mul => write!(f, "bvmul"),
            BvNaryOp::Or => write!(f, "bvor"),
            BvNaryOp::And => write!(f, "bvand"),
            BvNaryOp::Xor => write!(f, "bvxor"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
/// Bit-vector unary operator
pub enum BvUnOp {
    /// Bit-vector bitwise not
    Not,
    /// Bit-vector two's complement negation
    Neg,
}

impl Display for BvUnOp {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            BvUnOp::Not => write!(f, "bvnot"),
            BvUnOp::Neg => write!(f, "bvneg"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
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

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            FpUnOp::Neg => write!(f, "fpneg"),
            FpUnOp::Abs => write!(f, "fpabs"),
            FpUnOp::Sqrt => write!(f, "fpsqrt"),
            FpUnOp::Round => write!(f, "fpround"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            FpBinPred::Le => write!(f, "fple"),
            FpBinPred::Lt => write!(f, "fplt"),
            FpBinPred::Eq => write!(f, "fpeq"),
            FpBinPred::Ge => write!(f, "fpge"),
            FpBinPred::Gt => write!(f, "fpgt"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
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
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
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

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
/// Finite field n-ary operator
pub enum PfNaryOp {
    /// Finite field (+)
    Add,
    /// Finite field (*)
    Mul,
}

impl Display for PfNaryOp {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            PfNaryOp::Add => write!(f, "+"),
            PfNaryOp::Mul => write!(f, "*"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
/// Finite field n-ary operator
pub enum PfUnOp {
    /// Finite field negation
    Neg,
    /// Finite field reciprocal
    Recip,
}

impl Display for PfUnOp {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            PfUnOp::Neg => write!(f, "-"),
            PfUnOp::Recip => write!(f, "pfrecip"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
/// Integer n-ary operator
pub enum IntNaryOp {
    /// Finite field (+)
    Add,
    /// Finite field (*)
    Mul,
}

impl Display for IntNaryOp {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            IntNaryOp::Add => write!(f, "intadd"),
            IntNaryOp::Mul => write!(f, "intmul"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Copy, Serialize, Deserialize)]
/// Integer binary predicate. See [Op::Eq] for equality.
pub enum IntBinPred {
    /// Integer (<)
    Lt,
    /// Integer (>)
    Gt,
    /// Integer (<=)
    Le,
    /// Integer (>=)
    Ge,
}

impl Display for IntBinPred {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            IntBinPred::Lt => write!(f, "<"),
            IntBinPred::Gt => write!(f, ">"),
            IntBinPred::Le => write!(f, "<="),
            IntBinPred::Ge => write!(f, ">="),
        }
    }
}

impl Serialize for Term {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let linearized = lin::LinTerm::from(self);
        linearized.serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for Term {
    fn deserialize<D>(deserializer: D) -> Result<Term, D::Error>
    where
        D: Deserializer<'de>,
    {
        let linearized = lin::LinTerm::deserialize(deserializer)?;
        Ok(Term::from(linearized))
    }
}

#[derive(Clone, PartialEq, PartialOrd, Serialize, Deserialize)]
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
    Field(FieldV),
    /// Boolean
    Bool(bool),
    /// Array
    Array(Array),
    /// Tuple
    Tuple(Box<[Value]>),
}

#[derive(Clone, PartialEq, Eq, Debug, PartialOrd, Hash, Serialize, Deserialize)]
/// An IR array value.
///
/// A sized, space array.
pub struct Array {
    /// Key sort
    pub key_sort: Sort,
    /// Default (fill) value. What is stored when a key is missing from the next member
    pub default: Box<Value>,
    /// Key-> Value map
    pub map: BTreeMap<Value, Value>,
    /// Size of array. There are this many valid keys.
    pub size: usize,
}

impl Array {
    /// Create a new [Array] from components
    pub fn new(
        key_sort: Sort,
        default: Box<Value>,
        map: BTreeMap<Value, Value>,
        size: usize,
    ) -> Self {
        if key_sort.default_value().as_usize().is_none() {
            panic!(
                "IR Arrays cannot have {} index (Int, BitVector, Bool, or Field only)",
                key_sort
            );
        }
        Self {
            key_sort,
            default,
            map,
            size,
        }
    }
    /// Create a new, default-initialized [Array]
    pub fn default(key_sort: Sort, val_sort: &Sort, size: usize) -> Self {
        Self::new(
            key_sort,
            Box::new(val_sort.default_value()),
            Default::default(),
            size,
        )
    }
    /// Create a new array from a vector
    pub fn from_vec(key_sort: Sort, value_sort: Sort, items: Vec<Value>) -> Self {
        assert!(!items.is_empty());
        let default = value_sort.default_value();
        let size = items.len();
        let map = key_sort.elems_iter_values().zip(items).collect();
        Self::new(key_sort, Box::new(default), map, size)
    }

    // consistency check for index
    fn check_idx(&self, idx: &Value) {
        if idx.sort() != self.key_sort {
            panic!(
                "Tried to index array with key {}, but {} was expected",
                idx.sort(),
                self.key_sort
            );
        }
        match idx.as_usize() {
            Some(idx_u) if idx_u < self.size => (),
            Some(idx_u) => panic!(
                "IR Array out of range: accessed {}, size is {}",
                idx_u, self.size
            ),
            _ => panic!("IR Array index {} not convertible to usize", idx),
        }
    }

    // consistency check for value
    fn check_val(&self, vsrt: Sort) {
        if vsrt != self.default.sort() {
            panic!(
                "Attempted to store {} to an array of {}",
                vsrt,
                self.default.sort()
            );
        }
    }

    /// Store
    pub fn store(mut self, idx: Value, val: Value) -> Self {
        self.check_idx(&idx);
        self.check_val(val.sort());
        self.map.insert(idx, val);
        self
    }

    /// Select
    pub fn select(&self, idx: &Value) -> Value {
        self.check_idx(idx);
        self.map.get(idx).unwrap_or(&*self.default).clone()
    }

    /// All values
    pub fn values(&self) -> Vec<Value> {
        self.key_sort
            .elems_iter_values()
            .take(self.size)
            .map(|i| self.select(&i))
            .collect()
    }
}

impl std::cmp::Eq for Value {}
// We walk in danger here, intentionally. One day we may fix it.
// FP is the heart of the problem.
#[allow(clippy::derive_ord_xor_partial_ord)]
impl std::cmp::Ord for Value {
    fn cmp(&self, o: &Self) -> std::cmp::Ordering {
        self.partial_cmp(o).expect("broken Value cmp")
    }
}
// We walk in danger here, intentionally. One day we may fix it.
// FP is the heart of the problem.
#[allow(clippy::derived_hash_with_manual_eq)]
impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Value::BitVector(bv) => bv.hash(state),
            Value::F32(bv) => bv.to_bits().hash(state),
            Value::F64(bv) => bv.to_bits().hash(state),
            Value::Int(bv) => bv.hash(state),
            Value::Field(bv) => bv.hash(state),
            Value::Bool(bv) => bv.hash(state),
            Value::Array(a) => a.hash(state),
            Value::Tuple(s) => {
                s.hash(state);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
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
    /// prime field, integers mod FieldT.modulus()
    Field(FieldT),
    /// boolean
    Bool,
    /// Array from one sort to another, of fixed size.
    ///
    /// size presumes an order, and a zero, for the key sort.
    Array(Box<Sort>, Box<Sort>, usize),
    /// A tuple
    Tuple(Box<[Sort]>),
}

impl Default for Sort {
    fn default() -> Self {
        Self::Bool
    }
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
    pub fn as_pf(&self) -> &FieldT {
        if let Sort::Field(fty) = self {
            fty
        } else {
            panic!("{} is not a field", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent sorts of this tuple, panicking otherwise.
    pub fn as_tuple(&self) -> &[Sort] {
        if let Sort::Tuple(w) = self {
            w
        } else {
            panic!("{} is not a tuple", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent sorts of this array, panicking otherwise.
    pub fn as_array(&self) -> (&Sort, &Sort, usize) {
        if let Sort::Array(k, v, s) = self {
            (k, v, *s)
        } else {
            panic!("{} is not an array", self)
        }
    }

    /// Is this an array?
    pub fn is_array(&self) -> bool {
        matches!(self, Sort::Array(..))
    }

    /// The nth element of this sort.
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn nth_elem(&self, n: usize) -> Term {
        match self {
            Sort::Bool => {
                assert!(n < 2);
                bool_lit([false, true][n])
            }
            Sort::BitVector(w) => {
                assert!(n < (1 << w));
                bv_lit(n, *w)
            }
            Sort::Field(f) => {
                debug_assert!(&Integer::from(n) < f.modulus());
                pf_lit(f.new_v(n))
            }
            _ => panic!("Can't get nth element of sort {}", self),
        }
    }

    /// An iterator over the elements of this sort (as IR Terms).
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn elems_iter(&self) -> Box<dyn Iterator<Item = Term>> {
        Box::new(self.elems_iter_values().map(|v| leaf_term(Op::Const(v))))
    }

    /// An iterator over the elements of this sort (as IR values).
    /// Only defined for booleans, bit-vectors, and field elements.
    #[track_caller]
    pub fn elems_iter_values(&self) -> Box<dyn Iterator<Item = Value>> {
        match self {
            Sort::Bool => Box::new([false, true].iter().map(|b| Value::Bool(*b))),
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
                    .map(move |i| Value::BitVector(BitVector::new(i, w))),
                )
            }
            Sort::Field(fty) => {
                let m = fty.modulus_arc();
                let fty = fty.clone();
                Box::new(
                    std::iter::successors(Some(Integer::from(0)), move |p| {
                        let q = p.clone() + 1;
                        if q < *m {
                            Some(q)
                        } else {
                            None
                        }
                    })
                    .map(move |i| Value::Field(fty.new_v(i))),
                )
            }
            _ => panic!("Cannot iterate over {}", self),
        }
    }

    /// Compute the default term for this sort.
    ///
    /// * booleans: false
    /// * bit-vectors: zero
    /// * field elements: zero
    /// * floats: zero
    /// * tuples/arrays: recursively default
    pub fn default_term(&self) -> Term {
        leaf_term(Op::Const(self.default_value()))
    }

    /// Compute the default value for this sort.
    ///
    /// * booleans: false
    /// * bit-vectors: zero
    /// * field elements: zero
    /// * floats: zero
    /// * tuples/arrays: recursively default
    pub fn default_value(&self) -> Value {
        match self {
            Sort::Bool => Value::Bool(false),
            Sort::BitVector(w) => Value::BitVector(BitVector::new(0.into(), *w)),
            Sort::Field(fty) => Value::Field(fty.default_value()),
            Sort::Int => Value::Int(0.into()),
            Sort::F32 => Value::F32(0.0f32),
            Sort::F64 => Value::F64(0.0),
            Sort::Tuple(t) => Value::Tuple(t.iter().map(Sort::default_value).collect()),
            Sort::Array(k, v, n) => Value::Array(Array::default((**k).clone(), v, *n)),
        }
    }

    /// Is this a scalar?
    pub fn is_scalar(&self) -> bool {
        !matches!(self, Sort::Tuple(..) | Sort::Array(..))
    }
}

mod hc {
    use circ_hc::generate_hashcons_rc;

    generate_hashcons_rc!(super::Op);
}

/// A (perfectly shared) pointer to a term
pub type Term = hc::Node;
// "Temporary" terms.
/// A weak (perfectly shared) pointer to a term
pub type TTerm = hc::Weak;

type TypeTable = circ_hc::collections::cache::NodeCache<Op, hc::Table, Sort>;

/// Scans the term database and the type database and removes dead terms and types.
pub fn garbage_collect() {
    // Don't garbage collect while panicking.
    // this function may be called from Drop implementations, which are called
    // when a thread is unwinding due to a panic. When that happens, RwLocks are
    // poisoned, which would cause a panic-in-panic, no bueno.
    if std::thread::panicking() {
        log::warn!("Not garbage collecting because we are currently panicking.");
        return;
    }

    // lock the collector before locking anything else
    collect_terms();
    collect_types();
    super::opt::cfold::collect();
}

thread_local! {
    static LAST_LEN: Cell<usize> = Default::default();
}

fn should_collect() -> bool {
    let last_len = LAST_LEN.with(|l| l.get());
    let ret = LEN_THRESH_DEN * hc::Table::table_size() > LEN_THRESH_NUM * last_len;
    if last_len > TERM_CACHE_LIMIT {
        // when last_len is big, force a garbage collect every once in a while
        LAST_LEN.with(|l| l.set((last_len * LEN_DECAY_NUM) / LEN_DECAY_DEN));
    }
    ret
}

const LEN_THRESH_NUM: usize = 8;
const LEN_THRESH_DEN: usize = 1;
const LEN_DECAY_NUM: usize = 15;
const LEN_DECAY_DEN: usize = 16;
/// Scan term and type databases only if they've grown in size since last scan
pub fn maybe_garbage_collect() -> bool {
    // Don't garbage collect while panicking.
    // NOTE This function probably shouldn't be called from Drop impls, but let's be safe anyway.
    if std::thread::panicking() {
        log::warn!("Not garbage collecting because we are currently panicking.");
        return false;
    }

    if should_collect() {
        collect_terms();
        collect_types();
        super::opt::cfold::collect();
        true
    } else {
        false
    }
}

fn collect_terms() {
    hc::Table::gc();
}

fn collect_types() {
    ty::TERM_TYPES.with(|tys| tys.borrow_mut().collect());
}

impl Term {
    /// Get the underlying boolean constant, if possible.
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Op::Const(Value::Bool(b)) = &self.op() {
            Some(*b)
        } else {
            None
        }
    }
    /// Get the underlying bit-vector constant, if possible.
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Op::Const(Value::BitVector(b)) = &self.op() {
            Some(b)
        } else {
            None
        }
    }
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf_opt(&self) -> Option<&FieldV> {
        if let Op::Const(Value::Field(b)) = &self.op() {
            Some(b)
        } else {
            None
        }
    }

    /// Get the underlying tuple constant, if possible.
    pub fn as_tuple_opt(&self) -> Option<&[Value]> {
        if let Op::Const(Value::Tuple(t)) = &self.op() {
            Some(t)
        } else {
            None
        }
    }

    /// Get the underlying array constant, if possible.
    pub fn as_array_opt(&self) -> Option<&Array> {
        if let Op::Const(Value::Array(a)) = &self.op() {
            Some(a)
        } else {
            None
        }
    }

    /// Get the underlying constant value, if possible.
    pub fn as_value_opt(&self) -> Option<&Value> {
        if let Op::Const(v) = &self.op() {
            Some(v)
        } else {
            None
        }
    }

    /// Is this a variable?
    pub fn is_var(&self) -> bool {
        matches!(&self.op(), Op::Var(..))
    }

    /// Is this a value
    pub fn is_const(&self) -> bool {
        matches!(&self.op(), Op::Const(..))
    }

    /// Get the variable name; panic if not a variable.
    #[track_caller]
    pub fn as_var_name(&self) -> &str {
        if let Op::Var(n, _) = &self.op() {
            n
        } else {
            panic!("not a variable")
        }
    }
}

impl Value {
    /// Compute the sort of this value
    pub fn sort(&self) -> Sort {
        match &self {
            Value::Bool(_) => Sort::Bool,
            Value::Field(f) => Sort::Field(f.ty()),
            Value::Int(_) => Sort::Int,
            Value::F64(_) => Sort::F64,
            Value::F32(_) => Sort::F32,
            Value::BitVector(b) => Sort::BitVector(b.width()),
            Value::Array(Array {
                key_sort,
                default,
                size,
                ..
            }) => Sort::Array(Box::new(key_sort.clone()), Box::new(default.sort()), *size),
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
    /// Get the underlying integer constant, or panic!
    pub fn as_int(&self) -> &Integer {
        if let Value::Int(b) = self {
            b
        } else {
            panic!("Not an int: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying prime field constant, if possible.
    pub fn as_pf(&self) -> &FieldV {
        if let Value::Field(b) = self {
            b
        } else {
            panic!("Not a field-elem: {}", self)
        }
    }
    #[track_caller]
    /// Get the underlying tuple's constituent values, if possible.
    pub fn as_tuple(&self) -> &[Value] {
        if let Value::Tuple(b) = self {
            b
        } else {
            panic!("Not a tuple: {}", self)
        }
    }

    #[track_caller]
    /// Unwrap the constituent value of this array, panicking otherwise.
    pub fn as_array(&self) -> &Array {
        if let Value::Array(w) = self {
            w
        } else {
            panic!("{} is not an aray", self)
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

    /// Convert this value into a usize if possible
    pub fn as_usize(&self) -> Option<usize> {
        match &self {
            Value::Bool(b) => Some(*b as usize),
            Value::Field(f) => f.i().to_usize(),
            Value::Int(i) => i.to_usize(),
            Value::BitVector(b) => b.uint().to_usize(),
            _ => None,
        }
    }
}

/// Recursively the term `t`, using variable values in `h` and storing intermediate evaluations in
/// the cache `vs`.
pub fn eval_cached<'a>(
    t: &Term,
    h: &FxHashMap<String, Value>,
    vs: &'a mut TermMap<Value>,
) -> &'a Value {
    // the custom traversal (rather than [PostOrderIter]) allows us to break early based on the cache

    // (children pushed, term)
    let mut stack = vec![(false, t.clone())];
    while let Some((children_pushed, node)) = stack.pop() {
        if vs.contains_key(&node) {
            continue;
        }
        if children_pushed {
            eval_value(vs, h, node);
        } else {
            stack.push((true, node.clone()));
            for c in node.cs() {
                // vs doubles as our visited set.
                if !vs.contains_key(c) {
                    stack.push((false, c.clone()));
                }
            }
        }
    }
    vs.get(t).unwrap()
}

/// Recursively evaluate the term `t`, using variable values in `h`.
pub fn eval(t: &Term, h: &FxHashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::default();
    eval_cached(t, h, &mut vs).clone()
}

/// Helper function for eval function. Handles a single term
fn eval_value(vs: &mut TermMap<Value>, h: &FxHashMap<String, Value>, t: Term) -> Value {
    let args: Vec<&Value> = t.cs().iter().map(|c| vs.get(c).unwrap()).collect();
    trace!("Eval {} on {:?}", t.op(), args);
    let v = eval_op(t.op(), &args, h);
    trace!("=> {}", v);
    if let Value::Bool(false) = &v {
        trace!("term {}", t);
        for v in extras::free_variables(t.clone()) {
            trace!("  {} = {}", v, h.get(&v).unwrap());
        }
    }
    vs.insert(t, v.clone());
    v
}

/// Helper function for eval function. Handles a single op
#[allow(clippy::uninlined_format_args)]
pub fn eval_op(op: &Op, args: &[&Value], var_vals: &FxHashMap<String, Value>) -> Value {
    match op {
        Op::Var(n, _) => var_vals
            .get(n)
            .unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, var_vals))
            .clone(),
        Op::Eq => Value::Bool(args[0] == args[1]),
        Op::Not => Value::Bool(!args[0].as_bool()),
        Op::Implies => Value::Bool(!args[0].as_bool() || args[1].as_bool()),
        Op::BoolNaryOp(BoolNaryOp::Or) => Value::Bool(args.iter().any(|a| a.as_bool())),
        Op::BoolNaryOp(BoolNaryOp::And) => Value::Bool(args.iter().all(|a| a.as_bool())),
        Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
            args.iter()
                .map(|a| a.as_bool())
                .fold(false, std::ops::BitXor::bitxor),
        ),
        Op::BvBit(i) => Value::Bool(args[0].as_bv().uint().get_bit(*i as u32)),
        Op::BoolMaj => {
            let c0 = args[0].as_bool() as u8;
            let c1 = args[1].as_bool() as u8;
            let c2 = args[2].as_bool() as u8;
            Value::Bool(c0 + c1 + c2 > 1)
        }
        Op::BvConcat => Value::BitVector({
            let mut it = args.iter().map(|a| a.as_bv().clone());
            let f = it.next().unwrap();
            it.fold(f, BitVector::concat)
        }),
        Op::BvExtract(h, l) => Value::BitVector(args[0].as_bv().clone().extract(*h, *l)),
        Op::Const(v) => v.clone(),
        Op::BvBinOp(o) => Value::BitVector({
            let a = args[0].as_bv().clone();
            let b = args[1].as_bv().clone();
            match o {
                BvBinOp::Udiv => a / &b,
                BvBinOp::Urem => a % &b,
                BvBinOp::Sub => a - b,
                BvBinOp::Ashr => a.ashr(&b),
                BvBinOp::Lshr => a.lshr(&b),
                BvBinOp::Shl => a << &b,
            }
        }),
        Op::BvUnOp(o) => Value::BitVector({
            let a = args[0].as_bv().clone();
            match o {
                BvUnOp::Not => !a,
                BvUnOp::Neg => -a,
            }
        }),
        Op::BvNaryOp(o) => Value::BitVector({
            let mut xs = args.iter().map(|a| a.as_bv().clone());
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
            let a = args[0].as_bv().clone();
            let mask = ((Integer::from(1) << *w as u32) - 1)
                * Integer::from(a.uint().get_bit(a.width() as u32 - 1));
            BitVector::new(a.uint() | (mask << a.width() as u32), a.width() + w)
        }),
        Op::PfToBv(w) => Value::BitVector({
            let i = args[0].as_pf().i();
            if let FieldToBv::Panic = cfg().ir.field_to_bv {
                assert!(
                    (i.significant_bits() as usize) <= *w,
                    "{}",
                    "oversized input to Op::PfToBv({w})",
                );
            }
            BitVector::new(i % (Integer::from(1) << *w), *w)
        }),
        Op::BvUext(w) => Value::BitVector({
            let a = args[0].as_bv().clone();
            BitVector::new(a.uint().clone(), a.width() + w)
        }),
        Op::Ite => args[if args[0].as_bool() { 1 } else { 2 }].clone(),
        Op::BvBinPred(o) => Value::Bool({
            let a = args[0].as_bv();
            let b = args[1].as_bv();
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
        Op::BoolToBv => Value::BitVector(BitVector::new(Integer::from(args[0].as_bool()), 1)),
        Op::PfUnOp(o) => Value::Field({
            let a = args[0].as_pf().clone();
            match o {
                PfUnOp::Recip => {
                    if a.is_zero() {
                        a.ty().zero()
                    } else {
                        a.recip()
                    }
                }
                PfUnOp::Neg => -a,
            }
        }),
        Op::PfDiv => Value::Field({
            let a = args[0].as_pf().clone();
            let b = args[1].as_pf().clone();
            a * b.recip()
        }),
        Op::PfNaryOp(o) => Value::Field({
            let mut xs = args.iter().map(|a| a.as_pf().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    PfNaryOp::Add => std::ops::Add::add,
                    PfNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::IntBinPred(o) => Value::Bool({
            let a = args[0].as_int();
            let b = args[1].as_int();
            match o {
                IntBinPred::Ge => a >= b,
                IntBinPred::Gt => a > b,
                IntBinPred::Le => a <= b,
                IntBinPred::Lt => a < b,
            }
        }),
        Op::IntNaryOp(o) => Value::Int({
            let mut xs = args.iter().map(|a| a.as_int().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    IntNaryOp::Add => std::ops::Add::add,
                    IntNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::UbvToPf(fty) => Value::Field(fty.new_v(args[0].as_bv().uint())),
        Op::PfChallenge(name, field) => Value::Field(pf_challenge(name, field)),
        Op::PfFitsInBits(n_bits) => {
            Value::Bool(args[0].as_pf().i().signed_bits() <= *n_bits as u32)
        }
        // tuple
        Op::Tuple => Value::Tuple(args.iter().map(|a| (*a).clone()).collect()),
        Op::Field(i) => {
            let t = args[0].as_tuple();
            assert!(i < &t.len(), "{} out of bounds for {} on {:?}", i, op, args);
            t[*i].clone()
        }
        Op::Update(i) => {
            let mut t = Vec::from(args[0].as_tuple()).into_boxed_slice();
            assert!(i < &t.len(), "{} out of bounds for {} on {:?}", i, op, args);
            let e = args[1].clone();
            assert_eq!(t[*i].sort(), e.sort());
            t[*i] = e;
            Value::Tuple(t)
        }
        // array
        Op::Store => {
            let a = args[0].as_array().clone();
            let i = args[1].clone();
            let v = args[2].clone();
            Value::Array(a.store(i, v))
        }
        Op::CStore => {
            let a = args[0].as_array().clone();
            let i = args[1].clone();
            let v = args[2].clone();
            let c = args[3].as_bool();
            if c {
                Value::Array(a.store(i, v))
            } else {
                Value::Array(a)
            }
        }
        Op::Fill(key_sort, size) => {
            let v = args[0].clone();
            Value::Array(Array::new(
                key_sort.clone(),
                Box::new(v),
                Default::default(),
                *size,
            ))
        }
        Op::Array(key, value) => Value::Array(Array::from_vec(
            key.clone(),
            value.clone(),
            args.iter().cloned().cloned().collect(),
        )),
        Op::Select => {
            let a = args[0].as_array();
            let i = args[1];
            a.select(i)
        }
        Op::Map(inner_op) => {
            //  term_vecs[i] will store a vector of all the i-th index entries of the array arguments
            let mut arg_vecs: Vec<Vec<Value>> = vec![Vec::new(); args[0].as_array().size];

            for arg in args {
                let arr = arg.as_array().clone();
                let iter = match arg.sort() {
                    Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                    _ => panic!("Input type should be Array"),
                };
                for (j, jval) in iter {
                    arg_vecs[j].push(arr.select(&jval))
                }
            }
            let term = term(
                op.clone(),
                args.iter()
                    .map(|a| leaf_term(Op::Const((*a).clone())))
                    .collect(),
            );
            let (mut res, iter) = match check(&term) {
                Sort::Array(k, v, n) => (
                    Array::default((*k).clone(), &v, n),
                    (*k).clone().elems_iter_values().take(n).enumerate(),
                ),
                _ => panic!("Output type of map should be array"),
            };

            for (i, idxval) in iter {
                let args: Vec<&Value> = arg_vecs[i].iter().collect();
                let val = eval_op(inner_op, &args, var_vals);
                res.map.insert(idxval, val);
            }
            Value::Array(res)
        }
        Op::Rot(i) => {
            let a = args[0].as_array().clone();
            let (mut res, iter, len) = match args[0].sort() {
                Sort::Array(k, v, n) => (
                    Array::default((*k).clone(), &v, n),
                    (*k).clone().elems_iter_values().take(n).enumerate(),
                    n,
                ),
                _ => panic!("Input type should be Array"),
            };

            // calculate new rotation amount
            let rot = *i % len;
            for (idx, idx_val) in iter {
                let w = idx_val.as_bv().width();
                let new_idx = Value::BitVector(BitVector::new(Integer::from((idx + rot) % len), w));
                let new_val = a.select(&idx_val);
                res.map.insert(new_idx, new_val);
            }
            Value::Array(res)
        }
        Op::PfToBoolTrusted => {
            let v = args[0].as_pf().i();
            assert!(v == 0 || v == 1);
            Value::Bool(v == 1)
        }
        Op::ExtOp(o) => o.eval(args),

        o => unimplemented!("eval: {:?}", o),
    }
}

/// Make an array from a sequence of terms.
///
/// Requires
///
/// * a key sort, as all arrays do. This sort must be iterable (i.e., bool, int, bit-vector, or field).
/// * a value sort, for the array's default
pub fn make_array(key_sort: Sort, value_sort: Sort, i: Vec<Term>) -> Term {
    term(Op::Array(key_sort, value_sort), i)
}

/// Make a sequence of terms from an array.
///
/// Requires
///
/// * an array term
pub fn unmake_array(a: Term) -> Vec<Term> {
    let sort = check(&a);
    let (key_sort, _, size) = sort.as_array();
    key_sort
        .elems_iter()
        .take(size)
        .map(|idx| term(Op::Select, vec![a.clone(), idx]))
        .collect()
}

/// Make a term with no arguments, just an operator.
pub fn leaf_term(op: Op) -> Term {
    term(op, Vec::new())
}

/// Make a term with arguments.
#[track_caller]
pub fn term(op: Op, cs: Vec<Term>) -> Term {
    #[cfg_attr(not(debug_assertions), allow(clippy::let_and_return))]
    let t = hc::Table::create(&op, cs);
    #[cfg(debug_assertions)]
    check_rec(&t);
    t
}

/// Make a prime-field constant term.
pub fn pf_lit(elem: FieldV) -> Term {
    leaf_term(Op::Const(Value::Field(elem)))
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

/// Make a bit-vector constant term.
pub fn bool_lit(b: bool) -> Term {
    leaf_term(Op::Const(Value::Bool(b)))
}

#[macro_export]
/// Make a term.
///
/// Syntax:
///
///    * without children: `term![OP]`
///    * with children: `term![OP; ARG0, ARG1, ... ]`
///       * Note the semi-colon
macro_rules! term {
    ($x:expr) => {
        leaf_term($x)
    };
    ($x:expr; $($y:expr),+) => {
        term($x, vec![$($y),+])
    };
}

#[macro_export]
/// Make a term, with clones.
///
/// Syntax:
///
///    * without children: `term![OP]`
///    * with children: `term![OP; ARG0, ARG1, ... ]`
///       * Note the semi-colon
macro_rules! term_c {
    ($x:expr; $($y:expr),+) => {
        {
            let mut args = Vec::new();
            #[allow(clippy::vec_init_then_push)]
            {
                $(
                    args.push(($y).clone());
                )+
            }
            term($x, args)
        }
    };
}

/// Map from terms
pub type TermMap<T> = FxHashMap<Term, T>;
/// LRU cache of terms (like TermMap, but limited size)
pub type TermCache<T> = circ_hc::collections::lru::NodeLruCache<Op, hc::Table, T>;
/// Set of terms
pub type TermSet = FxHashSet<Term>;

// default LRU cache size
// this size avoids quadratic behavior for Falcon verification
pub(super) const TERM_CACHE_LIMIT: usize = 65536;

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
            visited: TermSet::default(),
        }
    }
    /// Make an iterator over the descendents of `roots`, stopping at `skips`.
    pub fn from_roots_and_skips(roots: impl IntoIterator<Item = Term>, skips: TermSet) -> Self {
        Self {
            stack: roots
                .into_iter()
                .filter(|t| !skips.contains(t))
                .map(|t| (false, t))
                .collect(),
            visited: skips,
        }
    }
}

impl std::iter::Iterator for PostOrderIter {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs().iter().map(|c| (false, c.clone())));
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

/// A party identifier
pub type PartyId = u8;

/// Which round the variable is given in.
///
/// (Relevant when compiling to/from an interactive protocol).
pub type Round = u8;

/// Metadata associated with a variable.
///
/// We require all fields to have a [Default] implementation. This requirement is forced by
/// deriving [Default].
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariableMetadata {
    /// Who knows it (None if public)
    pub vis: Option<PartyId>,
    /// Its type
    pub sort: Sort,
    /// The name
    pub name: String,
    /// Which round this is introduced in
    pub round: Round,
    /// Whether this is random
    pub random: bool,
    /// Whether this is committed
    pub committed: bool,
}

impl VariableMetadata {
    /// term (cached)
    pub fn term(&self) -> Term {
        leaf_term(Op::Var(self.name.clone(), self.sort.clone()))
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
/// An IR constraint system.
pub struct ComputationMetadata {
    /// A map from variables to their metadata
    vars: FxHashMap<String, VariableMetadata>,
    /// A map from party names to numbers assigned to them.
    party_ids: FxHashMap<String, PartyId>,
    /// Committments.
    ///
    /// Each commitment is a vector of variables.
    commitments: Vec<Vec<String>>,
}

impl ComputationMetadata {
    /// Add a new party to the computation, getting a [PartyId] for them.
    pub fn add_party(&mut self, name: String) -> PartyId {
        self.party_ids.insert(name, self.party_ids.len() as u8);
        self.party_ids.len() as u8 - 1
    }

    /// Add a new input to the computation, visible to `party`, or public if `party` is [None].
    pub fn new_input(&mut self, name: String, party: Option<PartyId>, sort: Sort) {
        let var_md = VariableMetadata {
            sort,
            vis: party,
            name,
            ..Default::default()
        };
        self.new_input_from_meta(var_md);
    }

    /// Make this list of variables a commitment.
    pub fn add_commitment(&mut self, names: Vec<String>) {
        for n in &names {
            let md = self
                .vars
                .get_mut(n)
                .unwrap_or_else(|| panic!("Cannot commit to {}; it is not a variable", n));
            assert!(
                !md.committed,
                "Cannot commit to {}: it is already commited",
                n
            );
            assert_ne!(md.vis, None, "Cannot commit to {}: it is public", n);
            md.committed = true;
        }
        self.commitments.push(names);
    }

    /// Add a new input to the computation.
    pub fn new_input_from_meta(&mut self, metadata: VariableMetadata) {
        debug_assert!(
            !self.vars.contains_key(&metadata.name),
            "Tried to create input {}, but it already existed: {:?}",
            metadata.name,
            self.vars.get(&metadata.name).unwrap()
        );
        self.vars.insert(metadata.name.clone(), metadata);
    }

    /// Lookup metadata
    #[track_caller]
    pub fn lookup<Q: std::borrow::Borrow<str> + ?Sized>(&self, name: &Q) -> &VariableMetadata {
        let n = name.borrow();
        self.vars
            .get(n)
            .unwrap_or_else(|| panic!("Missing input {} in inputs{:#?}", n, self.vars))
    }

    /// Lookup metadata
    #[track_caller]
    pub fn lookup_mut<Q: std::borrow::Borrow<str> + ?Sized>(
        &mut self,
        name: &Q,
    ) -> &mut VariableMetadata {
        let n = name.borrow();
        self.vars
            .get_mut(n)
            .unwrap_or_else(|| panic!("Missing input {}", n))
    }

    /// Returns None if the value is public. Otherwise, the unique party that knows it.
    pub fn get_input_visibility(&self, input_name: &str) -> Option<PartyId> {
        self.lookup(input_name).vis
    }

    /// Is this an input?
    pub fn is_input(&self, input_name: &str) -> bool {
        self.vars.contains_key(input_name)
    }

    /// Is this input public?
    pub fn is_input_public(&self, input_name: &str) -> bool {
        self.get_input_visibility(input_name).is_none()
    }

    /// What sort is this input?
    pub fn input_sort(&self, input_name: &str) -> Sort {
        self.lookup(input_name).sort.clone()
    }

    /// Give all inputs, in a fixed order.
    pub fn ordered_input_names(&self) -> Vec<String> {
        let mut out: Vec<String> = self.vars.keys().cloned().collect();
        out.sort();
        out
    }

    /// Give all public inputs, in a fixed order.
    pub fn ordered_public_inputs(&self) -> Vec<Term> {
        let mut out: Vec<Term> = self
            .vars
            .values()
            .filter_map(|v| {
                if v.vis.is_none() {
                    Some(v.term())
                } else {
                    None
                }
            })
            .collect();
        out.sort_by(|a, b| a.as_var_name().cmp(b.as_var_name()));
        out
    }

    /// Get the interactive structure of the variables. See [InteractiveVars].
    pub fn interactive_vars(&self) -> InteractiveVars {
        let final_round = self.vars.values().map(|m| m.round).max().unwrap_or(0);
        let mut instances = Vec::new();
        let mut rounds = vec![RoundVars::default(); final_round as usize + 1];
        for meta in self.vars.values() {
            if meta.random {
                // is this a challenge?, if so it must be public
                assert!(meta.vis.is_none());
                rounds[meta.round as usize].challenges.push(meta.term());
            } else if meta.vis.is_none() {
                // is it a public non-challenge? if so, it must be round 0
                assert!(meta.round == 0);
                instances.push(meta.term());
            } else if !meta.committed {
                // this is a witness
                rounds[meta.round as usize].witnesses.push(meta.term());
            }
        }
        // If there no final challenges, distinguish the last round of witnesses
        let final_witnesses = if rounds.last().unwrap().challenges.is_empty() {
            rounds.pop().unwrap().witnesses
        } else {
            Vec::new()
        };
        // get the committed witness variables
        let committed_wit_vecs: Vec<Vec<Term>> = self
            .commitments
            .iter()
            .map(|cmt| {
                cmt.iter()
                    .map(|w| self.vars.get(w).unwrap().term())
                    .collect()
            })
            .collect();
        let mut ret = InteractiveVars {
            instances,
            committed_wit_vecs,
            rounds,
            final_witnesses,
        };
        // sort!
        let cmp_name = |a: &Term, b: &Term| a.as_var_name().cmp(b.as_var_name());
        ret.instances.sort_by(cmp_name);
        for round in &mut ret.rounds {
            round.witnesses.sort_by(cmp_name);
            round.challenges.sort_by(cmp_name);
        }
        ret.final_witnesses.sort_by(cmp_name);
        ret
    }

    /// Get a round after the rounds of these variables
    pub fn future_round<'a, Q: Borrow<str> + 'a>(
        &self,
        var_names: impl Iterator<Item = &'a Q>,
    ) -> Round {
        var_names
            .map(|name| self.lookup(name.borrow()).round)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .unwrap()
    }

    /// Give all inputs, in a fixed order.
    pub fn ordered_inputs(&self) -> Vec<Term> {
        let mut out: Vec<Term> = self.vars.values().map(|v| v.term()).collect();
        out.sort_by(|a, b| a.as_var_name().cmp(b.as_var_name()));
        out
    }

    /// Give the set of public input names.
    pub fn public_input_names_set(&self) -> FxHashSet<String> {
        self.ordered_public_inputs()
            .iter()
            .map(|t| t.as_var_name().into())
            .collect()
    }

    /// Get all the inputs visible to `party`.
    pub fn get_inputs_for_party(&self, party: Option<PartyId>) -> FxHashSet<String> {
        self.vars
            .values()
            .filter_map(|v| {
                if v.vis.is_none() || v.vis == party {
                    Some(v.name.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Remove an input
    pub fn remove_var(&mut self, name: &str) {
        self.vars.remove(name);
    }

    /// Create a call term, given the input arguments in sorted order by argument names.
    ///
    /// ## Arguments
    ///
    /// * `name`: function name
    /// * `args`: map of argument name (String) to argument term (Term)
    /// * `ret_sort`: return sort of the function
    ///
    /// ## Returns
    ///
    /// A call term with the input arguments in sorted order by argument names.
    ///
    pub fn ordered_call_term(
        &self,
        name: String,
        args: FxHashMap<String, Term>,
        ret_sort: Sort,
    ) -> Term {
        let ordered_arg_names = self.ordered_input_names();
        let ordered_args = ordered_arg_names
            .iter()
            .map(|name| args.get(name).expect("Argument not found: {}").clone())
            .collect::<Vec<Term>>();
        let ordered_sorts = ordered_args.iter().map(check).collect::<Vec<Sort>>();

        term(Op::Call(name, ordered_sorts, ret_sort), ordered_args)
    }
}

/// A structured collection of variables that indicates the round structure: e.g., orderings,
/// challenges.
///
/// It represents the variables themselves as terms.
#[derive(Default, Debug)]
pub struct InteractiveVars {
    /// Instance vars
    pub instances: Vec<Term>,
    /// Committed witness vectors
    pub committed_wit_vecs: Vec<Vec<Term>>,
    /// Rounds
    pub rounds: Vec<RoundVars>,
    /// Final witnesses
    pub final_witnesses: Vec<Term>,
}

/// Witnesses, followed by a challenge.
#[derive(Default, Clone, Debug)]
pub struct RoundVars {
    /// witnesses
    pub witnesses: Vec<Term>,
    /// followed by challenges
    pub challenges: Vec<Term>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
/// An IR computation.
pub struct Computation {
    /// The outputs of the computation.
    #[serde(with = "crate::ir::term::serde_mods::vec")]
    pub outputs: Vec<Term>,
    /// Metadata about the computation. I.e. who knows what inputs
    pub metadata: ComputationMetadata,
    /// Pre-computations
    pub precomputes: precomp::PreComp,
    /// Persistent Arrays. [(name, term)]
    /// where:
    /// * name: a variable name (array type) indicating the input state
    /// * name: a term indicating the output state
    pub persistent_arrays: Vec<(String, Term)>,
    /// Check these arrays using RAM transcripts
    pub ram_arrays: TermSet,
}

impl Computation {
    /// Create a new variable, `name: s`, where `val_fn` can be called to get the concrete value,
    /// and `public` indicates whether this variable is public in the constraint system.
    ///
    /// ## Arguments
    ///
    ///    * `name`: the name of the new variable
    ///    * `s`: its sort
    ///    * `party`: its visibility: who knows it initially
    ///    * `precompute`: a precomputation that can determine its value (optional). Note that the
    ///      precomputation may rely on information that some parties do not have. In this case,
    ///      those parties will have to provide a value for the variables directly.
    pub fn new_var(
        &mut self,
        name: &str,
        s: Sort,
        party: Option<PartyId>,
        precompute: Option<Term>,
    ) -> Term {
        debug!(
            "Var: {} : {} (visibility: {:?}) (precompute: {})",
            name,
            s,
            party,
            precompute.is_some()
        );
        self.metadata.new_input(name.to_owned(), party, s.clone());
        if let Some(p) = precompute {
            assert_eq!(&s, &check(&p), "precompute {} doesn't match sort {}", p, s);
            self.precomputes.add_output(name.to_owned(), p);
        }
        leaf_term(Op::Var(name.to_owned(), s))
    }

    /// Create a new variable with the given metadata.
    ///
    /// If `precompute` is set, that precomputation is added to give a value for this variable.
    /// Otherwise, the variable is assumed to be an input.
    pub fn new_var_metadata(
        &mut self,
        metadata: VariableMetadata,
        precompute: Option<Term>,
    ) -> Term {
        debug!(
            "Var: {} : {:?} (precompute {})",
            metadata.name,
            metadata,
            precompute.is_some()
        );
        let sort = metadata.sort.clone();
        let name = metadata.name.clone();
        self.metadata.new_input_from_meta(metadata);
        if let Some(p) = precompute {
            assert_eq!(&sort, &check(&p));
            self.precomputes.add_output(name.clone(), p);
        }
        leaf_term(Op::Var(name, sort))
    }

    /// Add a new input `new_input_var` to this computation,
    /// whose value is determined by `precomp`: a term over existing inputs.
    ///
    /// The visibility for `new_input_var` will be computed from the visibility of variables in
    /// `precomp`: there must be at most **one** non-public variable.
    ///
    /// The sort for `new_input_var` will be computed from `precomp`.
    pub fn extend_precomputation(&mut self, new_input_var: String, precomp: Term) {
        debug!("Precompute {}", new_input_var);
        let vis = {
            let mut input_visiblities: FxHashSet<Option<PartyId>> =
                extras::free_variables(precomp.clone())
                    .into_iter()
                    .map(|v| self.metadata.get_input_visibility(&v))
                    .collect();
            input_visiblities.remove(&None);
            match input_visiblities.len() {
                0 => None,
                1 => input_visiblities.into_iter().next().unwrap(),
                _ => panic!("Precomputation for new var {} with term\n\t{}\ninvolves multiple input non-public visibilities:\n\t{:?}", new_input_var, precomp, input_visiblities),
            }
        };
        let sort = check(&precomp);
        self.new_var(&new_input_var, sort, vis, Some(precomp));
    }

    /// Intialize a new persistent array.
    pub fn start_persistent_array(
        &mut self,
        var: &str,
        size: usize,
        field: FieldT,
        party: PartyId,
    ) -> Term {
        let f = Sort::Field(field);
        let s = Sort::Array(Box::new(f.clone()), Box::new(f), size);
        let md = VariableMetadata {
            name: var.to_owned(),
            vis: Some(party),
            sort: s,
            committed: true,
            ..Default::default()
        };
        let term = self.new_var_metadata(md, None);

        // we'll replace dummy later
        let dummy = bool_lit(true);
        self.persistent_arrays.push((var.into(), dummy));
        term
    }

    /// Record the final state of a persistent array. Should be called once per array, with the
    /// same name as [Computation::start_persistent_array].
    pub fn end_persistent_array(&mut self, var: &str, final_state: Term) {
        for (name, t) in &mut self.persistent_arrays {
            if name == var {
                assert_eq!(*t, bool_lit(true));
                *t = final_state;
                return;
            }
        }
        panic!("No existing persistent memory {}", var)
    }

    /// Make a vector of existing variables a commitment.
    pub fn add_commitment(&mut self, names: Vec<String>) {
        self.metadata.add_commitment(names);
    }

    /// Change the sort of a variables
    pub fn remove_var(&mut self, var: &str) {
        self.metadata.remove_var(var);
    }

    /// Assert `s` in the system.
    pub fn assert(&mut self, s: Term) {
        assert!(check(&s) == Sort::Bool);
        debug!("Assert: {}", &s.op());
        self.outputs.push(s);
    }

    /// Create a new system, which tracks values iff `values`.
    pub fn new() -> Self {
        Self {
            outputs: Vec::new(),
            metadata: ComputationMetadata::default(),
            precomputes: Default::default(),
            persistent_arrays: Default::default(),
            ram_arrays: Default::default(),
        }
    }

    /// Get the outputs of the computation.
    ///
    /// For proof systems, these are the assertions that must hold.
    pub fn outputs(&self) -> &Vec<Term> {
        &self.outputs
    }

    /// How many total (unique) terms are there?
    pub fn terms(&self) -> usize {
        let mut terms = FxHashSet::<Term>::default();
        for a in &self.outputs {
            for s in PostOrderIter::new(a.clone()) {
                terms.insert(s);
            }
        }
        terms.len()
    }

    /// An iterator that visits each term in the computation, once.
    pub fn terms_postorder(&self) -> impl Iterator<Item = Term> {
        let mut terms: Vec<_> = PostOrderIter::new(term(Op::Tuple, self.outputs.clone())).collect();
        // drop the top-level tuple term.
        terms.pop();
        terms.into_iter()
    }

    /// Evaluate the precompute, then this computation.
    pub fn eval_all(&self, values: &FxHashMap<String, Value>) -> Vec<Value> {
        let mut values = values.clone();

        // set all challenges to 1.
        for v in self.metadata.vars.values() {
            if v.random {
                let field = v.sort.as_pf();
                let value = Value::Field(pf_challenge(&v.name, field));
                values.insert(v.name.clone(), value);
            }
        }

        values = self.precomputes.eval(&values);

        let mut cache = Default::default();
        let mut outputs = Vec::new();
        for o in &self.outputs {
            outputs.push(eval_cached(o, &values, &mut cache).clone());
        }
        outputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
/// A map of IR computations.
pub struct Computations {
    /// A map of function name --> function computation
    pub comps: FxHashMap<String, Computation>,
}

impl Computations {
    /// Create new empty computations.
    pub fn new() -> Self {
        Self {
            comps: FxHashMap::default(),
        }
    }

    /// Get computation by name
    pub fn get(&self, name: &str) -> &Computation {
        match self.comps.get(name) {
            Some(c) => c,
            None => panic!("Unknown computation: {}", name),
        }
    }
}

/// Compute a (deterministic) prime-field challenge.
pub fn pf_challenge(name: &str, field: &FieldT) -> FieldV {
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use std::hash::{Hash, Hasher};
    // hash the string
    let mut hasher = fxhash::FxHasher::default();
    name.hash(&mut hasher);
    let hash: u64 = hasher.finish();
    // seed ChaCha with the hash
    let mut seed = [0u8; 32];
    seed[0..8].copy_from_slice(&hash.to_le_bytes());
    let mut rng = ChaChaRng::from_seed(seed);
    // sample from ChaCha
    field.random_v(&mut rng)
}

#[cfg(test)]
pub mod test;
