//! IR term definition
//!
//! Generally based on SMT-LIB, and its theories.
//!
//! The most important types and functions are:
//!
//!    * Term structure
//!       * [Term]: perfectly-shared terms. Think of them as shared pointers to
//!       * [TermData]: the underlying term. An operator and some children.
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
use crate::util::once::OnceQueue;
use fxhash::{FxHashMap, FxHashSet};
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
    /// Unsigned bit-vector to prime-field
    ///
    /// Takes the modulus.
    UbvToPf(Arc<Integer>),

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
    /// Update (tuple, element)
    Update(usize),
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
            Op::UbvToPf(_) => Some(1),
            Op::Select => Some(2),
            Op::Store => Some(3),
            Op::Tuple => None,
            Op::Field(_) => Some(1),
            Op::Update(_) => Some(2),
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
            Op::UbvToPf(a) => write!(f, "bv2pf {}", a),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
            Op::Tuple => write!(f, "tuple"),
            Op::Field(i) => write!(f, "field{}", i),
            Op::Update(i) => write!(f, "update{}", i),
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
    Array(Array),
    /// Tuple
    Tuple(Box<[Value]>),
}

#[derive(Clone, PartialEq, Debug, PartialOrd, Hash)]
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
                for field in fields.iter() {
                    write!(f, " {}", field)?;
                }
                write!(f, ")")
            }
            Value::Array(a) => write!(f, "{}", a),
        }
    }
}

impl Display for Array {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(
            f,
            "(array default:{} size:{} {:?})",
            self.default, self.size, self.map
        )
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
#[allow(clippy::derive_hash_xor_eq)]
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
    Tuple(Box<[Sort]>),
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
    pub fn as_tuple(&self) -> &[Sort] {
        if let Sort::Tuple(w) = self {
            w
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
                        if q < *m {
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
            Sort::Field(m) => Value::Field(FieldElem::new(Integer::from(0), m.clone())),
            Sort::Int => Value::Int(0.into()),
            Sort::F32 => Value::F32(0.0f32),
            Sort::F64 => Value::F64(0.0),
            Sort::Tuple(t) => Value::Tuple(t.iter().map(Sort::default_value).collect()),
            Sort::Array(k, v, n) => Value::Array(Array::default((**k).clone(), v, *n)),
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
                for field in fields.iter() {
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
    map: FxHashMap<TermData, TTerm>,
    count: u64,
    last_len: usize,
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
    fn should_collect(&mut self) -> bool {
        let ret = LEN_THRESH_DEN * self.map.len() > LEN_THRESH_NUM * self.last_len;
        if self.last_len > TERM_CACHE_LIMIT {
            // when last_len is big, force a garbage collect every once in a while
            self.last_len = (self.last_len * LEN_DECAY_NUM) / LEN_DECAY_DEN;
        }
        ret
    }
    fn collect(&mut self) {
        let old_size = self.map.len();
        let mut to_check: OnceQueue<Term> = OnceQueue::new();
        self.map.retain(|key, val| {
            if val.elm.upgrade().is_some() {
                true
            } else {
                to_check.extend(key.cs.iter().cloned());
                false
            }
        });
        while let Some(t) = to_check.pop() {
            let data: TermData = (*t).clone();
            std::mem::drop(t);
            if let std::collections::hash_map::Entry::Occupied(e) = self.map.entry(data) {
                if e.get().elm.upgrade().is_none() {
                    let (key, _val) = e.remove_entry();
                    to_check.extend(key.cs.iter().cloned());
                }
            }
        }
        let new_size = self.map.len();
        for (k, v) in self.map.iter() {
            assert!(v.elm.upgrade().is_some(), "Can not upgrade: {:?}", k)
        }
        debug!(target: "ir::term::gc", "{} of {} terms collected", old_size - new_size, old_size);
        self.last_len = new_size;
    }
}
struct TypeTable {
    map: FxHashMap<TTerm, Sort>,
    last_len: usize,
}
impl std::ops::Deref for TypeTable {
    type Target = FxHashMap<TTerm, Sort>;
    fn deref(&self) -> &Self::Target {
        &self.map
    }
}
impl std::ops::DerefMut for TypeTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.map
    }
}
impl TypeTable {
    fn should_collect(&mut self) -> bool {
        let ret = LEN_THRESH_DEN * self.map.len() > LEN_THRESH_NUM * self.last_len;
        if self.last_len > TERM_CACHE_LIMIT {
            // when last_len is big, force a garbage collect every once in a while
            self.last_len = (self.last_len * LEN_DECAY_NUM) / LEN_DECAY_DEN;
        }
        ret
    }
    fn collect(&mut self) {
        let old_size = self.map.len();
        self.map.retain(|term, _| term.to_hconsed().is_some());
        let new_size = self.map.len();
        debug!(target: "ir::term::gc", "{} of {} types collected", old_size - new_size, old_size);
        self.last_len = new_size;
    }
}

lazy_static! {
    static ref TERMS: RwLock<TermTable> = RwLock::new(TermTable {
        map: FxHashMap::default(),
        count: 0,
        last_len: 0,
    });
}

fn mk(elm: TermData) -> Term {
    let mut slf = TERMS.write().unwrap();
    slf.mk(elm)
}

/// Scans the term database and the type database and removes dead terms and types.
pub fn garbage_collect() {
    collect_terms();
    collect_types();
}

const LEN_THRESH_NUM: usize = 8;
const LEN_THRESH_DEN: usize = 1;
const LEN_DECAY_NUM: usize = 15;
const LEN_DECAY_DEN: usize = 16;
/// Scan term and type databases only if they've grown in size since last scan
pub fn maybe_garbage_collect() -> bool {
    let mut ran = {
        let mut term_table = TERMS.write().unwrap();
        if term_table.should_collect() {
            term_table.collect();
            true
        } else {
            false
        }
    };
    {
        let mut type_table = ty::TERM_TYPES.write().unwrap();
        if type_table.should_collect() {
            type_table.collect();
            ran = true;
        }
    }
    ran
}

fn collect_terms() {
    TERMS.write().unwrap().collect();
}

fn collect_types() {
    ty::TERM_TYPES.write().unwrap().collect();
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

    /// Get the underlying tuple constant, if possible.
    pub fn as_tuple_opt(&self) -> Option<&[Value]> {
        if let Op::Const(Value::Tuple(t)) = &self.op {
            Some(t)
        } else {
            None
        }
    }

    /// Get the underlying array constant, if possible.
    pub fn as_array_opt(&self) -> Option<&Array> {
        if let Op::Const(Value::Array(a)) = &self.op {
            Some(a)
        } else {
            None
        }
    }

    /// Get the underlying constant value, if possible.
    pub fn as_value_opt(&self) -> Option<&Value> {
        if let Op::Const(v) = &self.op {
            Some(v)
        } else {
            None
        }
    }

    /// Is this a variable?
    pub fn is_var(&self) -> bool {
        matches!(&self.op, Op::Var(..))
    }

    /// Is this a value
    pub fn is_const(&self) -> bool {
        matches!(&self.op, Op::Const(..))
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

/// Evaluate the term `t`, using variable values in `h`.
pub fn eval(t: &Term, h: &FxHashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::new();
    for c in PostOrderIter::new(t.clone()) {
        let v = match &c.op {
            Op::Var(n, _) => h
                .get(n)
                .unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, h))
                .clone(),
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
            Op::UbvToPf(m) => Value::Field({
                let a = vs.get(&c.cs[0]).unwrap().as_bv().clone();
                field::FieldElem::new(a.uint().clone(), m.clone())
            }),
            // tuple
            Op::Tuple => Value::Tuple(c.cs.iter().map(|c| vs.get(c).unwrap().clone()).collect()),
            Op::Field(i) => {
                let t = vs.get(&c.cs[0]).unwrap().as_tuple();
                assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
                t[*i].clone()
            }
            Op::Update(i) => {
                let mut t = Vec::from(vs.get(&c.cs[0]).unwrap().as_tuple()).into_boxed_slice();
                assert!(i < &t.len(), "{} out of bounds for {}", i, c.cs[0]);
                let e = vs.get(&c.cs[1]).unwrap().clone();
                assert_eq!(t[*i].sort(), e.sort());
                t[*i] = e;
                Value::Tuple(t)
            }
            // array
            Op::Store => {
                let a = vs.get(&c.cs[0]).unwrap().as_array().clone();
                let i = vs.get(&c.cs[1]).unwrap().clone();
                let v = vs.get(&c.cs[2]).unwrap().clone();
                Value::Array(a.clone().store(i, v))
            }
            Op::Select => {
                let a = vs.get(&c.cs[0]).unwrap().as_array().clone();
                let i = vs.get(&c.cs[1]).unwrap();
                a.clone().select(i)
            }
            o => unimplemented!("eval: {:?}", o),
        };
        //println!("Eval {}\nAs   {}", c, v);
        vs.insert(c.clone(), v);
    }
    vs.get(t).unwrap().clone()
}

/// Make an array from a sequence of terms.
///
/// Requires
///
/// * a key sort, as all arrays do. This sort must be iterable (i.e., bool, int, bit-vector, or field).
/// * a value sort, for the array's default
pub fn make_array(key_sort: Sort, value_sort: Sort, i: Vec<Term>) -> Term {
    let d = Sort::Array(Box::new(key_sort.clone()), Box::new(value_sort), i.len()).default_term();
    i.into_iter()
        .zip(key_sort.elems_iter())
        .fold(d, |arr, (val, idx)| term(Op::Store, vec![arr, idx, val]))
}

/// Make a term with no arguments, just an operator.
pub fn leaf_term(op: Op) -> Term {
    term(op, Vec::new())
}

/// Make a term with arguments.
#[track_caller]
pub fn term(op: Op, cs: Vec<Term>) -> Term {
    #[cfg_attr(not(debug_assertions), allow(clippy::let_and_return))]
    let t = mk(TermData { op, cs });
    #[cfg(debug_assertions)]
    check_rec(&t);
    t
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

/// Map from terms
pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;
/// LRU cache of terms (like TermMap, but limited size)
pub type TermCache<T> = hashconsing::coll::HConLru<Term, T>;
/// Set of terms
pub type TermSet = hashconsing::coll::HConSet<Term>;

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
            visited: TermSet::new(),
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

/// A party identifier
pub type PartyId = u8;

#[derive(Clone, Debug, Default)]
/// An IR constraint system.
pub struct ComputationMetadata {
    /// A map from party names to numbers assigned to them.
    pub party_ids: FxHashMap<String, PartyId>,
    /// The next free id.
    pub next_party_id: PartyId,
    /// The order of the inputs
    pub inputs: Vec<Term>,
    /// All inputs, including who knows them. If no visibility is set, the input is public.
    pub input_vis: FxHashMap<String, Option<PartyId>>,
}

impl ComputationMetadata {
    /// Add a new party to the computation, getting a [PartyId] for them.
    pub fn add_party(&mut self, name: String) -> PartyId {
        self.party_ids.insert(name, self.next_party_id);
        self.next_party_id += 1;
        self.next_party_id - 1
    }
    /// Add a new input to the computation, visible to `party`, or public if `party` is [None].
    pub fn new_input(&mut self, input_name: String, party: Option<PartyId>, sort: Sort) {
        let term = leaf_term(Op::Var(input_name.clone(), sort));
        debug_assert!(
            !self.input_vis.contains_key(&input_name),
            "Tried to create input {} (visibility {:?}), but it already existed (visibility {:?})",
            input_name,
            party,
            self.input_vis.get(&input_name).unwrap()
        );
        self.input_vis.insert(input_name, party);
        self.inputs.push(term);
    }
    /// Replace the `original` computation input with `new`, in the order given.
    ///
    /// If the old input order was
    ///
    ///    w x y z x1 x2 x3
    ///
    /// and `x` was replaced with `x1`, `x2`, `x3`, then the new input order is
    ///
    ///    w x1 x2 x3 y z
    ///
    /// and other metadata associated with `x` is removed.
    ///
    /// This is probably called after making the new inputs with `new_input`.
    pub fn replace_input(
        &mut self,
        original: Term,
        new: Vec<(String, Sort, Option<Value>, Option<PartyId>)>,
    ) {
        let mut i = self.inputs.iter().position(|t| t == &original).unwrap();
        self.inputs.remove(i);
        let name = if let Op::Var(n, _) = &original.op {
            n.to_string()
        } else {
            unreachable!()
        };
        self.input_vis.remove(&name).unwrap();
        for (input_name, sort, _, party) in new {
            let term = leaf_term(Op::Var(input_name.clone(), sort));
            debug_assert!(
                !self.input_vis.contains_key(&input_name),
                "Tried to create input {} (visibility {:?}), but it already existed (visibility {:?})",
                input_name,
                party,
                self.input_vis.get(&input_name).unwrap()
            );
            self.input_vis.insert(input_name.clone(), party);
            self.inputs.insert(i, term);
            i += 1;
        }
    }
    /// Returns None if the value is public. Otherwise, the unique party that knows it.
    pub fn get_input_visibility(&self, input_name: &str) -> Option<PartyId> {
        *self
            .input_vis
            .get(input_name)
            .unwrap_or_else(|| panic!("Missing input {} in inputs{:#?}", input_name, self.inputs))
    }
    /// Is this input public?
    pub fn is_input(&self, input_name: &str) -> bool {
        self.input_vis.contains_key(input_name)
    }
    /// Is this input public?
    pub fn is_input_public(&self, input_name: &str) -> bool {
        self.get_input_visibility(input_name).is_none()
    }
    /// Get all public inputs.
    pub fn public_input_names(&self) -> impl Iterator<Item = &str> {
        self.input_vis.iter().filter_map(|(name, party)| {
            if party.is_none() {
                Some(name.as_str())
            } else {
                None
            }
        })
    }
    /// Get all public inputs.
    // I think the lint is just broken here.
    // TODO: submit a patch
    #[allow(clippy::needless_lifetimes)]
    pub fn public_inputs<'a>(&'a self) -> impl Iterator<Item = Term> + 'a {
        self.inputs.iter().filter_map(move |input| {
            if let Op::Var(name, _) = &input.op {
                let party = self.get_input_visibility(name);
                if party.is_none() {
                    Some(input.clone())
                } else {
                    None
                }
            } else {
                unreachable!()
            }
        })
    }
}

#[derive(Clone, Debug, Default)]
/// An IR computation.
pub struct Computation {
    /// The outputs of the computation.
    pub outputs: Vec<Term>,
    /// The values of variables in the system.
    ///
    /// These are tracked when doing witness extension for proof systems.
    pub values: Option<FxHashMap<String, Value>>,
    /// Metadata about the computation. I.e. who knows what inputs
    pub metadata: ComputationMetadata,
}

impl Computation {
    /// Create a new variable, `name: s`, where `val_fn` can be called to get the concrete value,
    /// and `public` indicates whether this variable is public in the constraint system.
    pub fn new_var<F: FnOnce() -> Value>(
        &mut self,
        name: &str,
        s: Sort,
        val_fn: F,
        party: Option<PartyId>,
    ) -> Term {
        debug!("Var: {} (visibility: {:?})", name, party);
        self.metadata.new_input(name.to_owned(), party, s.clone());
        if let Some(vs) = self.values.as_mut() {
            let val = val_fn();
            debug!("  val = {}", val);
            if let Some(v) = vs.insert(name.to_owned(), val) {
                panic!("{} already had a value: {}", name, v);
            }
        }
        leaf_term(Op::Var(name.to_owned(), s))
    }
    /// Replace the `original` computation input with `new`, in the order given.
    ///
    /// If the old input order was
    ///
    ///    w x y z
    ///
    /// and `x` was replaced with `x1`, `x2`, `x3`, then the new input order is
    ///
    ///    w x1 x2 x3 y z
    ///
    /// and other metadata associated with `x` is removed.
    ///
    /// This is called in place of `new_var` during transformations.
    pub fn replace_input(
        &mut self,
        original: Term,
        mut new: Vec<(String, Sort, Option<Value>, Option<PartyId>)>,
    ) {
        if let Some(vs) = self.values.as_mut() {
            if let Op::Var(name, _) = &original.op {
                vs.remove(name);
                for (name, _, val_opt, _) in &mut new {
                    vs.insert(name.clone(), std::mem::take(val_opt).unwrap());
                }
            }
        }
        self.metadata.replace_input(original, new);
    }

    /// Change the value associated with an input
    pub fn map_value(&mut self, name: &str, f: impl FnOnce(Value) -> Value) {
        if let Some(vs) = self.values.as_mut() {
            let loc = vs.get_mut(name).unwrap();
            let v = std::mem::replace(loc, Value::Bool(false));
            *loc = f(v);
        }
    }

    /// Create a new variable, `name` in the constraint system, and set it equal to `term`.
    /// `public` indicates whether this variable is public in the constraint system.
    pub fn assign(&mut self, name: &str, term: Term, party: Option<PartyId>) -> Term {
        let val = self.eval(&term);
        let sort = check(&term);
        let var = self.new_var(name, sort, || val.unwrap(), party);
        self.assert(term![Op::Eq; var.clone(), term]);
        var
    }
    /// Assert `s` in the system.
    pub fn assert(&mut self, s: Term) {
        assert!(check(&s) == Sort::Bool);
        debug!("Assert: {}", &s.op);
        self.outputs.push(s);
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
            outputs: Vec::new(),
            metadata: ComputationMetadata::default(),
            values: if values {
                Some(FxHashMap::default())
            } else {
                None
            },
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
}

#[cfg(test)]
pub mod test;
