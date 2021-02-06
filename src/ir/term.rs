use hashconsing::{consign, HConsed, WHConsed};
use lazy_static::lazy_static;
use rug::Integer;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::sync::{Arc, RwLock};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Ite,
    Eq,
    Let(String),
    Var(String, Sort),
    Const(Value),

    BvBinOp(BvBinOp),
    BvBinPred(BvBinPred),
    BvNaryOp(BvNaryOp),
    BvUnOp(BvUnOp),
    BoolToBv,
    // high, low (zero-indexed, inclusive)
    BvExtract(usize, usize),
    BvConcat,
    // number of extra bits
    BvUext(usize),
    BvSext(usize),

    Implies,
    BoolNaryOp(BoolNaryOp),
    Not,
    BvBit(usize),

    FpBinOp(FpBinOp),
    FpBinPred(FpBinPred),
    FpUnPred(FpBinPred),
    FpUnOp(FpUnOp),
    //FpFma,
    BvToFp,
    UbvToFp(usize),
    SbvToFp(usize),
    // dest width
    FpToFp(usize),

    PfUnOp(PfUnOp),
    PfNaryOp(PfNaryOp),

    // key sort
    ConstArray(Sort),
    Select,
    Store,
}

impl Op {
    fn arity(&self) -> Option<usize> {
        match self {
            Op::Ite => Some(3),
            Op::Eq => Some(2),
            Op::Let(_) => Some(2),
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
            Op::Implies => Some(2),
            Op::BoolNaryOp(_) => None,
            Op::Not => Some(1),
            Op::BvBit(_) => Some(1),
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
            Op::ConstArray(_) => Some(1),
            Op::Select => Some(2),
            Op::Store => Some(3),
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Op::Ite => write!(f, "ite"),
            Op::Eq => write!(f, "="),
            Op::Let(a) => write!(f, "let {}", a),
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
            Op::Implies => write!(f, "=>"),
            Op::BoolNaryOp(a) => write!(f, "{}", a),
            Op::Not => write!(f, "not"),
            Op::BvBit(a) => write!(f, "bit {}", a),
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
            Op::ConstArray(_) => write!(f, "const-array"),
            Op::Select => write!(f, "select"),
            Op::Store => write!(f, "store"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoolNaryOp {
    And,
    Xor,
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
pub enum BvBinOp {
    Sub,
    Udiv,
    Urem,
    Shl,
    Ashr,
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
pub enum BvBinPred {
    Ult,
    Ugt,
    Ule,
    Uge,
    Slt,
    Sgt,
    Sle,
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
pub enum BvNaryOp {
    Add,
    Mul,
    Or,
    And,
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
pub enum BvUnOp {
    Not,
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
pub enum FpBinOp {
    Add,
    Mul,
    Sub,
    Div,
    Rem,
    Max,
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
pub enum FpUnOp {
    Neg,
    Abs,
    Sqrt,
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
pub enum FpBinPred {
    Le,
    Lt,
    Eq,
    Ge,
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
pub enum FpUnPred {
    Normal,
    Subnormal,
    Zero,
    Infinite,
    Nan,
    Negative,
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
pub enum PfNaryOp {
    Add,
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
pub enum PfUnOp {
    Neg,
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TermData {
    pub op: Op,
    pub children: Vec<Term>,
}

impl Display for TermData {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if let Op::Var(..) = &self.op {
            write!(f, "{}", self.op)
        } else {
            write!(f, "({}", self.op)?;
            for c in &self.children {
                write!(f, " {}", c)?;
            }
            write!(f, ")")
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FieldElem {
    pub i: Integer,
    pub modulus: Arc<Integer>,
}

impl Display for FieldElem {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.i.significant_bits() + 1 < self.modulus.significant_bits() {
            write!(f, "{}", self.i)
        } else {
            write!(f, "-{}", (*self.modulus).clone() - &self.i)
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BitVector {
    pub uint: Integer,
    pub width: usize,
}

macro_rules! bv_arith_impl {
    ($Trait:path, $fn:ident) => {
        impl $Trait for BitVector {
            type Output = Self;
            fn $fn(self, other: Self) -> Self {
                assert_eq!(self.width, other.width);
                BitVector {
                    uint: (self.uint.$fn(other.uint)).keep_bits(self.width as u32),
                    width: self.width,
                }
            }
        }
    };
}

bv_arith_impl!(std::ops::Add, add);
bv_arith_impl!(std::ops::Sub, sub);
bv_arith_impl!(std::ops::Mul, mul);
bv_arith_impl!(std::ops::Div, div);
bv_arith_impl!(std::ops::Rem, rem);

impl std::ops::Shl for BitVector {
    type Output = Self;
    fn shl(self, other: Self) -> Self {
        assert_eq!(self.width, other.width);
        BitVector {
            uint: (self.uint.shl(other.uint.to_u32().unwrap())).keep_bits(self.width as u32),
            width: self.width,
        }
    }
}

impl BitVector {
    pub fn ashr(mut self, other: Self) -> Self {
        assert_eq!(self.width, other.width);
        let n = other.uint.to_u32().unwrap();
        let b = self.uint.get_bit(self.width as u32 - 1);
        self.uint >>= n;
        for i in 0..n {
            self.uint.set_bit(self.width as u32 - 1 - i, b);
        }
        self
    }
    pub fn lshr(self, other: Self) -> Self {
        assert_eq!(self.width, other.width);
        BitVector {
            uint: (self.uint >> other.uint.to_u32().unwrap()).keep_bits(self.width as u32),
            width: self.width,
        }
    }
    pub fn concat(self, other: Self) -> Self {
        BitVector {
            uint: (self.uint << other.width as u32) | other.uint,
            width: self.width + other.width,
        }
    }
    pub fn extract(self, high: usize, low: usize) -> Self {
        BitVector {
            uint: (self.uint >> low as u32).keep_bits((high - low + 1) as u32),
            width: high - low + 1,
        }
    }
}

impl Display for BitVector {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "#b")?;
        for i in 0..self.width {
            write!(
                f,
                "#{}",
                self.uint.get_bit((self.width - i - 1) as u32) as u8
            )?;
        }
        Ok(())
    }
}

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    BitVector(BitVector),
    F32(f32),
    F64(f64),
    Int(Integer),
    Field(FieldElem),
    Bool(bool),
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
        }
    }
}

impl std::cmp::Eq for Value {}
impl std::hash::Hash for Value {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Value::BitVector(bv) => bv.hash(state),
            Value::F32(bv) => bv.to_bits().hash(state),
            Value::F64(bv) => bv.to_bits().hash(state),
            Value::Int(bv) => bv.hash(state),
            Value::Field(bv) => bv.hash(state),
            Value::Bool(bv) => bv.hash(state),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sort {
    BitVector(usize),
    F32,
    F64,
    Int,
    Field(Arc<Integer>),
    Bool,
    Array(Box<Sort>, Box<Sort>),
}

pub type Term = HConsed<TermData>;
// "Temporary" terms.
pub type TTerm = WHConsed<TermData>;

consign! {
    let TERM_FACTORY = consign(100) for TermData;
}

lazy_static! {
    static ref TERM_TYPES: RwLock<HashMap<TTerm, Sort>> = RwLock::new(HashMap::new());
}

impl Value {
    pub fn sort(&self) -> Sort {
        match &self {
            Value::Bool(_) => Sort::Bool,
            Value::Field(f) => Sort::Field(f.modulus.clone()),
            Value::Int(_) => Sort::Int,
            Value::F64(_) => Sort::F64,
            Value::F32(_) => Sort::F32,
            Value::BitVector(b) => Sort::BitVector(b.width),
        }
    }
    pub fn as_bool(&self) -> bool {
        if let Value::Bool(b) = self {
            *b
        } else {
            panic!("Not a bool: {}", self)
        }
    }
    pub fn as_bv(&self) -> &BitVector {
        if let Value::BitVector(b) = self {
            b
        } else {
            panic!("Not a bit-vec: {}", self)
        }
    }
}

fn bv_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    if let Sort::BitVector(_) = a {
        Ok(a)
    } else {
        Err(TypeErrorReason::ExpectedBv(a.clone(), ctx))
    }
}

fn bool_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    if let &Sort::Bool = a {
        Ok(a)
    } else {
        Err(TypeErrorReason::ExpectedBool(a.clone(), ctx))
    }
}

fn fp_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    match a {
        Sort::F32 | Sort::F64 => Ok(a),
        _ => Err(TypeErrorReason::ExpectedFp(a.clone(), ctx)),
    }
}

fn pf_or<'a>(a: &'a Sort, ctx: &'static str) -> Result<&'a Sort, TypeErrorReason> {
    match a {
        Sort::Field(_) => Ok(a),
        _ => Err(TypeErrorReason::ExpectedPf(a.clone(), ctx)),
    }
}

fn eq_or(a: &Sort, b: &Sort, ctx: &'static str) -> Result<(), TypeErrorReason> {
    if a == b {
        Ok(())
    } else {
        Err(TypeErrorReason::NotEqual(a.clone(), b.clone(), ctx))
    }
}

fn all_eq_or<'a, I: Iterator<Item = &'a Sort>>(
    mut a: I,
    ctx: &'static str,
) -> Result<&'a Sort, TypeErrorReason> {
    let first = a
        .next()
        .ok_or_else(|| TypeErrorReason::EmptyNary(ctx.to_owned()))?;
    for x in a {
        if first != x {
            return Err(TypeErrorReason::NotEqual(
                (*first).clone(),
                (*x).clone(),
                ctx,
            ));
        }
    }
    Ok(first)
}

/// Type-check this term, recursively as needed.
/// All results are stored in the global type table.
pub fn check(t: Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.read().unwrap().get(&t.to_weak()) {
        return Ok(s.clone());
    }
    {
        let mut term_tys = TERM_TYPES.write().unwrap();
        // to_check is a stack of (node, children checked) pairs.
        let mut to_check = vec![(t.clone(), false)];
        while to_check.len() > 0 {
            let back = to_check.last_mut().unwrap();
            let weak = back.0.to_weak();
            // The idea here is to check that
            match term_tys.get_key_value(&weak) {
                Some((p, _)) => {
                    if p.to_hconsed().is_some() {
                        to_check.pop();
                        continue;
                    } else {
                        term_tys.remove(&weak);
                    }
                }
                None => {}
            }
            if !back.1 {
                back.1 = true;
                for c in back.0.children.clone() {
                    to_check.push((c, false));
                }
            } else {
                let tys = back
                    .0
                    .children
                    .iter()
                    .map(|c| term_tys.get(&c.to_weak()).unwrap())
                    .collect::<Vec<_>>();
                let ty = (match (&back.0.op, &tys[..]) {
                    (Op::Eq, &[a, b]) => eq_or(a, b, "=").map(|_| Sort::Bool),
                    (Op::Ite, &[&Sort::Bool, b, c]) => eq_or(b, c, "ITE").map(|_| b.clone()),
                    (Op::Var(_, s), &[]) => Ok(s.clone()),
                    (Op::Let(_), &[_, a]) => Ok(a.clone()),
                    (Op::Const(c), &[]) => Ok(c.sort()),
                    (Op::BvBinOp(_), &[a, b]) => {
                        let ctx = "bv binary op";
                        bv_or(a, ctx)
                            .and_then(|_| eq_or(a, b, ctx))
                            .map(|_| a.clone())
                    }
                    (Op::BvBinPred(_), &[a, b]) => {
                        let ctx = "bv binary predicate";
                        bv_or(a, ctx)
                            .and_then(|_| eq_or(a, b, ctx))
                            .map(|_| Sort::Bool)
                    }
                    (Op::BvNaryOp(_), a) => {
                        let ctx = "bv nary op";
                        all_eq_or(a.into_iter().cloned(), ctx)
                            .and_then(|t| bv_or(t, ctx))
                            .map(|a| a.clone())
                    }
                    (Op::BvUnOp(_), &[a]) => bv_or(a, "bv unary op").map(|a| a.clone()),
                    (Op::BoolToBv, &[Sort::Bool]) => Ok(Sort::BitVector(1)),
                    (Op::BvExtract(high, low), &[Sort::BitVector(w)]) => {
                        if low <= high && high < w {
                            Ok(Sort::BitVector(high - low + 1))
                        } else {
                            Err(TypeErrorReason::OutOfBounds(format!(
                                "Cannot slice from {} to {} in a bit-vector of width {}",
                                high, low, w
                            )))
                        }
                    }
                    (Op::BvConcat, a) => a
                        .iter()
                        .try_fold(0, |w, x| match x {
                            Sort::BitVector(ww) => Ok(w + ww),
                            s => Err(TypeErrorReason::ExpectedBv((*s).clone(), "concat")),
                        })
                        .map(Sort::BitVector),
                    (Op::BvSext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
                    (Op::BvUext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
                    (Op::Implies, &[a, b]) => {
                        let ctx = "bool binary op";
                        bool_or(a, ctx)
                            .and_then(|_| eq_or(a, b, ctx))
                            .map(|_| a.clone())
                    }
                    (Op::BoolNaryOp(_), a) => {
                        let ctx = "bool nary op";
                        all_eq_or(a.into_iter().cloned(), ctx)
                            .and_then(|t| bool_or(t, ctx))
                            .map(|a| a.clone())
                    }
                    (Op::Not, &[a]) => bool_or(a, "bool unary op").map(|a| a.clone()),
                    (Op::BvBit(i), &[Sort::BitVector(w)]) => {
                        if i < w {
                            Ok(Sort::Bool)
                        } else {
                            Err(TypeErrorReason::OutOfBounds(format!(
                                "Cannot get bit {} of a {}-bit bit-vector",
                                i, w
                            )))
                        }
                    }
                    (Op::FpBinOp(_), &[a, b]) => {
                        let ctx = "fp binary op";
                        fp_or(a, ctx)
                            .and_then(|_| eq_or(a, b, ctx))
                            .map(|_| a.clone())
                    }
                    (Op::FpBinPred(_), &[a, b]) => {
                        let ctx = "fp binary predicate";
                        fp_or(a, ctx)
                            .and_then(|_| eq_or(a, b, ctx))
                            .map(|_| Sort::Bool)
                    }
                    (Op::FpUnOp(_), &[a]) => fp_or(a, "fp unary op").map(|a| a.clone()),
                    (Op::FpUnPred(_), &[a]) => fp_or(a, "fp unary predicate").map(|_| Sort::Bool),
                    (Op::BvToFp, &[Sort::BitVector(64)]) => Ok(Sort::F64),
                    (Op::BvToFp, &[Sort::BitVector(32)]) => Ok(Sort::F64),
                    (Op::UbvToFp(64), &[a]) => bv_or(a, "ubv-to-fp").map(|_| Sort::F64),
                    (Op::UbvToFp(32), &[a]) => bv_or(a, "ubv-to-fp").map(|_| Sort::F32),
                    (Op::SbvToFp(64), &[a]) => bv_or(a, "sbv-to-fp").map(|_| Sort::F64),
                    (Op::SbvToFp(32), &[a]) => bv_or(a, "sbv-to-fp").map(|_| Sort::F32),
                    (Op::FpToFp(64), &[a]) => fp_or(a, "fp-to-fp").map(|_| Sort::F64),
                    (Op::FpToFp(32), &[a]) => fp_or(a, "fp-to-fp").map(|_| Sort::F32),
                    (Op::PfNaryOp(_), a) => {
                        let ctx = "pf nary op";
                        all_eq_or(a.into_iter().cloned(), ctx)
                            .and_then(|t| pf_or(t, ctx))
                            .map(|a| a.clone())
                    }
                    (Op::PfUnOp(_), &[a]) => pf_or(a, "pf unary op").map(|a| a.clone()),
                    (Op::ConstArray(s), &[a]) => {
                        Ok(Sort::Array(Box::new(s.clone()), Box::new(a.clone())))
                    }
                    (Op::Select, &[Sort::Array(k, v), a]) => {
                        eq_or(k, a, "select").map(|_| (**v).clone())
                    }
                    (Op::Store, &[Sort::Array(k, v), a, b]) => eq_or(k, a, "store")
                        .and_then(|_| eq_or(v, b, "store"))
                        .map(|_| Sort::Array(k.clone(), v.clone())),

                    (_, _) => Err(TypeErrorReason::Custom(format!("other"))),
                })
                .map_err(|reason| TypeError {
                    op: back.0.op.clone(),
                    args: tys.into_iter().cloned().collect(),
                    reason,
                })?;
                term_tys.insert(back.0.to_weak(), ty);
            }
        }
    }
    Ok(TERM_TYPES
        .read()
        .unwrap()
        .get(&t.to_weak())
        .unwrap()
        .clone())
}

pub fn eval(t: &Term, h: &HashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::new();
    for c in PostOrderIter::new(t.clone()) {
        let v = match &c.op {
            Op::Var(n, _) => h.get(n).unwrap().clone(),
            Op::Eq => {
                Value::Bool(vs.get(&c.children[0]).unwrap() == vs.get(&c.children[1]).unwrap())
            }
            Op::Not => Value::Bool(!vs.get(&c.children[0]).unwrap().as_bool()),
            Op::Implies => Value::Bool(
                !vs.get(&c.children[0]).unwrap().as_bool()
                    || vs.get(&c.children[1]).unwrap().as_bool(),
            ),
            Op::BoolNaryOp(BoolNaryOp::Or) => {
                Value::Bool(c.children.iter().any(|c| vs.get(c).unwrap().as_bool()))
            }
            Op::BoolNaryOp(BoolNaryOp::And) => {
                Value::Bool(c.children.iter().all(|c| vs.get(c).unwrap().as_bool()))
            }
            Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
                c.children
                    .iter()
                    .map(|c| vs.get(c).unwrap().as_bool())
                    .fold(false, std::ops::BitXor::bitxor),
            ),
            Op::BvBit(i) => Value::Bool(
                vs.get(&c.children[0])
                    .unwrap()
                    .as_bv()
                    .uint
                    .get_bit(*i as u32),
            ),
            Op::BvConcat => Value::BitVector({
                let mut it = c
                    .children
                    .iter()
                    .map(|c| vs.get(c).unwrap().as_bv().clone());
                let f = it.next().unwrap();
                it.fold(f, BitVector::concat)
            }),
            Op::BvExtract(h, l) => Value::BitVector(
                vs.get(&c.children[0])
                    .unwrap()
                    .as_bv()
                    .clone()
                    .extract(*h, *l),
            ),
            Op::Const(v) => v.clone(),
            o => unimplemented!("eval: {:?}", o),
        };
        vs.insert(c.clone(), v);
    }
    vs.get(t).unwrap().clone()
}

#[derive(Debug, PartialEq, Eq)]
pub struct TypeError {
    op: Op,
    args: Vec<Sort>,
    reason: TypeErrorReason,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeErrorReason {
    NotEqual(Sort, Sort, &'static str),
    ExpectedBool(Sort, &'static str),
    ExpectedFp(Sort, &'static str),
    ExpectedBv(Sort, &'static str),
    ExpectedPf(Sort, &'static str),
    EmptyNary(String),
    Custom(String),
    OutOfBounds(String),
}

pub fn leaf_term(op: Op) -> Term {
    term(op, Vec::new())
}

pub fn term(op: Op, children: Vec<Term>) -> Term {
    use hashconsing::HashConsign;
    let t = TERM_FACTORY.mk(TermData { op, children });
    check(t.clone()).unwrap();
    t
}

#[macro_export]
macro_rules! term {
    ($x:expr; $($y:expr),+) => {
        term($x, vec![$($y),+])
    };
}

// A distribution of boolean terms with some size.
// All subterms are booleans.
pub struct BoolDist(pub usize);

// A distribution of n usizes that sum to this value.
// (n, sum)
pub struct Sum(usize, usize);
impl rand::distributions::Distribution<Vec<usize>> for Sum {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Vec<usize> {
        use rand::seq::SliceRandom;
        let mut acc = self.1;
        let mut ns = Vec::new();
        assert!(acc == 0 || self.0 > 0);
        while acc > 0 && ns.len() < self.0 {
            let x = rng.gen_range(0..acc);
            acc -= x;
            ns.push(x);
        }
        while ns.len() < self.0 {
            ns.push(0);
        }
        if acc > 0 {
            *ns.last_mut().unwrap() += acc;
        }
        ns.shuffle(rng);
        ns
    }
}

impl rand::distributions::Distribution<Term> for BoolDist {
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> Term {
        use rand::seq::SliceRandom;
        let ops = &[
            Op::Const(Value::Bool(rng.gen())),
            Op::Var(
                std::str::from_utf8(&[b'a' + rng.gen_range(0..26)])
                    .unwrap()
                    .to_owned(),
                Sort::Bool,
            ),
            Op::Not,
            Op::Implies,
            Op::BoolNaryOp(BoolNaryOp::Or),
            Op::BoolNaryOp(BoolNaryOp::And),
            Op::BoolNaryOp(BoolNaryOp::Xor),
        ];
        let o = match self.0 {
            1 => ops[..2].choose(rng),  // arity 0
            2 => ops[2..3].choose(rng), // arity 1
            _ => ops[2..].choose(rng),  // others
        }
        .unwrap()
        .clone();
        // Now, self.0 is a least arity+1
        let a = o.arity().unwrap_or_else(|| rng.gen_range(2..self.0));
        let excess = self.0 - 1 - a;
        let ns = Sum(a, excess).sample(rng);
        let subterms = ns
            .into_iter()
            .map(|n| BoolDist(n + 1).sample(rng))
            .collect::<Vec<_>>();
        term(o, subterms)
    }
}

pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;
pub type TermSet = hashconsing::coll::HConSet<Term>;

pub struct PostOrderIter {
    // (children stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter {
    pub fn new(t: Term) -> Self {
        Self {
            stack: vec![(false, t)],
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
                let cs = self.stack.last().unwrap().1.children.clone();
                self.stack.extend(cs.into_iter().map(|c| (false, c)));
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
pub struct Constraints {
    pub assertions: Vec<Term>,
    pub public_inputs: HashSet<String>,
    pub values: Option<HashMap<String, Value>>,
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
            assert_eq!(check(v), Ok(Sort::Bool));
            let v = leaf_term(Op::Var("b".to_owned(), Sort::BitVector(4)));
            assert_eq!(check(v.clone()), Ok(Sort::BitVector(4)));
            let v = t();
            assert_eq!(check(v), Ok(Sort::Bool));
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
