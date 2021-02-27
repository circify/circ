use hashconsing::{consign, HConsed, WHConsed};
use lazy_static::lazy_static;
use log::debug;
use rug::Integer;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::{self, Display, Formatter};
use std::sync::{Arc, RwLock};

pub mod bv;
pub mod dist;
pub mod extras;
pub mod field;

pub use bv::BitVector;
pub use field::FieldElem;

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
    // number of bits the element should fit in.
    PfToBv(usize),

    Implies,
    BoolNaryOp(BoolNaryOp),
    Not,
    BvBit(usize),
    // Ternary majority operator.
    BoolMaj,

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

    // key sort, size
    // Note that "size" assumes an order and starting point for keys.
    ConstArray(Sort, usize),
    Select,
    Store,
}

impl Op {
    pub fn arity(&self) -> Option<usize> {
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
    // TODO: add overflow predicates.
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

#[derive(Clone, PartialEq, Debug, PartialOrd)]
pub enum Value {
    BitVector(BitVector),
    F32(f32),
    F64(f64),
    Int(Integer),
    Field(FieldElem),
    Bool(bool),
    Array(Sort, Box<Value>, BTreeMap<Value, Value>, usize),
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
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Sort {
    BitVector(usize),
    F32,
    F64,
    Int,
    Field(Arc<Integer>),
    Bool,
    // key, value, size
    // size presumes an order, and zero, for the keys.
    Array(Box<Sort>, Box<Sort>, usize),
}

impl Sort {
    #[track_caller]
    pub fn as_bv(&self) -> usize {
        if let Sort::BitVector(w) = self {
            *w
        } else {
            panic!("{} is not a bit-vector", self)
        }
    }

    #[track_caller]
    pub fn as_pf(&self) -> Arc<Integer> {
        if let Sort::Field(w) = self {
            w.clone()
        } else {
            panic!("{} is not a field", self)
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
        }
    }
}

pub type Term = HConsed<TermData>;
// "Temporary" terms.
pub type TTerm = WHConsed<TermData>;

consign! {
    let TERM_FACTORY = consign(10000) for TermData;
}

lazy_static! {
    static ref TERM_TYPES: RwLock<HashMap<TTerm, Sort>> = RwLock::new(HashMap::new());
}

/// Scans the term database and the type database and removes dead terms.
pub fn garbage_collect() {
    use hashconsing::HashConsign;
    TERM_FACTORY.collect();
    let mut ty_map = TERM_TYPES.write().unwrap();
    let old_size = ty_map.len();
    ty_map.retain(|term, _| term.to_hconsed().is_some());
    let new_size = ty_map.len();
    debug!(target: "ir::term::gc", "{} of {} types collected", old_size -new_size, old_size);
}

impl TermData {
    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Op::Const(Value::Bool(b)) = &self.op {
            Some(*b)
        } else {
            None
        }
    }
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Op::Const(Value::BitVector(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }
    pub fn as_pf_opt(&self) -> Option<&FieldElem> {
        if let Op::Const(Value::Field(b)) = &self.op {
            Some(b)
        } else {
            None
        }
    }
    pub fn is_var(&self) -> bool {
        if let Op::Var(..) = &self.op {
            true
        } else {
            false
        }
    }
}

impl Value {
    pub fn sort(&self) -> Sort {
        match &self {
            Value::Bool(_) => Sort::Bool,
            Value::Field(f) => Sort::Field(f.modulus().clone()),
            Value::Int(_) => Sort::Int,
            Value::F64(_) => Sort::F64,
            Value::F32(_) => Sort::F32,
            Value::BitVector(b) => Sort::BitVector(b.width()),
            Value::Array(s, _, _, _) => s.clone(),
        }
    }
    #[track_caller]
    pub fn as_bool(&self) -> bool {
        if let Value::Bool(b) = self {
            *b
        } else {
            panic!("Not a bool: {}", self)
        }
    }
    #[track_caller]
    pub fn as_bv(&self) -> &BitVector {
        if let Value::BitVector(b) = self {
            b
        } else {
            panic!("Not a bit-vec: {}", self)
        }
    }
    #[track_caller]
    pub fn as_pf(&self) -> &FieldElem {
        if let Value::Field(b) = self {
            b
        } else {
            panic!("Not a field-elem: {}", self)
        }
    }

    pub fn as_bool_opt(&self) -> Option<bool> {
        if let Value::Bool(b) = self {
            Some(*b)
        } else {
            None
        }
    }
    pub fn as_bv_opt(&self) -> Option<&BitVector> {
        if let Value::BitVector(b) = self {
            Some(b)
        } else {
            None
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
pub fn check_raw(t: &Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.read().unwrap().get(&t.to_weak()) {
        return Ok(s.clone());
    }
    {
        let mut term_tys = TERM_TYPES.write().unwrap();
        // to_check is a stack of (node, cs checked) pairs.
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
                for c in back.0.cs.clone() {
                    to_check.push((c, false));
                }
            } else {
                let tys = back
                    .0
                    .cs
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
                    (Op::PfToBv(a), &[Sort::Field(_)]) => Ok(Sort::BitVector(*a)),
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
                    (Op::BoolMaj, &[a, b, c]) => {
                        let ctx = "bool majority";
                        bool_or(a, ctx)
                            .and_then(|_| bool_or(b, ctx).and_then(|_| bool_or(c, ctx)))
                            .map(|c| c.clone())
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
                    (Op::ConstArray(s, n), &[a]) => {
                        Ok(Sort::Array(Box::new(s.clone()), Box::new(a.clone()), *n))
                    }
                    (Op::Select, &[Sort::Array(k, v, _), a]) => {
                        eq_or(k, a, "select").map(|_| (**v).clone())
                    }
                    (Op::Store, &[Sort::Array(k, v, n), a, b]) => eq_or(k, a, "store")
                        .and_then(|_| eq_or(v, b, "store"))
                        .map(|_| Sort::Array(k.clone(), v.clone(), *n)),
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

#[track_caller]
pub fn check(t: &Term) -> Sort {
    check_raw(t).unwrap()
}

pub fn eval(t: &Term, h: &HashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::new();
    for c in PostOrderIter::new(t.clone()) {
        let v = match &c.op {
            Op::Var(n, _) => h.get(n).unwrap().clone(),
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
            o => unimplemented!("eval: {:?}", o),
        };
        //println!("Eval {}\nAs   {}", c, v);
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

pub fn term(op: Op, cs: Vec<Term>) -> Term {
    use hashconsing::HashConsign;
    let t = TERM_FACTORY.mk(TermData { op, cs });
    check(&t);
    t
}

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
macro_rules! term {
    ($x:expr; $($y:expr),+) => {
        term($x, vec![$($y),+])
    };
}

pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;
pub type TermSet = hashconsing::coll::HConSet<Term>;

pub struct PostOrderIter {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter {
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
pub struct Constraints {
    pub(super) assertions: Vec<Term>,
    pub(super) public_inputs: HashSet<String>,
    pub(super) values: Option<HashMap<String, Value>>,
}

impl Constraints {
    pub fn eval_and_save(&mut self, name: &str, term: &Term) {
        if let Some(vs) = self.values.as_mut() {
            let v = eval(term, vs);
            vs.insert(name.to_owned(), v);
        }
    }
    pub fn new(values: bool) -> Self {
        Self {
            assertions: Vec::new(),
            public_inputs: HashSet::new(),
            values: if values { Some(HashMap::new()) } else { None },
        }
    }
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
    pub fn publicize(&mut self, s: String) {
        self.public_inputs.insert(s);
    }
    pub fn assert(&mut self, s: Term) {
        assert!(check(&s) == Sort::Bool);
        debug!("Assert: {}", s);
        self.assertions.push(s);
    }
    pub fn assertions(&self) -> &Vec<Term> {
        &self.assertions
    }
    pub fn consume(self) -> (Vec<Term>, HashSet<String>, Option<HashMap<String, Value>>) {
        (self.assertions, self.public_inputs, self.values)
    }
    pub fn from_parts(
        assertions: Vec<Term>,
        public_inputs: HashSet<String>,
        values: Option<HashMap<String, Value>>,
    ) -> Self {
        Self {
            assertions,
            public_inputs,
            values,
        }
    }
    pub fn assertions_as_term(&self) -> Term {
        term(Op::BoolNaryOp(BoolNaryOp::And), self.assertions.clone())
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
