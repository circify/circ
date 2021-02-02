use hashconsing::{consign, HConsed, WHConsed};
use lazy_static::lazy_static;
use rug::Integer;
use std::collections::HashMap;
use std::sync::RwLock;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Ite,
    Eq,
    Let(String),
    Var(String, Sort),
    Const(Const),

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

    BoolBinOp(BoolBinOp),
    BoolNaryOp(BoolNaryOp),
    BoolUnOp(BoolUnOp),
    BvBit(usize),

    FpBinOp(FpBinOp),
    FpBinPred(FpBinPred),
    FpUnPred(FpBinPred),
    FpUnOp(FpUnOp),
    FpFma,
    BvToFp,
    UbvToFp(usize),
    SbvToFp(usize),
    // (from, to)
    FpToFp(usize, usize),

    PfUnOp(PfUnOp),
    PfNaryOp(PfNaryOp),

    // key sort
    ConstArray(Sort),
    Select,
    Store,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoolBinOp {
    Implies,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoolNaryOp {
    And,
    Xor,
    Or,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BoolUnOp {
    Not,
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BvNaryOp {
    Add,
    Mul,
    Or,
    And,
    Xor,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BvUnOp {
    Not,
    Neg,
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FpUnOp {
    Neg,
    Abs,
    Sqrt,
    Round,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum FpBinPred {
    Le,
    Lt,
    Eq,
    Ge,
    Gt,
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

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PfNaryOp {
    Add,
    Mul,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PfUnOp {
    Neg,
    Recip,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TermData {
    pub op: Op,
    pub children: Vec<Term>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FieldElem {
    pub i: Integer,
    pub modulus: Integer,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BitVector {
    pub uint: Integer,
    pub width: usize,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Const {
    BitVector(BitVector),
    F32(f32),
    F64(f64),
    Int(Integer),
    Field(FieldElem),
    Bool(bool),
}

impl std::cmp::Eq for Const {}
impl std::hash::Hash for Const {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Const::BitVector(bv) => bv.hash(state),
            Const::F32(bv) => bv.to_bits().hash(state),
            Const::F64(bv) => bv.to_bits().hash(state),
            Const::Int(bv) => bv.hash(state),
            Const::Field(bv) => bv.hash(state),
            Const::Bool(bv) => bv.hash(state),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Sort {
    BitVector(usize),
    F32,
    F64,
    Int,
    Field(Integer),
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

pub fn check(t: Term) -> Result<Sort, TypeError> {
    if let Some(s) = TERM_TYPES.read().unwrap().get(&t.to_weak()) {
        return Ok(s.clone());
    }
    let term_tys = TERM_TYPES.write().unwrap();
    let mut to_check = vec![(t.clone(), false)];
    while to_check.len() > 0 {
        let back = to_check.last_mut().unwrap();
        if term_tys.contains_key(&back.0.to_weak()) {
            to_check.pop();
        } else if !back.1 {
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
            let ty = match (&back.0.op, &tys[..]) {
                (Op::Eq, &[a, b]) => {
                    if a == b {
                        Ok(Sort::Bool)
                    } else {
                        Err(TypeError::NotEqual(a.clone(), b.clone(), "="))
                    }
                }
                (Op::Ite, &[&Sort::Bool, b, c]) => {
                    if b != c {
                        Err(TypeError::NotEqual(b.clone(), c.clone(), "="))
                    } else {
                        Ok(b.clone())
                    }
                }
                (Op::Var(_, s), &[]) => Ok(s.clone()),
                (o, args) => Err(TypeError::Custom(format!(
                    "Cannot type {:?} applied to {:?}",
                    o, args
                ))),
            }?;
            // TODO
        }
    }
    Ok(TERM_TYPES
        .read()
        .unwrap()
        .get(&t.to_weak())
        .unwrap()
        .clone())
}

pub enum TypeError {
    NotEqual(Sort, Sort, &'static str),
    ExpectedBool(Sort, &'static str),
    Custom(String),
}

macro_rules! term {
    ($x:expr) => {
        {
            use hashconsing::HashConsign;
            TERM_FACTORY.mk(TermData { op: $x, children: Vec::new() })
        }
    };
    ($x:expr, $($y:expr),+) => {
        {
            use hashconsing::HashConsign;
            TERM_FACTORY.mk(TermData { op: $x, children: vec![$($y),+] })
        }
    };
}

pub type TermMap<T> = hashconsing::coll::HConMap<Term, T>;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn eq() {
        let v = term![Op::Var("a".to_owned(), Sort::Bool)];
        let u = term![Op::Var("a".to_owned(), Sort::Bool)];
        let w = term![Op::Var("b".to_owned(), Sort::Bool)];
        assert_eq!(v, u);
        assert!(v != w);
        assert!(u != w);
    }
}
