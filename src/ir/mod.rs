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

impl Const {
    fn sort(&self) -> Sort {
        match &self {
            Const::Bool(_) => Sort::Bool,
            Const::Field(f) => Sort::Field(f.modulus.clone()),
            Const::Int(_) => Sort::Int,
            Const::F64(_) => Sort::F64,
            Const::F32(_) => Sort::F32,
            Const::BitVector(b) => Sort::BitVector(b.width),
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
                    (Op::BvConcat, &[Sort::BitVector(a), Sort::BitVector(b)]) => {
                        Ok(Sort::BitVector(a + b))
                    }
                    (Op::BvSext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
                    (Op::BvUext(a), &[Sort::BitVector(b)]) => Ok(Sort::BitVector(a + b)),
                    (Op::BoolBinOp(_), &[a, b]) => {
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
                    (Op::BoolUnOp(_), &[a]) => bool_or(a, "bool unary op").map(|a| a.clone()),
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

macro_rules! term {
    ($x:expr) => {
        {
            use hashconsing::HashConsign;
            let t = TERM_FACTORY.mk(TermData { op: $x, children: Vec::new() });
            check(t.clone()).unwrap();
            t
        }
    };
    ($x:expr, $($y:expr),+) => {
        {
            use hashconsing::HashConsign;
            let t = TERM_FACTORY.mk(TermData { op: $x, children: vec![$($y),+] });
            check(t.clone()).unwrap();
            t
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

    mod type_ {
        use super::*;

        #[test]
        fn vars() {
            let v = term![Op::Var("a".to_owned(), Sort::Bool)];
            assert_eq!(check(v), Ok(Sort::Bool));
            let v = term![Op::Var("b".to_owned(), Sort::BitVector(4))];
            assert_eq!(check(v.clone()), Ok(Sort::BitVector(4)));
            let v = term![
                Op::BvBit(4),
                term![
                    Op::BvConcat,
                    v,
                    term![Op::BoolToBv, term![Op::Var("c".to_owned(), Sort::Bool)]]
                ]
            ];
            assert_eq!(check(v), Ok(Sort::Bool));
        }
    }
}
