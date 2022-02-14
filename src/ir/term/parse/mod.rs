//! A parser for [Term]s.

use logos::Logos;

use fxhash::FxHashMap as HashMap;

mod lex;

use lex::Token;
use std::fmt::{self, Debug, Display, Formatter};
use std::str::{from_utf8, FromStr};
use std::sync::Arc;

use super::*;

/// A token tree, LISP-style.
///
/// It can be "interpreted" into an IR term
enum TokTree<'src> {
    Leaf(Token, &'src [u8]),
    List(Vec<TokTree<'src>>),
}

use TokTree::*;

impl<'src> Display for TokTree<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Leaf(_, l) => write!(f, "{}", from_utf8(l).unwrap()),
            List(tts) => {
                let mut first = true;
                write!(f, "(")?;
                for tt in tts {
                    if first {
                        first = false
                    } else {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", tt)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl<'src> Debug for TokTree<'src> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Leaf(_, l) => write!(f, "{}", from_utf8(l).unwrap()),
            List(tts) => f.debug_list().entries(tts).finish(),
        }
    }
}

/// Parse a token tree.
fn parse_tok_tree(bytes: &[u8]) -> TokTree {
    let mut stack: Vec<Vec<TokTree>> = vec![vec![]];
    let mut lex = Token::lexer(bytes).spanned();
    while let Some((t, s)) = lex.next() {
        match t {
            Token::TokenErr => {
                panic!("Could not tokenize: {}", from_utf8(&bytes[s]).unwrap())
            }
            Token::Open => {
                stack.push(vec![]);
            }
            Token::Close => {
                assert!(stack.len() > 1, "Hanging closing paren");
                let l = TokTree::List(stack.pop().unwrap());
                stack.last_mut().unwrap().push(l);
            }
            _ => {
                stack.last_mut().unwrap().push(TokTree::Leaf(t, &bytes[s]));
            }
        }
    }
    assert_eq!(
        stack.len(),
        1,
        "There are {} unclosed parens",
        stack.len() - 1
    );
    assert!(stack[0].len() > 0, "Empty parse");
    assert!(stack[0].len() < 2, "Multiple top-level expressions");
    stack.pop().unwrap().pop().unwrap()
}

struct IrInterp<'src> {
    /// A map from an identifier to a stack of bindings.
    /// The stack is there for scoping.
    bindings: HashMap<&'src [u8], Vec<Term>>,
    /// The stack of default field moduli
    moduli: Vec<Arc<Integer>>,
}

enum CtrlOp {
    Let,
    Declare,
    TupleValue,
    ArrayValue,
    SetDefaultModulus,
}

impl<'src> IrInterp<'src> {
    fn new() -> Self {
        Self {
            moduli: Vec::new(),
            bindings: HashMap::default(),
        }
    }

    /// Takes bindings in order bound, and unbinds
    fn unbind(&mut self, bindings: Vec<Vec<u8>>) {
        for b in bindings {
            self.bindings.get_mut(b.as_slice()).unwrap().pop().unwrap();
        }
    }

    /// Takes bindings in order bound, and unbinds
    fn bind(&mut self, key: &'src [u8], value: Term) {
        self.bindings
            .entry(key)
            .or_insert_with(Vec::new)
            .push(value)
    }

    /// Takes bindings in order bound, and unbinds
    fn get_binding(&self, key: &'src [u8]) -> &Term {
        self.bindings
            .get(key)
            .and_then(|v| v.last())
            .unwrap_or_else(|| panic!("Unknown binding {}", from_utf8(key).unwrap()))
    }

    fn op(&mut self, tt: &TokTree) -> Result<Op, CtrlOp> {
        use Token::Ident;
        match tt {
            Leaf(Ident, b"let") => Err(CtrlOp::Let),
            Leaf(Ident, b"declare") => Err(CtrlOp::Declare),
            Leaf(Ident, b"tuple_value") => Err(CtrlOp::TupleValue),
            Leaf(Ident, b"array_value") => Err(CtrlOp::ArrayValue),
            Leaf(Ident, b"set_default_modulus") => Err(CtrlOp::SetDefaultModulus),
            Leaf(Ident, b"ite") => Ok(Op::Ite),
            Leaf(Ident, b"=") => Ok(Op::Eq),
            Leaf(Ident, b"bvsub") => Ok(Op::BvBinOp(BvBinOp::Sub)),
            Leaf(Ident, b"bvashr") => Ok(Op::BvBinOp(BvBinOp::Ashr)),
            Leaf(Ident, b"bvlshr") => Ok(Op::BvBinOp(BvBinOp::Lshr)),
            Leaf(Ident, b"bvshl") => Ok(Op::BvBinOp(BvBinOp::Shl)),
            Leaf(Ident, b"bvudiv") => Ok(Op::BvBinOp(BvBinOp::Udiv)),
            Leaf(Ident, b"bvurem") => Ok(Op::BvBinOp(BvBinOp::Urem)),
            Leaf(Ident, b"bvsge") => Ok(Op::BvBinPred(BvBinPred::Sge)),
            Leaf(Ident, b"bvsgt") => Ok(Op::BvBinPred(BvBinPred::Sgt)),
            Leaf(Ident, b"bvsle") => Ok(Op::BvBinPred(BvBinPred::Sle)),
            Leaf(Ident, b"bvslt") => Ok(Op::BvBinPred(BvBinPred::Slt)),
            Leaf(Ident, b"bvuge") => Ok(Op::BvBinPred(BvBinPred::Uge)),
            Leaf(Ident, b"bvugt") => Ok(Op::BvBinPred(BvBinPred::Ugt)),
            Leaf(Ident, b"bvule") => Ok(Op::BvBinPred(BvBinPred::Ule)),
            Leaf(Ident, b"bvult") => Ok(Op::BvBinPred(BvBinPred::Ult)),
            Leaf(Ident, b"bvadd") => Ok(Op::BvNaryOp(BvNaryOp::Add)),
            Leaf(Ident, b"bvmul") => Ok(Op::BvNaryOp(BvNaryOp::Mul)),
            Leaf(Ident, b"bvxor") => Ok(Op::BvNaryOp(BvNaryOp::Xor)),
            Leaf(Ident, b"bvand") => Ok(Op::BvNaryOp(BvNaryOp::And)),
            Leaf(Ident, b"bvor") => Ok(Op::BvNaryOp(BvNaryOp::Or)),
            Leaf(Ident, b"bvnot") => Ok(Op::BvUnOp(BvUnOp::Not)),
            Leaf(Ident, b"bvneg") => Ok(Op::BvUnOp(BvUnOp::Neg)),
            Leaf(Ident, b"bool2bv") => Ok(Op::BoolToBv),
            Leaf(Ident, b"concat") => Ok(Op::BvConcat),
            Leaf(Ident, b"=>") => Ok(Op::Implies),
            Leaf(Ident, b"not") => Ok(Op::Not),
            Leaf(Ident, b"xor") => Ok(Op::BoolNaryOp(BoolNaryOp::Xor)),
            Leaf(Ident, b"and") => Ok(Op::BoolNaryOp(BoolNaryOp::And)),
            Leaf(Ident, b"or") => Ok(Op::BoolNaryOp(BoolNaryOp::Or)),
            Leaf(Ident, b"maj") => Ok(Op::BoolMaj),
            Leaf(Ident, b"fpsub") => Ok(Op::FpBinOp(FpBinOp::Sub)),
            Leaf(Ident, b"fpadd") => Ok(Op::FpBinOp(FpBinOp::Add)),
            Leaf(Ident, b"fpmul") => Ok(Op::FpBinOp(FpBinOp::Mul)),
            Leaf(Ident, b"fpdiv") => Ok(Op::FpBinOp(FpBinOp::Div)),
            Leaf(Ident, b"fprem") => Ok(Op::FpBinOp(FpBinOp::Rem)),
            Leaf(Ident, b"fpmax") => Ok(Op::FpBinOp(FpBinOp::Max)),
            Leaf(Ident, b"fpmin") => Ok(Op::FpBinOp(FpBinOp::Min)),
            Leaf(Ident, b"fpneg") => Ok(Op::FpUnOp(FpUnOp::Neg)),
            Leaf(Ident, b"fpabs") => Ok(Op::FpUnOp(FpUnOp::Abs)),
            Leaf(Ident, b"fpsqrt") => Ok(Op::FpUnOp(FpUnOp::Sqrt)),
            Leaf(Ident, b"fpround") => Ok(Op::FpUnOp(FpUnOp::Round)),
            Leaf(Ident, b"fpge") => Ok(Op::FpBinPred(FpBinPred::Ge)),
            Leaf(Ident, b"fpgt") => Ok(Op::FpBinPred(FpBinPred::Gt)),
            Leaf(Ident, b"fple") => Ok(Op::FpBinPred(FpBinPred::Le)),
            Leaf(Ident, b"fplt") => Ok(Op::FpBinPred(FpBinPred::Lt)),
            Leaf(Ident, b"fpeq") => Ok(Op::FpBinPred(FpBinPred::Eq)),
            Leaf(Ident, b"fpnormal") => Ok(Op::FpUnPred(FpUnPred::Normal)),
            Leaf(Ident, b"fpsubnormal") => Ok(Op::FpUnPred(FpUnPred::Subnormal)),
            Leaf(Ident, b"fpzero") => Ok(Op::FpUnPred(FpUnPred::Zero)),
            Leaf(Ident, b"fpinfinite") => Ok(Op::FpUnPred(FpUnPred::Infinite)),
            Leaf(Ident, b"fpnan") => Ok(Op::FpUnPred(FpUnPred::Nan)),
            Leaf(Ident, b"fpnegative") => Ok(Op::FpUnPred(FpUnPred::Negative)),
            Leaf(Ident, b"fppositive") => Ok(Op::FpUnPred(FpUnPred::Positive)),
            Leaf(Ident, b"bv2fp") => Ok(Op::BvToFp),
            Leaf(Ident, b"+") => Ok(Op::PfNaryOp(PfNaryOp::Add)),
            Leaf(Ident, b"*") => Ok(Op::PfNaryOp(PfNaryOp::Mul)),
            Leaf(Ident, b"pfrecip") => Ok(Op::PfUnOp(PfUnOp::Recip)),
            Leaf(Ident, b"-") => Ok(Op::PfUnOp(PfUnOp::Neg)),
            Leaf(Ident, b"select") => Ok(Op::Select),
            Leaf(Ident, b"store") => Ok(Op::Store),
            Leaf(Ident, b"tuple") => Ok(Op::Tuple),
            List(tts) => match &tts[..] {
                [Leaf(Ident, b"extract"), a, b] => Ok(Op::BvExtract(self.usize(a), self.usize(b))),
                [Leaf(Ident, b"uext"), a] => Ok(Op::BvUext(self.usize(a))),
                [Leaf(Ident, b"sext"), a] => Ok(Op::BvSext(self.usize(a))),
                [Leaf(Ident, b"pf2bv"), a] => Ok(Op::PfToBv(self.usize(a))),
                [Leaf(Ident, b"bit"), a] => Ok(Op::BvBit(self.usize(a))),
                [Leaf(Ident, b"ubv2fp"), a] => Ok(Op::UbvToFp(self.usize(a))),
                [Leaf(Ident, b"sbv2fp"), a] => Ok(Op::SbvToFp(self.usize(a))),
                [Leaf(Ident, b"fp2fp"), a] => Ok(Op::FpToFp(self.usize(a))),
                [Leaf(Ident, b"bv2pf"), a] => Ok(Op::UbvToPf(Arc::new(self.int(a)))),
                [Leaf(Ident, b"field"), a] => Ok(Op::Field(self.usize(a))),
                [Leaf(Ident, b"update"), a] => Ok(Op::Update(self.usize(a))),
                _ => todo!("Unparsed op: {}", tt),
            },
            _ => todo!("Unparsed op: {}", tt),
        }
    }
    fn value(&mut self, tt: &TokTree<'src>) -> Value {
        let t = self.term(tt);
        match &t.op {
            Op::Const(v) => v.clone(),
            _ => panic!("Expected value, found term {}", t),
        }
    }
    fn sort(&mut self, tt: &TokTree) -> Sort {
        use Token::Ident;
        match tt {
            Leaf(Ident, b"bool") => Sort::Bool,
            Leaf(Ident, b"int") => Sort::Int,
            Leaf(Ident, b"f32") => Sort::F32,
            Leaf(Ident, b"f64") => Sort::F64,
            List(ls) => {
                assert!(ls.len() > 0);
                match &ls[..] {
                    [Leaf(Ident, b"mod"), m] => Sort::Field(Arc::new(self.int(m))),
                    [Leaf(Ident, b"bv"), w] => Sort::BitVector(self.usize(w)),
                    [Leaf(Ident, b"array"), k, v, s] => Sort::Array(
                        Box::new(self.sort(k)),
                        Box::new(self.sort(v)),
                        self.usize(s),
                    ),
                    [Leaf(Ident, b"tuple"), ..] => {
                        Sort::Tuple(ls[1..].iter().map(|li| self.sort(li)).collect())
                    }
                    _ => panic!("Expected sort, found {}", tt),
                }
            }
            _ => panic!("Expected sort, found {}", tt),
        }
    }
    fn int(&self, tt: &TokTree) -> Integer {
        match tt {
            Leaf(Token::Int, s) => Integer::parse(s).unwrap().into(),
            _ => panic!("Expected integer, got {}", tt),
        }
    }
    fn usize(&self, tt: &TokTree) -> usize {
        match tt {
            Leaf(Token::Int, s) => usize::from_str(from_utf8(s).unwrap()).unwrap().into(),
            _ => panic!("Expected integer, got {}", tt),
        }
    }
    /// Parse lets, returning bindings, in-order.
    fn let_list(&mut self, tt: &TokTree<'src>) -> Vec<Vec<u8>> {
        if let List(tts) = tt {
            tts.iter()
                .map(|tti| match tti {
                    List(ls) => match &ls[..] {
                        [Leaf(Token::Ident, name), s] => {
                            let t = self.term(s);
                            self.bind(name, t);
                            name.to_vec()
                        }
                        _ => panic!("Expected let, found {}", tti),
                    },
                    _ => panic!("Expected let, found {}", tti),
                })
                .collect()
        } else {
            panic!("Expected let list, found: {}", tt)
        }
    }
    /// Parse associative value list
    fn value_alist(&mut self, tt: &TokTree<'src>) -> Vec<(Value, Value)> {
        if let List(tts) = tt {
            tts.iter()
                .map(|tti| match tti {
                    List(ls) => match &ls[..] {
                        [k, v] => (self.value(k), self.value(v)),
                        _ => panic!("Expected let, found {}", tti),
                    },
                    _ => panic!("Expected let, found {}", tti),
                })
                .collect()
        } else {
            panic!("Expected let list, found: {}", tt)
        }
    }
    /// Parse declarations, returning bindings, in-order.
    fn decl_list(&mut self, tt: &TokTree<'src>) -> Vec<Vec<u8>> {
        if let List(tts) = tt {
            tts.iter()
                .map(|tti| match tti {
                    List(ls) => match &ls[..] {
                        [Leaf(Token::Ident, name), s] => {
                            let sort = self.sort(s);
                            let t = leaf_term(Op::Var(from_utf8(name).unwrap().to_owned(), sort));
                            self.bind(name, t);
                            name.to_vec()
                        }
                        _ => panic!("Expected declaration, found {}", tti),
                    },
                    _ => panic!("Expected declaration, found {}", tti),
                })
                .collect()
        } else {
            panic!("Expected declaration list, found: {}", tt)
        }
    }
    fn term(&mut self, tt: &TokTree<'src>) -> Term {
        use Token::*;
        match tt {
            Leaf(Bin, s) => leaf_term(Op::Const(Value::BitVector(
                BitVector::from_bin_lit(s).unwrap(),
            ))),
            Leaf(Hex, s) => leaf_term(Op::Const(Value::BitVector(
                BitVector::from_hex_lit(s).unwrap(),
            ))),
            Leaf(Int, s) => leaf_term(Op::Const(Value::Int(Integer::parse(s).unwrap().into()))),
            Leaf(Field, s) => {
                let (v, m) = if let Some(i) = s.iter().position(|b| *b == b'm') {
                    (
                        Integer::parse(&s[2..i]).unwrap().into(),
                        Arc::new(Integer::parse(&s[i + 1..]).unwrap().into()),
                    )
                } else {
                    let m = self
                        .moduli
                        .last()
                        .unwrap_or_else(|| {
                            panic!("Field value without a modulus, and no default modulus set")
                        })
                        .clone();
                    (Integer::parse(&s[2..]).unwrap().into(), m)
                };
                leaf_term(Op::Const(Value::Field(FieldElem::new(v, m))))
            }
            Leaf(Ident, n) => self.get_binding(n).clone(),
            List(tts) => {
                assert!(tts.len() > 0, "Expected term, got empty list");
                match self.op(&tts[0]) {
                    Err(CtrlOp::Let) => {
                        assert_eq!(
                            tts.len(),
                            3,
                            "A let should have 2 arguments: (let ((v1 t1) ... (vn tn)) t)"
                        );
                        let bindings = self.let_list(&tts[1]);
                        let t = self.term(&tts[2]);
                        self.unbind(bindings);
                        t
                    }
                    Err(CtrlOp::Declare) => {
                        assert_eq!(
                            tts.len(),
                            3,
                            "A decl should have 2 arguments: (let ((v1 s1) ... (vn sn)) t)"
                        );
                        let bindings = self.decl_list(&tts[1]);
                        let t = self.term(&tts[2]);
                        self.unbind(bindings);
                        t
                    }
                    Err(CtrlOp::ArrayValue) => {
                        assert_eq!(tts.len(), 5);
                        let key_sort = self.sort(&tts[1]);
                        let default = self.value(&tts[2]);
                        let size = self.usize(&tts[3]);
                        let vals = self.value_alist(&tts[4]);
                        leaf_term(Op::Const(Value::Array(Array::new(
                            key_sort,
                            Box::new(default),
                            vals.into_iter().collect(),
                            size,
                        ))))
                    }
                    Err(CtrlOp::TupleValue) => leaf_term(Op::Const(Value::Tuple(
                        tts[1..]
                            .iter()
                            .map(|tti| self.value(tti))
                            .collect::<Vec<_>>()
                            .into(),
                    ))),
                    Err(CtrlOp::SetDefaultModulus) => {
                        assert_eq!(
                            tts.len(),
                            3,
                            "A set_default_modulus should have 2 arguments: modulus and term"
                        );
                        let m = Arc::new(self.int(&tts[1]));
                        self.moduli.push(m);
                        let t = self.term(&tts[2]);
                        self.moduli.pop().unwrap();
                        t
                    }
                    Ok(o) => term(o, tts[1..].iter().map(|tti| self.term(tti)).collect()),
                }
            }
            Leaf(Open | Close | TokenErr, _) => unreachable!("should be caught in tree building"),
        }
    }
}

/// Parse a term.
pub fn parse_term(src: &[u8]) -> Term {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.term(&tree)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn bool() {
        let t = parse_term(b"(declare ((a bool) (b bool)) (let ((c (and a b))) (xor (or (not c) b) c a (=> a b))))");
        assert_eq!(check(&t), Sort::Bool);
    }

    #[test]
    fn bv() {
        let t = parse_term(b"(declare ((a (bv 5)) (b (bv 3))) (let ((c (bvand a a))) (bvxor (bvor (bvnot a) a) a ((sext 2) b))))");
        assert_eq!(check(&t), Sort::BitVector(5));
    }
}
