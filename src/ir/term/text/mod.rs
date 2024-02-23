//! Defines a textual serialization format for [Term]s.
//!
//! Includes a parser ([parse_term]) and serializer ([serialize_term]) for [Term]s.
//!
//! Includes a parser ([parse_value_map]) and serializer ([serialize_value_map]) for value maps.
//!
//! Includes a parser ([parse_computation]) and serializer ([serialize_computation]) for [Computation]s.
//!
//! Includes a parser ([parse_precompute]) and serializer ([serialize_precompute]) for [precomp::PreComp]s.
//!
//!
//! * IR Textual format
//!   * It's s-expressions.
//!   * `N`: natural number
//!   * `I`: integer (arbitrary-precision)
//!   * `X`: identifier
//!     * regex: `[^()0-9#; \t\n\f][^(); \t\n\f#]*`
//!   * Computation `C`: `(computation M P PERSISTENT_ARRAYS RAM_ARRAYS T)`
//!     * Metadata `M`: `(metadata PARTIES INPUTS COMMITMENTS)`
//!       * PARTIES is `(parties X1 .. Xn)`
//!       * INPUTS is `(inputs INPUT1 .. INPUTn)`
//!         * INPUT is `(X S PARTY)`
//!         * PARTY is `(party X)` or nothing (public)
//!       * COMMITMENTS is `(commitments COMMITMENT1 .. COMMITMENTn)`
//!         * COMMITMENT is `(commitment X1 .. Xn)`
//!       * ARRAYS is `(commitments COMMITMENT1 .. COMMITMENTn)`
//!     * Precompute `P`: `(precompute INPUTS OUTPUTS TUPLE_TERM)`
//!       * INPUTS is `((X1 S1) .. (Xn Sn))`
//!       * OUTPUTS is `((X1 S1) .. (Xn Sn))`
//!       * TUPLE_TERM is a tuple of the same arity as the output
//!     * PERSISTENT_ARRAYS (optional): `(persistent_arrays ARRAY*)`:
//!       * ARRAY is `(X S T)`
//!         * X is the name of the inital state
//!         * S is the size
//!         * T is the state (final)
//!     * RAM_ARRAYS (optional): `(ram_arrays T*)`:
//!   * Sort `S`:
//!     * `bool`
//!     * `f32`
//!     * `f64`
//!     * `(bv N)`
//!     * `(mod I)`
//!     * `(tuple S1 ... Sn)`
//!     * `(array Sk Sv N)`
//!   * Value `V`:
//!     * boolean: `true`, `false`
//!     * integer: `I`
//!     * bit-vector: `#xFFFF...`, `#bBBBB...`
//!     * field literal: `#fDD` or `#fDDmDD`.
//!       * In the former case, an ambient modulus must be set.
//!     * tuple: `(#t V1 ... Vn)`
//!     * array: `(#a Sk V N ((Vk1 Vv1) ... (Vkn Vvn)))`
//!     * list: `(#l Sk (V1 ... Vn))`
//!       * gives an array with default value sort, length n, and increasing keys for the values
//!   * Term `T`:
//!     * value: `V`
//!     * let: `(let ((X1 T1) ... (Xn Tn)) T)`
//!     * declare: `(declare ((X1 S1) ... (Xn Sn)) T)`
//!     * set_default_modulus: `(set_default_modulus I T)`
//!       * within term T, I will be the default field modulus
//!       * NB: after the closing paren, I is *no longer* the default modulus
//!     * operator: `(O T1 ... TN)`
//!   * Operator `O`:
//!     * Plain operators: (`bvmul`, `and`, ...)
//!     * Composite operators: `(field N)`, `(update N)`, `(sext N)`, `(uext N)`, `(bit N)`, ...
//!       * call operator: `(call X (X1 ... XN) (S1 ... SN) (RS1 ... RSN))`

use circ_fields::{FieldT, FieldV};

use logos::Logos;

use fxhash::FxHashMap as HashMap;

mod lex;

use lex::Token;
use std::fmt::{self, Debug, Display, Formatter, Write};
use std::str::{from_utf8, FromStr};
use std::sync::Arc;

use super::*;

/// A token tree, LISP-style.
///
/// It can be "interpreted" into an IR term
#[derive(PartialEq, Eq)]
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
                    write!(f, "{tt}")?;
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
    let lex = Token::lexer(bytes).spanned();
    for (t, s) in lex {
        match t {
            Token::Error => {
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
    assert!(!stack[0].is_empty(), "Empty parse");
    assert!(stack[0].len() < 2, "Multiple top-level expressions");
    stack.pop().unwrap().pop().unwrap()
}

struct IrInterp<'src> {
    /// A map from an identifier to a stack of bindings.
    /// The stack is there for scoping.
    bindings: HashMap<&'src [u8], Vec<Term>>,
    /// The stack of field moduli used in this IR
    int_arcs: Vec<Arc<Integer>>,
    /// The current default field modulus, if any
    modulus_stack: Vec<Arc<Integer>>,
    /// Whether we should un-bind out-of-scope ids
    do_unbinds: bool,
}

enum CtrlOp {
    Let,
    Declare,
    TupleValue,
    ArrayValue,
    ListValue,
    SetDefaultModulus,
}

enum VariableMetadataItem {
    Party(PartyId),
    Round(Round),
    Committed,
    Random,
}

impl<'src> IrInterp<'src> {
    fn new() -> Self {
        Self {
            bindings: HashMap::default(),
            int_arcs: Vec::new(),
            modulus_stack: Vec::new(),
            do_unbinds: true,
        }
    }

    /// Takes bindings in order bound, and unbinds
    fn unbind(&mut self, bindings: Vec<Vec<u8>>) {
        if self.do_unbinds {
            for b in bindings {
                self.bindings.get_mut(b.as_slice()).unwrap().pop().unwrap();
            }
        }
    }

    /// Takes bindings in order bound, and unbinds
    fn bind(&mut self, key: &'src [u8], value: Term) {
        self.bindings.entry(key).or_default().push(value)
    }

    /// Takes bindings in order bound, and unbinds
    fn get_binding(&self, key: &'src [u8]) -> &Term {
        self.bindings
            .get(key)
            .and_then(|v| v.last())
            .unwrap_or_else(|| panic!("Unknown binding {}", from_utf8(key).unwrap()))
    }

    fn op(&mut self, tt: &TokTree<'src>) -> Result<Op, CtrlOp> {
        use Token::Ident;
        match tt {
            Leaf(Ident, b"let") => Err(CtrlOp::Let),
            Leaf(Ident, b"declare") => Err(CtrlOp::Declare),
            Leaf(Ident, b"#t") => Err(CtrlOp::TupleValue),
            Leaf(Ident, b"#a") => Err(CtrlOp::ArrayValue),
            Leaf(Ident, b"#l") => Err(CtrlOp::ListValue),
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
            Leaf(Ident, b"/") => Ok(Op::PfDiv),
            Leaf(Ident, b"-") => Ok(Op::PfUnOp(PfUnOp::Neg)),
            Leaf(Ident, b"<") => Ok(INT_LT),
            Leaf(Ident, b"<=") => Ok(INT_LE),
            Leaf(Ident, b">") => Ok(INT_GT),
            Leaf(Ident, b">=") => Ok(INT_GE),
            Leaf(Ident, b"intadd") => Ok(INT_ADD),
            Leaf(Ident, b"intmul") => Ok(INT_MUL),
            Leaf(Ident, b"select") => Ok(Op::Select),
            Leaf(Ident, b"store") => Ok(Op::Store),
            Leaf(Ident, b"cstore") => Ok(Op::CStore),
            Leaf(Ident, b"tuple") => Ok(Op::Tuple),
            Leaf(Ident, b"pf2bool_trusted") => Ok(Op::PfToBoolTrusted),
            Leaf(Ident, bytes) => {
                if let Some(e) = ext::ExtOp::parse(bytes) {
                    Ok(Op::ExtOp(e))
                } else {
                    todo!("Unparsed op: {}", tt)
                }
            }
            List(tts) => match &tts[..] {
                [Leaf(Ident, b"extract"), a, b] => Ok(Op::BvExtract(self.usize(a), self.usize(b))),
                [Leaf(Ident, b"uext"), a] => Ok(Op::BvUext(self.usize(a))),
                [Leaf(Ident, b"sext"), a] => Ok(Op::BvSext(self.usize(a))),
                [Leaf(Ident, b"pf2bv"), a] => Ok(Op::PfToBv(self.usize(a))),
                [Leaf(Ident, b"pf_fits_in_bits"), a] => Ok(Op::PfFitsInBits(self.usize(a))),
                [Leaf(Ident, b"bit"), a] => Ok(Op::BvBit(self.usize(a))),
                [Leaf(Ident, b"ubv2fp"), a] => Ok(Op::UbvToFp(self.usize(a))),
                [Leaf(Ident, b"sbv2fp"), a] => Ok(Op::SbvToFp(self.usize(a))),
                [Leaf(Ident, b"fp2fp"), a] => Ok(Op::FpToFp(self.usize(a))),
                [Leaf(Ident, b"challenge"), name, field] => Ok(Op::PfChallenge(
                    self.ident_string(name),
                    FieldT::from(self.int(field)),
                )),
                [Leaf(Ident, b"array"), k, v] => Ok(Op::Array(self.sort(k), self.sort(v))),
                [Leaf(Ident, b"bv2pf"), a] => Ok(Op::UbvToPf(FieldT::from(self.int(a)))),
                [Leaf(Ident, b"field"), a] => Ok(Op::Field(self.usize(a))),
                [Leaf(Ident, b"update"), a] => Ok(Op::Update(self.usize(a))),
                [Leaf(Ident, b"call"), Leaf(Ident, name), arg_sorts, ret_sort] => {
                    let name = from_utf8(name).unwrap().to_owned();
                    let arg_sorts = self.sorts(arg_sorts);
                    let ret_sort = self.sort(ret_sort);
                    Ok(Op::Call(name, arg_sorts, ret_sort))
                }
                [Leaf(Ident, b"fill"), key_sort, size] => {
                    Ok(Op::Fill(self.sort(key_sort), self.usize(size)))
                }
                _ => todo!("Unparsed op: {}", tt),
            },
            _ => todo!("Unparsed op: {}", tt),
        }
    }
    fn value(&mut self, tt: &TokTree<'src>) -> Value {
        let t = self.term(tt);
        match &t.op() {
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
                assert!(!ls.is_empty());
                match &ls[..] {
                    [Leaf(Ident, b"mod"), m] => Sort::Field(FieldT::from(self.int(m))),
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
    /// Parse sorts, in-order
    fn sorts(&mut self, tt: &TokTree<'src>) -> Vec<Sort> {
        if let List(tts) = tt {
            tts.iter().map(|tti| self.sort(tti)).collect()
        } else {
            panic!("Expected sort list, found: {}", tt)
        }
    }

    /// Parse this text as an integer, but check the ARC cache before creating a new one.
    fn parse_int(&mut self, s: &[u8]) -> Arc<Integer> {
        let i: Integer = Integer::parse(s).unwrap().into();
        match self.int_arcs.binary_search_by(|v| v.as_ref().cmp(&i)) {
            Ok(idx) => self.int_arcs[idx].clone(),
            Err(idx) => {
                let i = Arc::new(i);
                self.int_arcs.insert(idx, i.clone());
                i
            }
        }
    }
    fn int(&mut self, tt: &TokTree) -> Arc<Integer> {
        match tt {
            Leaf(Token::Int, s) => self.parse_int(s),
            _ => panic!("Expected integer, got {}", tt),
        }
    }
    fn usize(&self, tt: &TokTree) -> usize {
        match tt {
            Leaf(Token::Int, s) => usize::from_str(from_utf8(s).unwrap()).unwrap(),
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
    /// Parse a value list
    fn value_list(&mut self, tt: &TokTree<'src>) -> Vec<Value> {
        self.unwrap_list(tt, "value list")
            .iter()
            .map(|tti| self.value(tti))
            .collect()
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
                        self.parse_int(&s[i + 1..]),
                    )
                } else {
                    let m = self
                        .modulus_stack
                        .last()
                        .unwrap_or_else(|| {
                            panic!("Field value without a modulus, and no default modulus set")
                        })
                        .clone();
                    (Integer::parse(&s[2..]).unwrap().into(), m)
                };
                leaf_term(Op::Const(Value::Field(FieldV::new::<Integer>(v, m))))
            }
            Leaf(Ident, b"false") => bool_lit(false),
            Leaf(Ident, b"true") => bool_lit(true),
            Leaf(Ident, n) => self.get_binding(n).clone(),
            List(tts) => {
                assert!(!tts.is_empty(), "Expected term, got empty list");
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
                            "A decl should have 2 arguments: (declare ((v1 s1) ... (vn sn)) t), found {tts:#?}",
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
                    Err(CtrlOp::ListValue) => {
                        assert_eq!(tts.len(), 3);
                        let key_sort = self.sort(&tts[1]);
                        let vals = self.value_list(&tts[2]);
                        leaf_term(Op::Const(Value::Array(Array::from_vec(
                            key_sort,
                            vals.first().unwrap().sort(),
                            vals,
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
                        let m = self.int(&tts[1]);
                        self.modulus_stack.push(m);
                        let t = self.term(&tts[2]);
                        self.modulus_stack.pop();
                        t
                    }
                    Ok(o) => term(o, tts[1..].iter().map(|tti| self.term(tti)).collect()),
                }
            }
            Leaf(Open | Close | Error, _) => unreachable!("should be caught in tree building"),
        }
    }

    fn string_list(&self, tt: &TokTree<'src>) -> Vec<String> {
        if let List(tts) = tt {
            tts.iter()
                .map(|tti| match tti {
                    Leaf(Token::Ident, name) => from_utf8(name).unwrap().into(),
                    _ => panic!("Expected party, found {}", tti),
                })
                .collect()
        } else {
            panic!("Expected party list, found: {}", tt)
        }
    }

    #[track_caller]
    fn unwrap_list<'a>(&self, tt: &'a TokTree<'src>, err: &str) -> &'a [TokTree<'src>] {
        if let List(tts) = tt {
            tts.as_slice()
        } else {
            panic!("Expected {}, found non-list: {}", err, tt)
        }
    }

    #[track_caller]
    fn unwrap_prefix_list<'a>(&self, tt: &'a TokTree<'src>, prefix: &str) -> &'a [TokTree<'src>] {
        let tts = self.unwrap_list(tt, prefix);
        assert_eq!(
            self.ident_str(&tts[0]),
            prefix,
            "Expected list head '{}', but found {}",
            prefix,
            &tts[0]
        );
        &tts[1..]
    }

    #[track_caller]
    fn ident(&self, tt: &TokTree<'src>) -> &'src [u8] {
        if let Leaf(Token::Ident, i) = tt {
            i
        } else {
            panic!("Expected identifier, found {}", tt)
        }
    }

    #[track_caller]
    fn ident_str(&self, tt: &TokTree<'src>) -> &'src str {
        from_utf8(self.ident(tt)).unwrap()
    }

    #[track_caller]
    fn ident_string(&self, tt: &TokTree<'src>) -> String {
        self.ident_str(tt).to_owned()
    }

    fn variable_metadata_item(&mut self, tt: &TokTree<'src>) -> VariableMetadataItem {
        let tts = self.unwrap_list(tt, "variable metadata item");
        match self.ident(&tts[0]) {
            b"party" => {
                let id = self.int(&tts[1]).to_u8().unwrap();
                VariableMetadataItem::Party(id)
            }
            b"round" => {
                let id = self.int(&tts[1]).to_u8().unwrap();
                VariableMetadataItem::Round(id)
            }
            b"random" => VariableMetadataItem::Random,
            b"committed" => VariableMetadataItem::Committed,
            i => {
                panic!(
                    "Expected variable metadata item, got {}",
                    from_utf8(i).unwrap()
                )
            }
        }
    }

    fn variable_metadata(&mut self, tt: &TokTree<'src>) -> (&'src [u8], VariableMetadata) {
        let tts = self.unwrap_list(tt, "variable metadata");
        let mut md = VariableMetadata {
            name: self.ident_string(&tts[0]),
            sort: self.sort(&tts[1]),
            ..Default::default()
        };
        let name_bytes = self.ident(&tts[0]);
        for tti in &tts[2..] {
            match self.variable_metadata_item(tti) {
                VariableMetadataItem::Party(p) => {
                    md.vis = Some(p);
                }
                VariableMetadataItem::Round(r) => {
                    md.round = r;
                }
                VariableMetadataItem::Random => {
                    md.random = true;
                }
                VariableMetadataItem::Committed => {
                    md.committed = true;
                }
            }
        }
        (name_bytes, md)
    }

    fn commitment(&mut self, tt: &TokTree<'src>) -> Vec<String> {
        let tts = self.unwrap_prefix_list(tt, "commitment");
        tts.iter().map(|tti| self.ident_string(tti)).collect()
    }

    fn commitments(&mut self, tt: &TokTree<'src>) -> Vec<Vec<String>> {
        let tts = self.unwrap_prefix_list(tt, "commitments");
        tts.iter().map(|tti| self.commitment(tti)).collect()
    }

    /// Returns a [ComputationMetadata] and a list of sort bindings to un-bind.
    fn metadata(&mut self, tt: &TokTree<'src>) -> (ComputationMetadata, Vec<Vec<u8>>) {
        let mut md = ComputationMetadata::default();
        let mut unbind = Vec::new();
        if let List(tts) = tt {
            if tts.is_empty() || tts[0] != Leaf(Token::Ident, b"metadata") {
                panic!(
                    "Expected meta-data, but list did not start with 'metadata': {}",
                    tt
                )
            }
            match &tts[1..] {
                [parties, inputs, commitments] => {
                    let parties = self.string_list(parties);
                    for p in parties.into_iter().skip(1) {
                        md.add_party(p);
                    }
                    let tts_inputs = self.unwrap_prefix_list(inputs, "inputs");
                    for tti_input in tts_inputs {
                        let (name_bytes, v_md) = self.variable_metadata(tti_input);
                        self.bind(name_bytes, v_md.term());
                        unbind.push(name_bytes.to_owned());
                        md.new_input_from_meta(v_md);
                    }
                    let parsed_commitments = self.commitments(commitments);
                    for c in parsed_commitments {
                        md.add_commitment(c);
                    }
                    (md, unbind)
                }
                _ => panic!("Expected meta-data, found {}", tt),
            }
        } else {
            panic!("Expected meta-data, found {}", tt)
        }
    }

    /// Parse a computation.
    pub fn computation(&mut self, tt: &TokTree<'src>) -> Computation {
        let tts = self.unwrap_prefix_list(tt, "computation");
        assert!(tts.len() >= 3);
        let (metadata, input_names) = self.metadata(&tts[0]);
        let precomputes = self.precompute(&tts[1]);
        let mut persistent_arrays = Vec::new();
        let mut ram_arrays = Vec::new();
        let mut num_skipped = 0;
        while let List(tts_inner) = &tts[2 + num_skipped] {
            if tts_inner[0] == Leaf(Token::Ident, b"persistent_arrays") {
                for tti in tts_inner.iter().skip(1) {
                    let ttis = self.unwrap_list(tti, "persistent_arrays");
                    let id = self.ident_string(&ttis[0]);
                    let _size = self.usize(&ttis[1]);
                    let term = self.term(&ttis[2]);
                    persistent_arrays.push((id, term));
                }
                num_skipped += 1;
            } else if tts_inner[0] == Leaf(Token::Ident, b"ram_arrays") {
                for tti in tts_inner.iter().skip(1) {
                    let term = self.term(tti);
                    ram_arrays.push(term);
                }
                num_skipped += 1;
            } else {
                break;
            }
        }
        let iter = tts.iter().skip(2 + num_skipped);
        let outputs = iter.map(|tti| self.term(tti)).collect();
        self.unbind(input_names);
        Computation {
            outputs,
            metadata,
            precomputes,
            persistent_arrays,
            ram_arrays: ram_arrays.into_iter().collect(),
        }
    }

    /// Parse a computation set.
    pub fn computations(&mut self, tt: &TokTree<'src>) -> Computations {
        if let List(tts) = tt {
            if tts.is_empty() || tts[0] != Leaf(Token::Ident, b"computations") {
                panic!(
                    "Expected computation set, but list did not start with 'computations': {}",
                    tt
                )
            }
            let mut comps: HashMap<String, Computation> = HashMap::default();
            for tt in &tts[1..] {
                if let List(ls) = tt {
                    match &ls[..] {
                        [Leaf(Token::Ident, var), ctree] => {
                            let name = from_utf8(var).unwrap().to_owned();
                            let c = self.computation(ctree);
                            comps.insert(name, c);
                        }
                        _ => panic!("Expected named computation, found {}", tt),
                    }
                } else {
                    panic!("Expected named computation, found {}", tt);
                }
            }
            Computations { comps }
        } else {
            panic!("Expected computation set, found {}", tt)
        }
    }

    fn var_decl_list(&mut self, tt: &TokTree<'src>) -> Vec<(String, Sort)> {
        let input_names = self.decl_list(tt);
        input_names
            .iter()
            .map(|i| (from_utf8(i).unwrap().into(), check(self.get_binding(i))))
            .collect()
    }

    /// Parse a pre-computation.
    pub fn precompute(&mut self, tt: &TokTree<'src>) -> precomp::PreComp {
        let mut p = precomp::PreComp::new();
        if let List(tts) = tt {
            if tts.is_empty() || tts[0] != Leaf(Token::Ident, b"precompute") {
                panic!(
                    "Expected precompute, but list did not start with 'precompute': {}",
                    tt
                )
            }
            assert!(
                tts.len() == 4,
                "precompute should have 4 children, but has {}",
                tts.len()
            );
            let inputs = self.var_decl_list(&tts[1]);
            let outputs = self.var_decl_list(&tts[2]);
            let tuple_term = self.term(&tts[3]);
            assert!(
                matches!(check(&tuple_term), Sort::Tuple(..)),
                "precompute output term must be a tuple"
            );
            assert!(
                outputs.len() == tuple_term.cs().len(),
                "output list has {} items, tuple has {}",
                outputs.len(),
                tuple_term.cs().len()
            );
            for (n, s) in inputs {
                p.add_input(n, s);
            }
            for ((n, s), t) in outputs.into_iter().zip(tuple_term.cs()) {
                assert_eq!(s, check(t));
                p.add_output(n, t.clone());
            }
            p
        } else {
            panic!("Expected computation, found {}", tt)
        }
    }
}

/// Parse a term.
pub fn parse_term(src: &[u8]) -> Term {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.term(&tree)
}

/// Serialize a term as a parseable string
pub fn serialize_term(t: &Term) -> String {
    format!(
        "{}",
        super::fmt::IrWrapper::new(t, super::fmt::IrCfg::parseable())
    )
}

/// Parse an IR "value map": a map from strings to values.
///
/// A serliazed IR map is a subset of serialized IR terms.  It must have
/// let-bindings for each map entry.  Each entry *must* be bound to a value
/// literal.  Duplicate entries are undefined behavior.
///
/// The value of the term does not matter, and is ignored.
pub fn parse_value_map(src: &[u8]) -> HashMap<String, Value> {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.do_unbinds = false;
    i.term(&tree);
    i.bindings
        .iter()
        .map(|(name, term)| {
            let name = std::str::from_utf8(name).unwrap().to_string();
            let val = match term[0].op() {
                Op::Const(v) => v.clone(),
                _ => panic!("Non-value binding {} associated with {}", term[0], name),
            };
            (name, val)
        })
        .collect()
}

/// Serialize an IR "value map": a map from strings to values.
///
/// See [parse_value_map].
pub fn serialize_value_map(src: &HashMap<String, Value>) -> String {
    let mut out = String::new();
    writeln!(&mut out, "(let (").unwrap();
    for (var, val) in src {
        writeln!(&mut out, "  ({var} {val})").unwrap();
    }
    writeln!(&mut out, ") true;ignored \n)").unwrap();
    out
}

/// Parse a computation.
pub fn parse_computation(src: &[u8]) -> Computation {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.computation(&tree)
}

/// Serialize a computation.
pub fn serialize_computation(c: &Computation) -> String {
    let mut out = String::new();
    writeln!(&mut out, "(computation \n{}", c.metadata).unwrap();
    writeln!(&mut out, "{}", serialize_precompute(&c.precomputes)).unwrap();
    if !c.persistent_arrays.is_empty() {
        writeln!(&mut out, "(persistent_arrays").unwrap();
        for (name, term) in &c.persistent_arrays {
            let size = check(term).as_array().2;
            writeln!(&mut out, "  ({name} {size} {})", serialize_term(term)).unwrap();
        }
        writeln!(&mut out, "\n)").unwrap();
    }
    if !c.ram_arrays.is_empty() {
        writeln!(&mut out, "(ram_arrays").unwrap();
        for term in &c.ram_arrays {
            writeln!(&mut out, "  {}", serialize_term(term)).unwrap();
        }
        writeln!(&mut out, "\n)").unwrap();
    }
    for o in &c.outputs {
        writeln!(&mut out, "\n  {}", serialize_term(o)).unwrap();
    }
    writeln!(&mut out, "\n)").unwrap();
    out
}

/// Parse a computation set.
pub fn parse_computations(src: &[u8]) -> Computations {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.computations(&tree)
}

/// Serialize a computations set.
pub fn serialize_computations(comps: &Computations) -> String {
    let mut out = String::new();
    writeln!(&mut out, "(computations ").unwrap();
    for (n, c) in &comps.comps {
        writeln!(&mut out, "\n({} {}\n)\n", n, serialize_computation(c)).unwrap();
    }
    writeln!(&mut out, "\n)").unwrap();
    out
}

/// Serialize a pre-computation.
pub fn serialize_precompute(p: &precomp::PreComp) -> String {
    let mut out = String::new();
    writeln!(&mut out, "(precompute (").unwrap();
    for (name, sort) in p.inputs() {
        writeln!(&mut out, " ({name} {sort})").unwrap();
    }
    writeln!(&mut out, ")(").unwrap();
    for (name, sort) in p.sequence() {
        writeln!(&mut out, " ({name} {sort})").unwrap();
    }
    writeln!(&mut out, ")").unwrap();
    writeln!(&mut out, "\n  {}", serialize_term(&p.tuple())).unwrap();
    writeln!(&mut out, "\n)").unwrap();
    out
}

/// Parse a pre-computation.
pub fn parse_precompute(src: &[u8]) -> precomp::PreComp {
    let tree = parse_tok_tree(src);
    let mut i = IrInterp::new();
    i.precompute(&tree)
}

#[cfg(test)]
mod test {
    use super::*;

    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;

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

    #[test]
    fn bool_roundtrip() {
        let t = parse_term(b"(declare ((a bool) (b bool)) (let ((c (and a b))) (xor (or (not c) b) c a (=> a b))))");
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[quickcheck]
    fn roundtrip_random_bool(ArbitraryBoolEnv(t, _): ArbitraryBoolEnv) {
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[quickcheck]
    fn roundtrip_random(ArbitraryTermEnv(t, _): ArbitraryTermEnv) {
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn arr_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (a bool)
         (b bool)
         (A (array bool bool 1))
         )
         (let (
                 (B (store A a b))
         ) (xor (select B a)
                (select (#a (bv 4) false 4 ((#b0000 true))) #b0000))))",
        );
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn arr_cstore_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (a bool)
         (b bool)
         (c bool)
         (A (array bool bool 1))
         )
         (let (
                 (B (cstore A a b c))
         ) (xor (select B a)
                (select (#a (bv 4) false 4 ((#b0000 true))) #b0000))))",
        );
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn arr_op_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (a bool)
         (b bool)
         (A (array bool bool 1))
         )
         (= A ((array bool bool) a))
         )",
        );
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn tup_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (a bool)
         (b bool)
         (A (tuple bool bool))
         )
         (let (
                 (B ((update 1) A b))
         ) (xor ((field 1) B)
                ((field 0) (#t false false #b0000 true)))))",
        );
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[quickcheck]
    fn serde_roundtrip_random_bool(ArbitraryBoolEnv(t, _): ArbitraryBoolEnv) {
        let json_string = serde_json::to_string(&t).unwrap();
        let t2 = serde_json::from_str::<Term>(&json_string).unwrap();
        assert_eq!(t, t2);
    }

    #[test]
    fn set_default_modulus() {
        let t = parse_term(
            b"
        (set_default_modulus 7
            (and
                (=
                    (set_default_modulus 11
                        (+ #f1m11 #f5) ; well-type b/c default modulus
                    )
                    #f2m11
                )
                (=
                    #f2 ; default modulus is now 7, so still well-typed
                    #f2m7
                )
            )
        )",
        );
        assert_eq!(check_rec(&t), Sort::Bool);
    }

    #[test]
    fn computation_roundtrip() {
        let c = parse_computation(
            b"
            (computation
                (metadata
                    (parties P V)
                    (inputs
                        (a bool (party 0) (random) (round 1))
                        (b bool)
                        (A (tuple bool bool))
                        (x bool (party 0) (committed))
                    )
                    (commitments)
                )
                (precompute
                    ((c bool) (d bool))
                    ((a bool))
                    (tuple (not (and c d)))
                )
                (let (
                        (B ((update 1) A b))
                ) (xor ((field 1) B)
                        ((field 0) (#t false false #b0000 true))))
            )",
        );
        assert_eq!(c.metadata.vars.len(), 4);
        assert!(!c.metadata.is_input_public("a"));
        assert!(c.metadata.is_input_public("b"));
        assert!(c.metadata.is_input_public("A"));
        assert_eq!(c.outputs().len(), 1);
        assert_eq!(check(&c.outputs()[0]), Sort::Bool);
        let s = serialize_computation(&c);
        let c2 = parse_computation(s.as_bytes());
        assert_eq!(c, c2);
    }

    #[test]
    fn call_roundtrip() {
        let t = parse_term(
            b"
            (declare ((a bool))
                ((field 0) ((call myxor (bool bool) (tuple bool)) a a))
            )",
        );
        assert_eq!(check(&t), Sort::Bool);
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn computations_roundtrip() {
        let c = parse_computations(
            b"
            (computations
                (myxor
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (xor a b false false)
                    )
                )
                (main
                    (computation
                        (metadata (parties ) (inputs (a bool) (b bool)) (commitments))
                        (precompute () () (#t ))
                        (and false ((field 0) ((call myxor (bool bool) (tuple bool)) a b)))
                    )
                )
            )",
        );
        assert_eq!(c.comps.len(), 2);
        assert!(c.comps.contains_key("myxor"));
        assert!(c.comps.contains_key("main"));
        let s = serialize_computations(&c);
        let c2 = parse_computations(s.as_bytes());
        assert_eq!(c, c2);
    }

    #[test]
    fn empty_precompute_roundtrip() {
        let c = parse_precompute(b"(precompute () () (#t ))");
        let s = serialize_precompute(&c);
        let c2 = parse_precompute(s.as_bytes());
        assert_eq!(c, c2);
    }

    #[test]
    fn precompute_roundtrip() {
        let c = parse_precompute(
            b"
                (precompute
                    ((c bool) (d bool))
                    ((a bool) (b bool))
                    (tuple (not (and c d)) (not a))
            )",
        );
        let s = serialize_precompute(&c);
        let c2 = parse_precompute(s.as_bytes());
        assert_eq!(c, c2);
    }

    #[test]
    fn computation_roundtrip_persistent_arrays() {
        let c = parse_computation(
            b"
            (computation
                (metadata
                    (parties P V)
                    (inputs
                        (a bool (party 0) (random) (round 1))
                        (b bool)
                        (A (tuple bool bool))
                        (x bool (party 0) (committed))
                    )
                    (commitments)
                )
                (precompute
                    ((c bool) (d bool))
                    ((a bool))
                    (tuple (not (and c d)))
                )
                (persistent_arrays (AA 2 (#a (bv 4) false 4 ((#b0000 true)))))
                (ram_arrays (#a (bv 4) false 4 ((#b0001 true))))
                (let (
                        (B ((update 1) A b))
                ) (xor ((field 1) B)
                        ((field 0) (#t false false #b0000 true))))
            )",
        );
        let s = serialize_computation(&c);
        let c2 = parse_computation(s.as_bytes());
        assert_eq!(c, c2);
    }

    #[test]
    fn challenge_roundtrip() {
        let t = parse_term(b"(declare ((a bool) (b bool)) ((challenge hithere 17) a b))");
        let s = serialize_term(&t);
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn persistent_ram_split_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (entries (array (mod 17) (tuple (mod 17) (mod 17)) 5))
         (indices (array (mod 17) (mod 17) 3))
        )
         (persistent_ram_split entries indices))",
        );
        let s = serialize_term(&t);
        println!("{s}");
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn list_value_equiv_to_array() {
        let t_array = parse_term(b"(declare () (#a (bv 4) #x0 3 ((#x0 #x0) (#x1 #x1) (#x2 #x4))))");
        let t_list = parse_term(b"(declare () (#l (bv 4) (#x0 #x1 #x4)))");
        assert_eq!(t_array, t_list);
        let s = serialize_term(&t_array);
        let t_roundtripped = parse_term(s.as_bytes());
        assert_eq!(t_array, t_roundtripped);
    }

    #[test]
    fn pf2bool_trusted_rountrip() {
        let t = parse_term(b"(declare ((a bool)) (pf2bool_trusted (ite a #f1m11 #f0m11)))");
        let t2 = parse_term(serialize_term(&t).as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn op_sort_rountrip() {
        let t = parse_term(b"(declare () (sort (#l (mod 3) ((#t true true) (#t true false)))))");
        let t2 = parse_term(serialize_term(&t).as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn fill_roundtrip() {
        let t = parse_term(b"(declare () ((fill (bv 4) 3) #x00))");
        let t2 = parse_term(serialize_term(&t).as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn pf_fits_in_bits_rountrip() {
        let t = parse_term(b"(declare ((a bool)) ((pf_fits_in_bits 4) (ite a #f1m11 #f0m11)))");
        let t2 = parse_term(serialize_term(&t).as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn uniq_deri_gcd_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (pairs (array (mod 17) (tuple (mod 17) bool) 5))
        )
         (uniq_deri_gcd pairs))",
        );
        let s = serialize_term(&t);
        println!("{s}");
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }

    #[test]
    fn haboeck_roundtrip() {
        let t = parse_term(
            b"
        (declare (
         (haystack (array (mod 17) (mod 17) 5))
         (needles (array (mod 17) (mod 17) 8))
        )
         (haboeck haystack needles))",
        );
        let s = serialize_term(&t);
        println!("{s}");
        let t2 = parse_term(s.as_bytes());
        assert_eq!(t, t2);
    }
}
