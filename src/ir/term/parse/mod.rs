use logos::{Logos, Span};

use fxhash::FxHashMap as HashMap;

mod lex;

use lex::Token;
use std::fmt::{self, Debug, Display, Formatter};
use std::str::{FromStr, from_utf8};
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
pub fn parse_tok_tree(bytes: &[u8]) -> TokTree {
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

pub struct IrInterp<'src> {
    src: &'src [u8],
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
    pub fn new(src: &'src [u8]) -> Self {
        Self {
            src,
            moduli: Vec::new(),
            bindings: HashMap::default(),
        }
    }

    pub fn span_bytes(&self, span: Span) -> &'src [u8] {
        &self.src[span]
    }

    pub fn span_str(&self, span: Span) -> &'src str {
        std::str::from_utf8(self.span_bytes(span)).unwrap()
    }

    /// Takes bindings in order bound, and unbinds
    pub fn unbind(&mut self, bindings: Vec<Vec<u8>>) {
        for b in bindings {
            self.bindings.get_mut(b.as_slice()).unwrap().pop().unwrap();
        }
    }

    pub fn op(&mut self, tt: &TokTree) -> Result<Op, CtrlOp> {
        use Token::Ident;
        match tt {
            Leaf(Ident, b"let") => Err(CtrlOp::Let),
            Leaf(Ident, b"declare") => Err(CtrlOp::Declare),
            Leaf(Ident, b"tuple_value") => Err(CtrlOp::TupleValue),
            Leaf(Ident, b"array_value") => Err(CtrlOp::ArrayValue),
            Leaf(Ident, b"set_default_modulus") => Err(CtrlOp::SetDefaultModulus),
            _ => todo!("Unparsed op: {}", tt),
        }
    }
    pub fn value(&mut self, tt: &TokTree) -> Value {
        let t = self.term(tt);
        match &t.op {
            Op::Const(v) => v.clone(),
            _ => panic!("Expected value, found term {}", t),
        }
    }
    pub fn sort(&mut self, tt: &TokTree) -> Sort {
        use Token::Ident;
        match tt {
            Leaf(Ident, b"bool") => Sort::Bool,
            Leaf(Ident, b"int") => Sort::Int,
            Leaf(Ident, b"f32") => Sort::F32,
            Leaf(Ident, b"f64") => Sort::F64,
            List(ls) => {
                assert!(ls.len() > 0);
                match &ls[..] {
                    [Leaf(Ident, b"field"), m] => Sort::Field(Arc::new(self.int(m))),
                    [Leaf(Ident, b"bv"), w] => Sort::BitVector(self.usize(w)),
                    [Leaf(Ident, b"array"), k, v, s] => Sort::Array(
                        Box::new(self.sort(k)),
                        Box::new(self.sort(v)),
                        self.usize(s),
                    ),
                    [Leaf(Ident, b"tuple"), ..] => Sort::Tuple(
                        ls[1..].iter().map(|li| self.sort(li)).collect()
                    ),
                    _ => panic!("Expected sort, found {}", tt),
                }
            }
            _ => panic!("Expected sort, found {}", tt),
        }
    }
    pub fn int(&mut self, tt: &TokTree) -> Integer {
        match tt {
            Leaf(Token::Int, s) => {
                Integer::parse(s).unwrap().into()
            }
            _ => panic!("Expected integer, got {}", tt),
        }
    }
    pub fn usize(&mut self, tt: &TokTree) -> usize {
        match tt {
            Leaf(Token::Int, s) => {
                usize::from_str(from_utf8(s).unwrap()).unwrap().into()
            }
            _ => panic!("Expected integer, got {}", tt),
        }
    }
    /// Parse lets, returning bindings, in-order.
    pub fn let_list(&mut self, tt: &TokTree) -> Vec<Vec<u8>> {
        todo!()
    }
    /// Parse declarations, returning bindings, in-order.
    pub fn decl_list(&mut self, tt: &TokTree) -> Vec<Vec<u8>> {
        todo!()
    }
    pub fn term(&mut self, tt: &TokTree) -> Term {
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
            Leaf(Ident, n) => self
                .bindings
                .get(n)
                .and_then(|v| v.last())
                .unwrap_or_else(|| panic!("No binding for {}", tt))
                .clone(),
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
                        todo!()
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
        }
    }
}
