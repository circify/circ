//! The SMT back-end.
//!
//!
//! The SMT solver's invocation command can be configured by setting the environmental variable
//! [rsmt2::conf::CVC4_ENV_VAR].

use crate::ir::term::*;

use rsmt2::errors::SmtRes;
use rsmt2::parse::{IdentParser, ModelParser, SmtParser};
use rsmt2::print::{Expr2Smt, Sort2Smt, Sym2Smt};

use rug::Integer;

use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::io::Write;
use std::str::FromStr;

use ieee754::Ieee754;

struct SmtDisp<'a, T>(pub &'a T);

impl<'a, T: Expr2Smt<()> + 'a> Display for SmtDisp<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut s = Vec::new();
        <T as Expr2Smt<()>>::expr_to_smt2(self.0, &mut s, ()).unwrap();
        write!(f, "{}", std::str::from_utf8(&s).unwrap())?;
        Ok(())
    }
}

struct SmtSortDisp<'a, T>(pub &'a T);
impl<'a, T: Sort2Smt + 'a> Display for SmtSortDisp<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut s = Vec::new();
        <T as Sort2Smt>::sort_to_smt2(self.0, &mut s).unwrap();
        write!(f, "{}", std::str::from_utf8(&s).unwrap())?;
        Ok(())
    }
}

impl Expr2Smt<()> for Value {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        match self {
            Value::Bool(b) => write!(w, "{b}")?,
            Value::Field(f) => write!(w, "#f{}m{}", f.i(), f.modulus())?,
            Value::Int(i) if i >= &Integer::new() => write!(w, "{i}")?,
            Value::Int(i) => write!(w, "(- 0 {})", *i.as_neg())?,
            Value::BitVector(b) => write!(w, "{b}")?,
            Value::F32(f) => {
                let (sign, exp, mant) = f.decompose_raw();
                write!(w, "(fp #b{} #b", sign as u8)?;
                for i in (0..8).rev() {
                    write!(w, "{}", (exp >> i) & 1)?;
                }
                write!(w, " #b")?;
                for i in (0..23).rev() {
                    write!(w, "{}", (mant >> i) & 1)?;
                }
                write!(w, ")")?;
            }
            Value::F64(f) => {
                let (sign, exp, mant) = f.decompose_raw();
                write!(w, "(fp #b{} #b", sign as u8)?;
                for i in (0..11).rev() {
                    write!(w, "{}", (exp >> i) & 1)?;
                }
                write!(w, " #b")?;
                for i in (0..52).rev() {
                    write!(w, "{}", (mant >> i) & 1)?;
                }
                write!(w, ")")?;
            }
            Value::Array(Array {
                key_sort,
                default,
                map,
                size,
            }) => {
                for _ in 0..map.len() {
                    write!(w, "(store ")?;
                }
                let val_s = check(&leaf_term(Op::Const((**default).clone())));
                let s = Sort::Array(Box::new(key_sort.clone()), Box::new(val_s), *size);
                write!(
                    w,
                    "((as const {}) {})",
                    SmtSortDisp(&s),
                    SmtDisp(&**default)
                )?;
                for (k, v) in map {
                    write!(w, " {} {})", SmtDisp(k), SmtDisp(v))?;
                }
            }
            Value::Tuple(fs) => {
                write!(w, "(mkTuple")?;
                for t in fs.iter() {
                    write!(w, " {}", SmtDisp(t))?;
                }
                write!(w, ")")?;
            }
        }
        Ok(())
    }
}

impl Expr2Smt<()> for Term {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        let s_expr_children = match &self.op() {
            Op::Var(n, _) => {
                write!(w, "{n}")?;
                false
            }
            Op::Eq => {
                write!(w, "(=")?;
                true
            }
            Op::Ite => {
                write!(w, "(ite")?;
                true
            }
            Op::Not => {
                write!(w, "(not")?;
                true
            }
            Op::Implies => {
                write!(w, "(=>")?;
                true
            }
            Op::BoolNaryOp(_) | Op::BvBinPred(_) | Op::BvBinOp(_) | Op::BvNaryOp(_) => {
                write!(w, "({}", self.op())?;
                true
            }
            Op::BvUext(s) => {
                write!(w, "((_ zero_extend {s})")?;
                true
            }
            Op::Const(c) => {
                write!(w, "{}", SmtDisp(c))?;
                false
            }
            Op::Store => {
                write!(w, "(store")?;
                true
            }
            Op::Select => {
                write!(w, "(select")?;
                true
            }
            Op::Tuple => {
                write!(w, "(mkTuple")?;
                true
            }
            Op::Field(i) => {
                write!(w, "((_ tupSel {i})")?;
                true
            }
            Op::PfNaryOp(PfNaryOp::Mul) => {
                write!(w, "(ff.mul")?;
                true
            }
            Op::PfNaryOp(PfNaryOp::Add) => {
                write!(w, "(ff.add")?;
                true
            }
            Op::PfUnOp(PfUnOp::Neg) => {
                write!(w, "(ff.neg")?;
                true
            }
            Op::IntNaryOp(IntNaryOp::Mul) => {
                write!(w, "(*")?;
                true
            }
            Op::IntNaryOp(IntNaryOp::Add) => {
                write!(w, "(+")?;
                true
            }
            Op::IntBinPred(o) => {
                write!(w, "({o}")?;
                true
            }
            o => panic!("Cannot give {} to SMT solver", o),
        };
        if s_expr_children {
            for c in self.cs() {
                write!(w, " {}", SmtDisp(c))?;
            }
            write!(w, ")")?;
        }
        Ok(())
    }
}

impl Sort2Smt for Sort {
    fn sort_to_smt2<W: Write>(&self, w: &mut W) -> SmtRes<()> {
        match self {
            Sort::BitVector(b) => write!(w, "(_ BitVec {b})")?,
            Sort::Array(k, v, _size) => {
                write!(w, "(Array {} {})", SmtSortDisp(&**k), SmtSortDisp(&**v))?;
            }
            Sort::F64 => write!(w, "Float64")?,
            Sort::F32 => write!(w, "Float32")?,
            Sort::Bool => write!(w, "Bool")?,
            Sort::Int => write!(w, "Int")?,
            Sort::Tuple(fs) => {
                write!(w, "(Tuple")?;
                for t in fs.iter() {
                    write!(w, " {}", SmtSortDisp(t))?;
                }
                write!(w, ")")?;
            }
            Sort::Field(f) => write!(w, "(_ FiniteField {})", f.modulus())?,
        }
        Ok(())
    }
}

impl Expr2Smt<()> for BitVector {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        write!(w, "#b")?;
        for i in (0..self.width()).rev() {
            write!(w, "{}", self.uint().get_bit(i as u32) as u8)?;
        }
        Ok(())
    }
}

struct SmtSymDisp<'a, T>(pub &'a T);

impl<'a, T: Display + 'a> Sym2Smt<()> for SmtSymDisp<'a, T> {
    fn sym_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        write!(w, "{}", self.0)?;
        Ok(())
    }
}

#[derive(Clone, Copy)]
struct Parser;

impl<'a, R: std::io::BufRead> IdentParser<String, Sort, &'a mut SmtParser<R>> for Parser {
    fn parse_ident(self, input: &'a mut SmtParser<R>) -> SmtRes<String> {
        Ok(input
            .try_sym(|a| -> Result<String, String> { Ok(a.to_owned()) })?
            .expect("sym"))
    }
    fn parse_type(self, input: &'a mut SmtParser<R>) -> SmtRes<Sort> {
        if input.try_tag("Bool")? {
            Ok(Sort::Bool)
        } else if input.try_tag("Int")? {
            Ok(Sort::Int)
        } else if input.try_tag("(_ BitVec")? {
            let n = input
                .try_int(|s, b| {
                    if b {
                        Ok(usize::from_str(s).unwrap())
                    } else {
                        Err("Non-positive bit-vector width")
                    }
                })?
                .unwrap();
            input.tag(")")?;
            Ok(Sort::BitVector(n))
        } else if input.try_tag("(_ FiniteField")? {
            let n = input
                .try_int(|s, b| {
                    if b {
                        Ok(rug::Integer::from_str_radix(s, 10).unwrap())
                    } else {
                        Err("Non-positive finite field size")
                    }
                })?
                .unwrap();
            input.tag(")")?;
            Ok(Sort::Field(circ_fields::FieldT::from(n)))
        } else {
            unimplemented!()
        }
    }
}

impl<'a, Br: ::std::io::BufRead> ModelParser<String, Sort, Value, &'a mut SmtParser<Br>>
    for Parser
{
    fn parse_value(
        self,
        input: &'a mut SmtParser<Br>,
        _: &String,
        _: &[(String, Sort)],
        s: &Sort,
    ) -> SmtRes<Value> {
        let r = if let Some(b) = input.try_bool()? {
            Value::Bool(b)
        } else if input.try_tag("#b")? {
            let bits = input.get_sexpr()?;
            let i = Integer::from_str_radix(bits, 2).unwrap();
            Value::BitVector(BitVector::new(i, bits.len()))
        } else if input.try_tag("(_")? {
            if input.try_tag("bv")? {
                let val = Integer::from_str_radix(input.get_sexpr()?, 10).unwrap();
                let width = usize::from_str(input.get_sexpr()?).unwrap();
                input.tag(")")?;
                Value::BitVector(BitVector::new(val, width))
            } else {
                unimplemented!(
                    "Could not parse model suffix: {}\n after (_ bv",
                    input.buff_rest()
                )
            }
        } else if let Sort::Field(f) = s {
            let int_literal = input.get_sexpr()?;
            let i = Integer::from_str_radix(int_literal, 10).unwrap();
            Value::Field(f.new_v(i))
        } else if let Sort::Int = s {
            let int_literal = input.get_sexpr()?;
            let i = Integer::from_str_radix(int_literal, 10).unwrap();
            Value::Int(i)
        } else {
            unimplemented!("Could not parse model suffix: {}", input.buff_rest())
        };
        //if !input.try_tag(")")? {
        //    input.fail_with("No trailing ')'")?;
        //}
        Ok(r)
    }
}

/// Create a solver, which can optionally parse models.
///
/// If [rsmt2::conf::CVC4_ENV_VAR] is set, uses that as the solver's invocation command.
fn make_solver<P>(parser: P, models: bool, inc: bool) -> rsmt2::Solver<P> {
    let mut conf = rsmt2::conf::SmtConf::default_cvc4();
    if let Ok(val) = std::env::var(rsmt2::conf::CVC4_ENV_VAR) {
        conf.cmd(val);
    }
    if models {
        conf.models();
    }
    conf.set_incremental(inc);
    rsmt2::Solver::new(conf, parser).expect("Error creating SMT solver")
}

/// Write SMT2 the encodes this terms satisfiability to a file
pub fn write_smt2<W: Write>(mut w: W, t: &Term) {
    for c in PostOrderIter::new(t.clone()) {
        if let Op::Var(n, s) = &c.op() {
            write!(w, "(declare-const ").unwrap();
            SmtSymDisp(n).sym_to_smt2(&mut w, ()).unwrap();
            write!(w, " ").unwrap();
            s.sort_to_smt2(&mut w).unwrap();
            writeln!(w, ")").unwrap();
        }
    }
    assert!(check(t) == Sort::Bool);
    write!(w, "(assert\n\t").unwrap();
    t.expr_to_smt2(&mut w, ()).unwrap();
    writeln!(w, "\n)").unwrap();
    writeln!(w, "(check-sat)").unwrap();
}

/// Check whether some term is satisfiable.
pub fn check_sat(t: &Term) -> bool {
    let mut solver = make_solver((), false, false);
    for c in PostOrderIter::new(t.clone()) {
        if let Op::Var(n, s) = &c.op() {
            solver.declare_const(&SmtSymDisp(n), s).unwrap();
        }
    }
    assert!(check(t) == Sort::Bool);
    solver.assert(t).unwrap();
    solver.check_sat().unwrap()
}

fn get_model_solver(t: &Term, inc: bool) -> rsmt2::Solver<Parser> {
    let mut solver = make_solver(Parser, true, inc);
    //solver.path_tee("solver_com").unwrap();
    for c in PostOrderIter::new(t.clone()) {
        if let Op::Var(n, s) = &c.op() {
            solver.declare_const(&SmtSymDisp(n), s).unwrap();
        }
    }
    assert!(check(t) == Sort::Bool);
    solver
}

/// Get a satisfying assignment for `t`, assuming it is SAT.
pub fn find_model(t: &Term) -> Option<HashMap<String, Value>> {
    let mut solver = get_model_solver(t, false);
    solver.assert(t).unwrap();
    if solver.check_sat().unwrap() {
        Some(
            solver
                .get_model()
                .unwrap()
                .into_iter()
                .map(|(id, _, _, v)| (id, v))
                .collect(),
        )
    } else {
        None
    }
}

/// Get a unique satisfying assignment for `t`, assuming it is SAT.
pub fn find_unique_model(t: &Term, uniqs: Vec<String>) -> Option<HashMap<String, Value>> {
    let mut solver = get_model_solver(t, true);
    solver.assert(t).unwrap();
    // first, get the result
    let model: HashMap<String, Value> = if solver.check_sat().unwrap() {
        solver
            .get_model()
            .unwrap()
            .into_iter()
            .map(|(id, _, _, v)| (id, v))
            .collect()
    } else {
        return None;
    };
    // now, assert that any value in uniq is not the value assigned and check unsat
    match uniqs
        .into_iter()
        .flat_map(|n| {
            model
                .get(&n)
                .map(|v| term![EQ; term![Op::Var(n, v.sort())], term![Op::Const(v.clone())]])
        })
        .reduce(|l, r| term![AND; l, r])
        .map(|t| term![NOT; t])
    {
        None => Some(model),
        Some(ast) => {
            solver.push(1).unwrap();
            solver.assert(&ast).unwrap();
            match solver.check_sat().unwrap() {
                true => None,
                false => Some(model),
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use fxhash::FxHashMap as HashMap;
    use quickcheck_macros::quickcheck;
    use rug::Integer;

    #[test]
    fn var_is_sat() {
        let t = leaf_term(Op::Var("a".into(), Sort::Bool));
        assert!(check_sat(&t));
    }

    #[test]
    fn var_is_sat_model() {
        let t = leaf_term(Op::Var("a".into(), Sort::Bool));
        assert!(
            find_model(&t)
                == Some(
                    vec![("a".to_owned(), Value::Bool(true))]
                        .into_iter()
                        .collect()
                )
        );
    }

    #[test]
    fn var_and_not_is_unsat() {
        let v = leaf_term(Op::Var("a".into(), Sort::Bool));
        let t = term![Op::BoolNaryOp(BoolNaryOp::And); v.clone(), term![Op::Not; v]];
        assert!(!check_sat(&t));
    }

    #[test]
    fn bv_is_sat() {
        let t = term![Op::Eq; bv_lit(0,4), leaf_term(Op::Var("a".into(), Sort::BitVector(4)))];
        assert!(check_sat(&t));
    }

    // ignored until FF support in cvc5 is upstreamed.
    #[ignore]
    #[test]
    fn ff_is_sat() {
        let t = text::parse_term(
            b"
        (declare ((a (mod 5)) (b (mod 5)))
            (and
                (= (* a a) a)
                (= (* b b) b)
                (= a b)
                (= a #f1m5)
            )
        )
        ",
        );
        assert!(check_sat(&t));
    }

    // ignored until FF support in cvc5 is upstreamed.
    #[ignore]
    #[test]
    fn ff_model() {
        let t = text::parse_term(
            b"
        (declare ((a (mod 5)) (b (mod 5)))
            (and
                (= (* a a) a)
                (= (* b b) b)
                (= a b)
                (= a #f1m5)
            )
        )
        ",
        );
        let field = circ_fields::FieldT::from(rug::Integer::from(5));
        assert_eq!(
            find_model(&t),
            Some(
                vec![
                    ("a".to_owned(), Value::Field(field.new_v(1)),),
                    ("b".to_owned(), Value::Field(field.new_v(1)),),
                ]
                .into_iter()
                .collect()
            )
        )
    }

    #[test]
    fn tuple_is_sat() {
        let t = term![Op::Eq; term![Op::Field(0); term![Op::Tuple; bv_lit(0,4), bv_lit(5,6)]], leaf_term(Op::Var("a".into(), Sort::BitVector(4)))];
        assert!(check_sat(&t));
        let t = term![Op::Eq; term![Op::Tuple; bv_lit(0,4), bv_lit(5,6)], leaf_term(Op::Var("a".into(), Sort::Tuple(vec![Sort::BitVector(4), Sort::BitVector(6)].into_boxed_slice())))];
        assert!(check_sat(&t));
    }

    #[test]
    fn bv_is_sat_model() {
        let t = term![Op::Eq; bv_lit(0,4), leaf_term(Op::Var("a".into(), Sort::BitVector(4)))];
        assert!(
            find_model(&t)
                == Some(
                    vec![(
                        "a".to_owned(),
                        Value::BitVector(BitVector::new(Integer::from(0), 4))
                    ),]
                    .into_iter()
                    .collect()
                )
        );
    }

    #[test]
    fn vars_are_sat_model() {
        let t = term![Op::BoolNaryOp(BoolNaryOp::And);
           leaf_term(Op::Var("a".into(), Sort::Bool)),
           leaf_term(Op::Var("b".into(), Sort::Bool)),
           leaf_term(Op::Var("c".into(), Sort::Bool))
        ];
        assert!(
            find_model(&t)
                == Some(
                    vec![
                        ("a".to_owned(), Value::Bool(true)),
                        ("b".to_owned(), Value::Bool(true)),
                        ("c".to_owned(), Value::Bool(true)),
                    ]
                    .into_iter()
                    .collect()
                )
        );
    }

    #[quickcheck]
    fn eval_random_bool(ArbitraryBoolEnv(t, vs): ArbitraryBoolEnv) {
        assert!(smt_eval_test(t.clone(), &vs));
        assert!(!smt_eval_alternate_solution(t, &vs));
    }

    /// Check that `t` evaluates consistently within the SMT solver under `vs`.
    pub fn smt_eval_test(t: Term, vs: &HashMap<String, Value>) -> bool {
        let mut solver = make_solver((), false, false);
        for (var, val) in vs {
            let s = val.sort();
            solver.declare_const(&SmtSymDisp(&var), &s).unwrap();
            solver.assert(&term![Op::Eq; leaf_term(Op::Var(var.to_owned(), s)), leaf_term(Op::Const(val.clone()))]).unwrap();
        }
        let val = eval(&t, vs);
        solver
            .assert(&term![Op::Eq; t, leaf_term(Op::Const(val))])
            .unwrap();
        solver.check_sat().unwrap()
    }

    /// Check that `t` evaluates consistently within the SMT solver under `vs`.
    pub fn smt_eval_alternate_solution(t: Term, vs: &HashMap<String, Value>) -> bool {
        let mut solver = make_solver((), false, false);
        for (var, val) in vs {
            let s = val.sort();
            solver.declare_const(&SmtSymDisp(&var), &s).unwrap();
            solver.assert(&term![Op::Eq; leaf_term(Op::Var(var.to_owned(), s)), leaf_term(Op::Const(val.clone()))]).unwrap();
        }
        let val = eval(&t, vs);
        solver
            .assert(&term![Op::Not; term![Op::Eq; t, leaf_term(Op::Const(val))]])
            .unwrap();
        solver.check_sat().unwrap()
    }

    #[test]
    fn int_model() {
        let t = text::parse_term(
            b"
        (declare ((a int) (b int))
            (and
                (or (= (intadd a b) 1)
                    (= (intadd a b) 0))
                (< a 1)
                (> 1 b)
                (>= a 0)
                (<= 0 b)
            )
        )
        ",
        );
        assert_eq!(
            find_model(&t),
            Some(
                vec![
                    ("a".to_owned(), Value::Int(0.into())),
                    ("b".to_owned(), Value::Int(0.into())),
                ]
                .into_iter()
                .collect()
            )
        )
    }

    #[test]
    fn int_no_model() {
        let t = text::parse_term(
            b"
        (declare ((a int) (b int))
            (and
                (or (= (intadd a b) 1)
                    (= (intadd a b) 1))
                (< a 1)
                (> 1 b)
                (>= a 0)
                (<= 0 b)
            )
        )
        ",
        );
        assert_eq!(find_model(&t), None)
    }

    #[test]
    fn int_model_nia() {
        let t = text::parse_term(
            b"
        (declare ((a int) (b int))
            (and
                (= (intmul a a) b)
                (= (intmul b b) a)
                (not (= a 0))
            )
        )
        ",
        );
        assert_eq!(
            find_model(&t),
            Some(
                vec![
                    ("a".to_owned(), Value::Int(1.into())),
                    ("b".to_owned(), Value::Int(1.into())),
                ]
                .into_iter()
                .collect()
            )
        )
    }

    #[test]
    fn int_model_div() {
        let t = text::parse_term(
            b"
        (declare ((a int) (q int) (r int))
            (and
                (= a (intadd (intmul q 5) r))
                (>= r 0)
                (< r 5)
                (= (intadd a (intmul -1 r)) 10)
                (>= a 14)
            )
        )
        ",
        );
        assert_eq!(
            find_model(&t),
            Some(
                vec![
                    ("a".to_owned(), Value::Int(14.into())),
                    ("r".to_owned(), Value::Int(4.into())),
                    ("q".to_owned(), Value::Int(2.into())),
                ]
                .into_iter()
                .collect()
            )
        )
    }

    #[test]
    fn bv_model_div() {
        let t = text::parse_term(
            b"
        (declare ((a (bv 8)) (q (bv 8)) (r (bv 8)))
            (and
                (= a (bvadd (bvmul q #x05) r))
                (bvuge r #x00)
                (bvult r #x05)
                (= (bvsub a r) #x0a)
                (bvuge a #x0e)
            )
        )
        ",
        );
        assert_eq!(
            find_model(&t),
            Some(
                vec![
                    (
                        "a".to_owned(),
                        Value::BitVector(BitVector::new(Integer::from(14), 8))
                    ),
                    (
                        "r".to_owned(),
                        Value::BitVector(BitVector::new(Integer::from(4), 8))
                    ),
                    (
                        "q".to_owned(),
                        Value::BitVector(BitVector::new(Integer::from(2), 8))
                    ),
                ]
                .into_iter()
                .collect()
            )
        )
    }

    #[test]
    fn bv_model_uext() {
        let t = text::parse_term(
            b"
        (declare ((a (bv 8)))
            (= a ((uext 6) #b10))
        )
        ",
        );
        assert_eq!(
            find_model(&t),
            Some(
                vec![(
                    "a".to_owned(),
                    Value::BitVector(BitVector::new(Integer::from(2), 8))
                ),]
                .into_iter()
                .collect()
            )
        )
    }
}
