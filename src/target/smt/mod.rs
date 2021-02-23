use crate::ir::term::*;

use rsmt2::conf::SmtConf;
use rsmt2::errors::SmtRes;
use rsmt2::parse::{IdentParser, ModelParser, SmtParser};
use rsmt2::print::{Expr2Smt, Sort2Smt, Sym2Smt};
use rsmt2::Solver;

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
        <T as Expr2Smt<()>>::expr_to_smt2(&self.0, &mut s, ()).unwrap();
        write!(f, "{}", std::str::from_utf8(&s).unwrap())?;
        Ok(())
    }
}

struct SmtSortDisp<'a, T>(pub &'a T);
impl<'a, T: Sort2Smt + 'a> Display for SmtSortDisp<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut s = Vec::new();
        <T as Sort2Smt>::sort_to_smt2(&self.0, &mut s).unwrap();
        write!(f, "{}", std::str::from_utf8(&s).unwrap())?;
        Ok(())
    }
}

impl Expr2Smt<()> for Value {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        match self {
            Value::Bool(b) => write!(w, "{}", b)?,
            Value::Field(_) => panic!("Can't give fields to SMT solver"),
            Value::Int(i) => write!(w, "{}", i)?,
            Value::BitVector(b) => write!(w, "{}", b)?,
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
            Value::Array(s, default, map, _size) => {
                for _ in 0..map.len() {
                    write!(w, "(store ")?;
                }
                write!(
                    w,
                    "((as const {}) {})",
                    SmtSortDisp(&*s),
                    SmtDisp(&**default)
                )?;
                for (k, v) in map {
                    write!(w, " {} {})", SmtDisp(k), SmtDisp(v))?;
                }
            }
        }
        Ok(())
    }
}

impl Expr2Smt<()> for TermData {
    fn expr_to_smt2<W: Write>(&self, w: &mut W, (): ()) -> SmtRes<()> {
        let s_expr_children = match &self.op {
            Op::Var(n, _) => {
                write!(w, "{}", n)?;
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
                write!(w, "({}", self.op)?;
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
            o => panic!("Cannot give {} to SMT solver", o),
        };
        if s_expr_children {
            for c in &self.cs {
                write!(w, " {}", SmtDisp(&**c))?;
            }
            write!(w, ")")?;
        }
        Ok(())
    }
}

impl Sort2Smt for Sort {
    fn sort_to_smt2<W: Write>(&self, w: &mut W) -> SmtRes<()> {
        match self {
            Sort::BitVector(b) => write!(w, "(_ BitVec {})", b)?,
            Sort::Array(k, v, _size) => {
                write!(w, "(Array {} {})", SmtSortDisp(&**k), SmtSortDisp(&**v))?;
            }
            Sort::F64 => write!(w, "Float64")?,
            Sort::F32 => write!(w, "Float32")?,
            Sort::Bool => write!(w, "Bool")?,
            Sort::Int => write!(w, "Int")?,
            Sort::Field(_) => panic!("Can't give fields to SMT solver"),
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
        _: &Sort,
    ) -> SmtRes<Value> {
        let r = if let Some(b) = input.try_bool()? {
            Value::Bool(b)
        } else if input.try_tag("#b")? {
            let bits = input.get_sexpr()?;
            let i = Integer::from_str_radix(bits, 2).unwrap();
            Value::BitVector(BitVector::new(i, bits.len()))
        } else {
            unimplemented!()
        };
        //if !input.try_tag(")")? {
        //    input.fail_with("No trailing ')'")?;
        //}
        Ok(r)
    }
}

pub fn check_sat(t: &Term) -> bool {
    let mut solver = Solver::default_cvc4(()).unwrap();
    for c in PostOrderIter::new(t.clone()) {
        if let Op::Var(n, s) = &c.op {
            solver.declare_const(&SmtSymDisp(n), s).unwrap();
        }
    }
    assert!(check(t) == Sort::Bool);
    solver.assert(&**t).unwrap();
    solver.check_sat().unwrap()
}

pub fn find_model(t: &Term) -> Option<HashMap<String, Value>> {
    let mut conf = SmtConf::default_cvc4();
    conf.models();
    let mut solver = Solver::new(conf, Parser).unwrap();
    //solver.path_tee("solver_com").unwrap();
    for c in PostOrderIter::new(t.clone()) {
        if let Op::Var(n, s) = &c.op {
            solver.declare_const(&SmtSymDisp(n), s).unwrap();
        }
    }
    assert!(check(t) == Sort::Bool);
    solver.assert(&**t).unwrap();
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

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;
    use rug::Integer;
    use std::collections::HashMap;

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
        assert!(!smt_eval_alternate_solution(t.clone(), &vs));
    }

    /// Check that `t` evaluates consistently within the SMT solver under `vs`.
    pub fn smt_eval_test(t: Term, vs: &HashMap<String, Value>) -> bool {
        let mut solver = Solver::default_cvc4(()).unwrap();
        for (var, val) in vs {
            let s = val.sort();
            solver.declare_const(&SmtSymDisp(&var), &s).unwrap();
            solver.assert(&*term![Op::Eq; leaf_term(Op::Var(var.to_owned(), s)), leaf_term(Op::Const(val.clone()))]).unwrap();
        }
        let val = eval(&t, vs);
        solver
            .assert(&*term![Op::Eq; t, leaf_term(Op::Const(val))])
            .unwrap();
        solver.check_sat().unwrap()
    }

    /// Check that `t` evaluates consistently within the SMT solver under `vs`.
    pub fn smt_eval_alternate_solution(t: Term, vs: &HashMap<String, Value>) -> bool {
        let mut solver = Solver::default_cvc4(()).unwrap();
        for (var, val) in vs {
            let s = val.sort();
            solver.declare_const(&SmtSymDisp(&var), &s).unwrap();
            solver.assert(&*term![Op::Eq; leaf_term(Op::Var(var.to_owned(), s)), leaf_term(Op::Const(val.clone()))]).unwrap();
        }
        let val = eval(&t, vs);
        solver
            .assert(&*term![Op::Not; term![Op::Eq; t, leaf_term(Op::Const(val))]])
            .unwrap();
        solver.check_sat().unwrap()
    }
}
