use crate::ir::term::*;

use rsmt2::errors::SmtRes;
use rsmt2::print::{Expr2Smt, Sort2Smt, Sym2Smt};
use rsmt2::Solver;

use std::fmt::{self, Display, Formatter};
use std::io::Write;

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::term::dist::test::*;
    use quickcheck_macros::quickcheck;
    use std::collections::HashMap;

    #[test]
    fn var_is_sat() {
        let t = leaf_term(Op::Var("a".into(), Sort::Bool));
        assert!(check_sat(&t));
    }
    #[test]
    fn var_and_not_is_unsat() {
        let v = leaf_term(Op::Var("a".into(), Sort::Bool));
        let t = term![Op::BoolNaryOp(BoolNaryOp::And); v.clone(), term![Op::Not; v]];
        assert!(!check_sat(&t));
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
