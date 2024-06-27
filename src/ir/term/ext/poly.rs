//! Operator UniqDeriGcd
//!
//! Given an array of (root, cond) tuples (root is a field element, cond is a boolean),
//! define f(X) = prod_i (cond_i ? X - root_i : 1)
//!
//! Compute f'(X) and s,t s.t. fs + f't = 1. Return an array of coefficients for s and one for t
//! (as a tuple).

use crate::ir::term::ty::*;
use crate::ir::term::*;

/// Type-check [super::ExtOp::UniqDeriGcd].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    let [pairs] = ty::count_or_ref(arg_sorts)?;
    let (size, value) = ty::homogenous_tuple_or(pairs, "UniqDeriGcd")?;
    let [root, cond] = ty::count_or(ty::tuple_or(value, "UniqDeriGcd")?)?;
    let f = pf_or(root, "UniqDeriGcd: first is field")?;
    eq_or(cond, &Sort::Bool, "UniqDeriGcd pairs: second is bool")?;
    let coeffs = Sort::new_tuple(vec![f.clone(); size]);
    Ok(Sort::new_tuple(vec![coeffs.clone(), coeffs]))
}

/// Evaluate [super::ExtOp::UniqDeriGcd].
#[cfg(feature = "poly")]
pub fn eval(args: &[&Value]) -> Value {
    use rug_polynomial::ModPoly;
    let sort = args[0].sort().as_tuple()[0].as_tuple()[0].clone();
    let field = sort.as_pf().clone();
    let mut roots: Vec<Integer> = Vec::new();
    let deg = args[0].as_tuple().len();
    for t in args[0].as_tuple() {
        let tuple = t.as_tuple();
        let cond = tuple[1].as_bool();
        if cond {
            roots.push(tuple[0].as_pf().i());
        }
    }
    let p = ModPoly::with_roots(roots, field.modulus());
    let dp = p.derivative();
    let (g, s, t) = p.xgcd(&dp);
    assert_eq!(g.len(), 1);
    assert_eq!(g.get_coefficient(0), 1);
    let coeff_arr = |s: ModPoly| {
        let v: Vec<Value> = (0..deg)
            .map(|i| Value::Field(field.new_v(s.get_coefficient(i))))
            .collect();
        Value::Tuple(v.into())
    };
    let s_cs = coeff_arr(s);
    let t_cs = coeff_arr(t);
    Value::Tuple(Box::new([s_cs, t_cs]))
}

/// Evaluate [super::ExtOp::UniqDeriGcd].
#[cfg(not(feature = "poly"))]
pub fn eval(_args: &[&Value]) -> Value {
    panic!("Cannot evalute Op::UniqDeriGcd without 'poly' feature")
}
