//! Extra algorithms for hint (precompute) and gadget (sub-circuit) constructions

use crate::cfg::cfg_or_default as cfg;
use crate::ir::term::*;

use super::FloatRewriter;

/// Wrapper for pf_lit
pub fn new_pf_lit<I>(v: I) -> Term
where
    rug::Integer: From<I>,
{
    pf_lit(cfg().field().new_v(v))
}

/// Computes a hint given a (mutable) computation, variable name, and hint function
///
/// Syntax:
///
///    * without children: `compute_hint![COMP, NAME, HINT]`
///    * with children: `compute_hint![COMP, NAME, HINT; ARG0, ARG1, ... ]`
///
/// Returns a variable term associated to a precompute term that can be used in the computation.
#[macro_export]
macro_rules! compute_hint {
    ($comp:expr, $name:expr, $hint_fn:path) => {{
        let hint = $hint_fn();
        let sort = check(&hint);
        $comp.extend_precomputation($name.clone(), hint);
        var($name, sort)
    }};

    ($comp:expr, $name:expr, $hint_fn:path; $($args:expr),+) => {{
        let hint = $hint_fn($($args),+);
        let sort = check(&hint);
        $comp.extend_precomputation($name.clone(), hint);
        var($name, sort)
    }};
}

/// Hints aka nondeterministic advice
///
/// These are unconstrained precompute terms, which _should_ be enforced by other
/// mechanisms in the computation.
pub struct Hint;
/// Frequently used gadgets
pub struct Gadget<'a> {
    pub rewriter: &'a mut FloatRewriter,
}

impl Hint {
    /// Precompute the sign and exponent of a float, together with its pf encoding.
    pub fn decode_float(var: &Term, e_size: usize, m_size: usize) -> Term {
        let var_pf = match var.op() {
            Op::Var(_) => term![Op::FpToPf(cfg().field().clone()); var.clone()],
            _ => panic!("Expected Op::Var but found something else"),
        };
        let var_bv = term![Op::PfToBv(64); var_pf.clone()];

        let s = term![BV_LSHR; var_bv.clone(), bv_lit(e_size + m_size, 64)];
        let shifted_v = term![BV_LSHR; var_bv.clone(), bv_lit(m_size, 64)];
        let shifted_s = term![BV_SHL; s.clone(), bv_lit(e_size, 64)];
        let e = term![BV_SUB; shifted_v, shifted_s];

        term![
            Op::Tuple;
            term![Op::UbvToPf(Box::new(cfg().field().clone())); s],
            term![Op::UbvToPf(Box::new(cfg().field().clone())); e],
            var_pf
        ]
    }
    /// Precompute the number of leading zeros of mantissa within m_size bits
    pub fn normalize(var: &Term, m_size: usize) -> Term {
        let mantissa = term![Op::PfToBv(m_size); var.clone()];

        let mut d = bv_lit(0, m_size);
        // shift length is number of zeros
        // d := ite (bit == 0) (d + 1) (d)
        for i in (0..m_size).rev() {
            let bit = term![Op::BvBit(i); mantissa.clone()];
            let cond = term![EQ; bit, bool_lit(false)];
            d = term![ITE; cond, term![BV_ADD; d.clone(), bv_lit(1, m_size)], d.clone()]
        }

        // if mantissa is zero, return zero, else return computed shift
        let is_zero = term![EQ; mantissa.clone(), bv_lit(0, m_size)];
        term![ITE; is_zero, new_pf_lit(0), term![Op::UbvToPf(Box::new(cfg().field().clone())); d.clone()]]
    }
    // /// Precompute the power of two of a given pf term.
    // pub fn power_of_two(var: &Term) -> Term {
    //     // maybe set the size to m_size. come back to this later.
    //     let d = term![Op::PfToBv(64); var.clone()];
    //     term![Op::UbvToPf(Box::new(cfg().field().clone())); term![BV_SHL; bv_lit(1, 64), d]]
    // }
}

impl Gadget<'_> {
    pub fn assert(&mut self, cond: Term) {
        self.rewriter.assertions.push(cond);
    }

    // /// TODO: implement lookup-related machinery
    // pub fn query_power_of_two(&self, comp: &mut Computation, exp: &Term) -> Term {
    //     // Precompute the power of two of the exponent
    //     let res = compute_hint!(
    //         comp,
    //         Hint::power_of_two(exp),
    //         format!("{}.pow2", exp.as_var_name())
    //     );

    //     // continue here...
    //     res
    // }

    /// Creates a bool term checking if pf term is 1 or 0
    pub fn is_bool(&self, a: &Term) -> Term {
        // compute a*(1-a) == 0
        self.is_zero(&term![PF_MUL; a.clone(), self.pf_sub(&new_pf_lit(1), a)])
    }

    /// Creates a bool term checking if pf term a is zero
    pub fn is_zero(&self, a: &Term) -> Term {
        term![EQ; a.clone(), new_pf_lit(0)]
    }

    /// Creates a pf term subtracting pf term b from pf term a
    pub fn pf_sub(&self, a: &Term, b: &Term) -> Term {
        term![PF_ADD; a.clone(), term![PF_NEG; b.clone()]]
    }
}
