//! Floating-point IEEE-754 constructions
//!
//! Replace IR floats with their respective constructions using lookup arguments.
//! The floats themselves are stored as a tuple of components.
//!
//! A tuple elimination pass should be run afterwards.
//! Based on the implementation of https://github.com/tumberger/zk-Location

mod extras;

use super::visit::RewritePass;
use crate::cfg::cfg_or_default as cfg;
use crate::compute_hint;
use crate::ir::term::*;
use extras::{new_pf_lit, Gadget, Hint};
// use lookup::{lookup_exponent, lookup_mantissa};
use rug::Integer;

/// Represents an IEEE-754 floating-point number
#[allow(dead_code)]
struct FloatVar {
    sign: Term,
    exponent: Term,
    mantissa: Term,
    is_abnormal: Term,
}

// Context
#[derive(Debug, Clone)]
#[allow(dead_code)]
struct Context {
    e: usize, // Exponent bit width
    m: usize, // Mantissa bit width
    e_max: Integer,
    e_normal_min: Integer,
    e_min: Integer,
}

#[allow(dead_code)]
impl Context {
    pub fn new(e: usize, m: usize) -> Self {
        let e_max = Integer::from(1) << (e - 1);
        let e_normal_min = Integer::from(2) - &e_max;
        let e_min = e_normal_min.clone() - (m + 1);

        Self {
            e,
            m,
            e_max,
            e_normal_min,
            e_min,
        }
    }

    fn components_of(&self, v: u64) -> (Integer, Integer, Integer, Integer) {
        let s = v >> (self.e + self.m);
        let e = (v >> self.m) - (s << self.e);
        let m = v - (s << (self.e + self.m)) - (e << self.m);

        let sign = Integer::from(s as i64);

        let exponent_max = Integer::from(1) << (self.e - 1);
        let exponent_min = Integer::from(1) - &exponent_max;

        let mut exponent = Integer::from(e as i64) + &exponent_min;
        let mut mantissa = Integer::from(m as i64);
        let mut shift = 0_usize;

        for i in (0..self.m).rev() {
            if ((m >> (self.m - 1 - i)) & 1) == 1 {
                break;
            }
            shift += 1;
        }

        let mantissa_is_not_zero = m != 0;
        let exponent_is_min = exponent == exponent_min;
        let exponent_is_max = exponent == exponent_max;

        if exponent_is_min {
            exponent -= Integer::from(shift as i64);
            mantissa <<= shift + 1;
        } else if exponent_is_max && mantissa_is_not_zero {
            mantissa = Integer::from(0);
        } else {
            mantissa += Integer::from(1) << self.m;
        }

        let is_abnormal = if exponent_is_max {
            Integer::from(1)
        } else {
            Integer::from(0)
        };

        (sign, exponent, mantissa, is_abnormal)
    }

    pub fn new_f32_constant(&self, v: f32) -> (Integer, Integer, Integer, Integer) {
        self.components_of(v.to_bits() as u64)
    }

    pub fn new_f64_constant(&self, v: f64) -> (Integer, Integer, Integer, Integer) {
        self.components_of(v.to_bits())
    }
}

#[derive(Default)]
struct FloatRewriter {
    assertions: Vec<Term>,
}

impl RewritePass for FloatRewriter {
    fn traverse(&mut self, computation: &mut Computation) {
        self.traverse_full(computation, false, true);

        // Apply all stored assertions at the end
        for assertion in self.assertions.drain(..) {
            computation.assert(assertion);
        }
    }

    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        _rewritten_children: F,
    ) -> Option<Term> {
        let mut gadget = Gadget { rewriter: self };

        match &orig.op() {
            // Destructures float variables into constrained tuples of (s: bool, e: field, m: field, a: bool).
            Op::Var(v) => {
                let ctx = match v.sort {
                    Sort::F32 => Context::new(8, 23),
                    Sort::F64 => Context::new(11, 52),
                    _ => todo!(),
                };

                // Precompute the float components
                let fp_tup = compute_hint![
                    computation,
                    format!("{}.fp_tup", v.name),
                    Hint::decode_float;
                    orig,
                    ctx.e,
                    ctx.m
                ];
                let s = term(Op::Field(0), vec![fp_tup.clone()]);
                let e = term(Op::Field(1), vec![fp_tup.clone()]);
                let v_pf = term(Op::Field(2), vec![fp_tup.clone()]);

                let s_mul = term![PF_MUL; s.clone(), new_pf_lit(1u64 << (ctx.e + ctx.m))];
                let e_mul = term![PF_MUL; e.clone(), new_pf_lit(1u64 << ctx.m)];
                let m = term![PF_ADD; v_pf, term![PF_NEG; term![PF_ADD; s_mul, e_mul]]];

                // Assert well-formedness of s, e and m through range checks
                gadget.assert(gadget.is_bool(&s));
                gadget.assert(term![Op::PfFitsInBits(ctx.e); e.clone()]);
                gadget.assert(term![Op::PfFitsInBits(ctx.m); m.clone()]);

                let exponent_min = gadget.pf_sub(&new_pf_lit(ctx.e_normal_min), &new_pf_lit(1));
                let exponent_max = new_pf_lit(ctx.e_max);

                let exponent = term![PF_ADD; e.clone(), exponent_min.clone()];

                let mantissa_is_zero = gadget.is_zero(&m);
                let _mantissa_is_not_zero = term![NOT; mantissa_is_zero.clone()];
                let _exponent_is_min = term![EQ; exponent.clone(), exponent_min.clone()];
                let _exponent_is_max = term![EQ; exponent.clone(), exponent_max];

                // Precompute the shift length `d` for float normalization
                let d = compute_hint![
                    computation,
                    format!("{}.d", v.name),
                    Hint::normalize;
                    &m,
                    ctx.m
                ];

                // Assert soundness of `d` with a range check
                // It should be in the range [0, ctx.m].
                let bitlen = (usize::BITS - ctx.m.leading_zeros()) as usize;
                gadget.assert(term![Op::PfFitsInBits(bitlen); d.clone()]);
                // continue here with the querypowerof2 gadget operation on shift

                // return the term that we rewrite orig with
                Some(term![
                Op::Tuple;
                term![Op::PfToBoolTrusted; s.clone()],
                e,
                m,
                term![Op::PfToBoolTrusted; s]
                ])
            }
            // Rewrites float constants into tuples of (s: bool, e: field, m: field, a: bool).
            Op::Const(v) => {
                let comps = match v.as_ref() {
                    Value::F32(fp) => Some(Context::new(8, 23).new_f32_constant(*fp)),
                    Value::F64(fp) => Some(Context::new(11, 52).new_f64_constant(*fp)),
                    _ => None,
                };
                comps.map(|float| {
                    term(
                        Op::Tuple,
                        vec![
                            const_(Value::Bool(float.0 == 1)),
                            const_(Value::Field(cfg().field().new_v(float.1))),
                            const_(Value::Field(cfg().field().new_v(float.2))),
                            const_(Value::Bool(float.3 == 1)),
                        ],
                    )
                })
            }
            Op::Eq => todo!(),
            Op::FpBinOp(_fp_bin_op) => todo!(),
            Op::FpBinPred(_fp_bin_pred) => todo!(),
            Op::FpUnPred(_fp_un_pred) => todo!(),
            Op::FpUnOp(_fp_un_op) => todo!(),
            Op::BvToFp => todo!(),
            Op::UbvToFp(_) => todo!(),
            Op::SbvToFp(_) => todo!(),
            Op::FpToFp(_) => todo!(),
            Op::PfToFp(_) => todo!(),
            _ => None,
        }
    }
}

/// Replace floats with IEEE 754 constructions
pub fn construct_floats(c: &mut Computation) {
    let mut pass = FloatRewriter::default();
    pass.traverse(c);
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::cfg::cfg_or_default as cfg;

    #[test]
    fn const_fp32() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (val #fp3.1415926535f32)
                    )
                    val
                )
            )
            ",
        );
        construct_floats(&mut c);

        let expected = term(
            Op::Tuple,
            vec![
                const_(Value::Bool(false)),
                const_(Value::Field(cfg().field().new_v(1))),
                const_(Value::Field(cfg().field().new_v(13176795))),
                const_(Value::Bool(false)),
            ],
        );

        assert_eq!(c.outputs[0], expected);
    }

    #[test]
    fn const_fp64() {
        let mut c = text::parse_computation(
            b"
            (computation
                (metadata (parties ) (inputs) (commitments))
                (precompute () () (#t ))
                (let
                    (
                        (val #fp-3.141592653589793)
                    )
                    val
                )
            )
            ",
        );
        construct_floats(&mut c);

        let expected = term(
            Op::Tuple,
            vec![
                const_(Value::Bool(true)),
                const_(Value::Field(cfg().field().new_v(1))),
                const_(Value::Field(cfg().field().new_v(
                    Integer::from_str_radix("7074237752028440", 10).unwrap(),
                ))),
                const_(Value::Bool(false)),
            ],
        );

        assert_eq!(c.outputs[0], expected);
    }

    // #[test]
    // fn init_fp32() {
    //     let mut c = text::parse_computation(
    //         b"
    //                 (computation
    //                     (metadata (parties ) (inputs (a f32)) (commitments))
    //                     (precompute () () (#t ))
    //                     (let
    //                         (
    //                             (val a)
    //                         )
    //                         val
    //                     )
    //                 )
    //             ",
    //     );
    //     let values = text::parse_value_map(
    //         b"
    //         (set_default_modulus 11
    //         (let (
    //             (a #fp3.1415926535f32)
    //         ) false ; ignored
    //         ))
    //     ",
    //     );
    //     // println!("{}", text::serialize_computation(&c));
    //     construct_floats(&mut c);
    //     println!("{}", text::serialize_computation(&c));
    //     // println!("{:#?}", c.eval_all(&values));
    //     assert_eq!(vec![Value::F32(1.234)], c.eval_all(&values));
    // }

    // #[test]
    // fn add_fp32() {
    //     let mut c = text::parse_computation(
    //         b"
    //                 (computation
    //                     (metadata (parties ) (inputs (a f32) (b f32) (return f32)) (commitments))
    //                     (precompute () () (#t ))
    //                     (= return (fpadd a b))
    //                 )
    //             ",
    //     );
    //     let values = text::parse_value_map(
    //         b"
    //         (set_default_modulus 11
    //         (let (
    //             (a #fp1f32)
    //             (b #fp2f32)
    //             (return #fp3f32)
    //         ) false ; ignored
    //         ))
    //     ",
    //     );
    //     construct_floats(&mut c);
    //     assert_eq!(vec![Value::F32(3.0)], c.eval_all(&values));
    // }
}
