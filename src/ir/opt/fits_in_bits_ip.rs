//! Replace [Op::PfFitsInBits] with an interactive protocol.

use super::mem::ram::haboeck_range_check;
use crate::ir::term::*;
use crate::util::ns::Namespace;
use circ_fields::FieldT;
use fxhash::FxHashMap as HashMap;
use log::debug;

/// Replace [Op::PfFitsInBits] with an interactive protocol.
pub fn fits_in_bits_ip(c: &mut Computation) {
    let mut constraints = Vec::new();
    assert_eq!(c.outputs.len(), 1);
    collect_constraints(&c.outputs[0], &mut constraints);
    // (field, num bits) -> terms in that range
    let mut by_field_and_size: HashMap<(FieldT, usize), Vec<Term>> = HashMap::default();
    for constraint in &constraints {
        if let Op::PfFitsInBits(bits) = constraint.op() {
            let field = check(&constraint.cs()[0]).as_pf().clone();
            by_field_and_size
                .entry((field, *bits))
                .or_default()
                .push(constraint.cs()[0].clone());
        } else {
            unreachable!()
        }
    }
    if constraints.is_empty() {
        return;
    }
    let mut new_assertions = Vec::new();
    let ns = Namespace::default();
    let mut substitution_cache = TermMap::default();
    for (i, ((field, num_bits), terms)) in by_field_and_size.into_iter().enumerate() {
        let ns = ns.subspace(format!("fib_{}_{}", i, num_bits));
        debug!(
            "Found {} values that fit in {} bits in field {}",
            terms.len(),
            num_bits,
            field
        );
        let (cost, k) = (0..=num_bits as u32)
            .filter_map(|k| {
                let cost = subrange_cost(terms.len(), num_bits, k)?;
                debug!("subrange size {} => cost {}", k, cost);
                Some((cost, k))
            })
            .min()
            .unwrap();
        debug!("Using subranges of size {}, for cost {}", k, cost);
        if k > 0 {
            for t in &terms {
                substitution_cache
                    .insert(term![Op::PfFitsInBits(num_bits); t.clone()], bool_lit(true));
            }
            if k < num_bits as u32 {
                let field_bits = field.modulus().significant_bits() as usize;
                let num_subranges = num_bits / k as usize;
                let end_length = num_bits - num_subranges * k as usize;
                let mut subterms = Vec::new();
                for (j, t) in terms.into_iter().enumerate() {
                    let ns = ns.subspace(format!("t{}", j));
                    let bv = term_c![Op::PfToBv(field_bits); t];
                    let mut pf_summands = Vec::new();
                    for ii in 0..num_subranges {
                        let sub_bv = term_c![Op::new_bv_extract(k as usize * (ii + 1) - 1, k as usize * ii); &bv];
                        let sub_f = c.new_var(
                            &ns.fqn(format!("sub{}", ii)),
                            Sort::Field(field.clone()),
                            Some(super::super::proof::PROVER_ID),
                            Some(term![Op::new_ubv_to_pf(field.clone()); sub_bv]),
                        );
                        pf_summands.push(
                        term![PF_MUL.clone(); pf_lit(field.new_v(1).pow(k as u64 * ii as u64)), sub_f.clone()],
                    );
                        subterms.push(sub_f);
                    }
                    if end_length > 0 {
                        let end_start = num_subranges * k as usize;
                        let sub_bv = term_c![Op::new_bv_extract(num_bits - 1, end_start); &bv];
                        let sub_f = c.new_var(
                            &ns.fqn("end"),
                            Sort::Field(field.clone()),
                            Some(super::super::proof::PROVER_ID),
                            Some(term![Op::new_ubv_to_pf(field.clone()); sub_bv]),
                        );
                        pf_summands.push(term![PF_MUL.clone(); pf_lit(field.new_v(1 << end_start)), sub_f.clone()]);
                        new_assertions.push(term![Op::PfFitsInBits(end_length); sub_f]);
                    }
                    new_assertions.push(term![EQ; t, term(PF_ADD.clone(), pf_summands)]);
                }
                let upper_bound = 1usize.checked_shl(k).unwrap();
                haboeck_range_check(
                    c,
                    subterms,
                    &ns.subspace("range"),
                    &mut new_assertions,
                    upper_bound,
                    &field,
                )
            } else {
                let upper_bound = 1usize.checked_shl(k).unwrap();
                haboeck_range_check(
                    c,
                    terms,
                    &ns.subspace("range"),
                    &mut new_assertions,
                    upper_bound,
                    &field,
                )
            }
        } else {
            for t in terms {
                new_assertions.push(term![Op::PfFitsInBits(num_bits); t.clone()]);
            }
        }
    }
    new_assertions.push(extras::substitute_cache(
        &c.outputs[0],
        &mut substitution_cache,
    ));
    assert!(new_assertions.len() > 1);
    c.outputs[0] = term(AND, new_assertions);
}

/// The cost of doing k-bit ranges for n b-bit values.
fn subrange_cost(n: usize, b: usize, k: u32) -> Option<usize> {
    if k == 0 {
        Some(n * b)
    } else {
        let n_ranges = b / k as usize;
        let n_leftover_bits = b - n_ranges * k as usize;
        n_ranges
            .checked_mul(n)?
            .checked_add(1usize.checked_shl(k)?)?
            .checked_mul(3)?
            .checked_add(n_leftover_bits.checked_mul(n)?)
    }
}

/// Given a boolean assertion `t`, collect any implied bitsize constraints into `constraints`.
///
/// Each constraint most have operator [Op::PfFitsInBits].
fn collect_constraints(t: &Term, constraints: &mut Vec<Term>) {
    debug_assert_eq!(check(t), Sort::Bool);
    match t.op() {
        Op::PfFitsInBits(_) => constraints.push(t.clone()),
        &AND => {
            for c in t.cs() {
                collect_constraints(c, constraints);
            }
        }
        _ => {}
    }
}
