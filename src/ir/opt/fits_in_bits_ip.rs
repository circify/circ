//! Replace [Op::PfFitsInBits] with an interactive protocol.

use super::mem::ram::range_check_ip;
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
        debug!(
            "Found {} values that fit in {} bits in field {}",
            terms.len(),
            num_bits,
            field
        );
        for t in &terms {
            substitution_cache.insert(term![Op::PfFitsInBits(num_bits); t.clone()], bool_lit(true));
        }
        let upper_bound = 1usize.checked_shl(num_bits as u32).unwrap();
        range_check_ip(
            c,
            terms,
            &ns.subspace(format!("range_{}_{}", i, num_bits)),
            &mut new_assertions,
            upper_bound,
            &field,
        )
    }
    new_assertions.push(extras::substitute_cache(
        &c.outputs[0],
        &mut substitution_cache,
    ));
    assert!(new_assertions.len() > 1);
    c.outputs[0] = term(AND, new_assertions);
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
