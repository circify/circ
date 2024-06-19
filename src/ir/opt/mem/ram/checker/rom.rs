//! Implementation of ROM checking based on https://eprint.iacr.org/2022/1530.pdf
//!
//! Cost: about (N + A)(L + 1) where the ROM size is N, there are A reads, and values have size L.
//! If the ROM contents are fixed, cost drops to N + A(L + 1)

use super::super::hash::UniversalHasher;
use super::{Access, Ram};
use crate::front::PROVER_VIS;
use crate::ir::opt::cfold::fold;
use crate::ir::term::*;
use crate::util::ns::Namespace;

use log::debug;

/// The implementation of Haboeck's lookup argument.
///
/// Takes haystack, needles, and returns a term which should be asserted to ensure that each needle
/// is in haystack.
pub fn lookup(c: &mut Computation, ns: Namespace, haystack: Vec<Term>, needles: Vec<Term>) -> Term {
    debug!(
        "Haboeck lookup haystack {}, needles {}",
        haystack.len(),
        needles.len()
    );
    if haystack.is_empty() {
        assert!(needles.is_empty());
        return bool_lit(true);
    }
    let sort = check(&haystack[0]);
    let f = sort.as_pf().clone();
    let haystack_tup = term(Op::Tuple, haystack.clone());
    let needles_tup = term(Op::Tuple, needles.clone());
    let counts_pre = tuple_terms(term![Op::ExtOp(ExtOp::Haboeck); haystack_tup, needles_tup]);
    let counts: Vec<Term> = counts_pre
        .into_iter()
        .enumerate()
        .map(|(i, coeff)| {
            c.new_var(
                &ns.fqn(format!("c{i}")),
                sort.clone(),
                PROVER_VIS,
                Some(coeff),
            )
        })
        .collect();
    let key = term(
        Op::PfChallenge(ns.fqn("key"), f.clone()),
        haystack
            .iter()
            .chain(&needles)
            .chain(&counts)
            .cloned()
            .collect(),
    );
    // x_i + k
    let needle_shifts: Vec<Term> = needles
        .into_iter()
        .map(|needle| term![PF_ADD; needle, key.clone()])
        .collect();
    // tup(1 / (x_i + k))
    let needle_invs_tup: Term =
        term![Op::ExtOp(ExtOp::PfBatchInv); term(Op::Tuple, needle_shifts.clone())];
    // 1 / (x_i + k)
    let needle_invs: Vec<Term> = (0..needle_shifts.len())
        .map(|i| {
            c.new_var(
                &ns.fqn(format!("needi{i}")),
                sort.clone(),
                PROVER_VIS,
                Some(term_c![Op::Field(i); needle_invs_tup]),
            )
        })
        .collect();
    let one = pf_lit(f.new_v(1));
    let mut assertions: Vec<Term> = Vec::new();
    // check 1 / (x_i + k)
    assertions.extend(
        needle_invs
            .iter()
            .zip(&needle_shifts)
            .map(|(ix, x)| term![EQ; term_c![PF_MUL; ix, x], one.clone()]),
    );

    // 1 / (x_i + k)
    let hay_shifts: Vec<Term> = haystack
        .clone()
        .into_iter()
        .map(|hay| term![PF_ADD; hay, key.clone()])
        .collect();
    // tup(1 / (x_i + k))
    let hay_invs_tup: Term =
        term![Op::ExtOp(ExtOp::PfBatchInv); term(Op::Tuple, hay_shifts.clone())];
    // ct_i / (x_i + k)
    let hay_divs: Vec<Term> = (0..hay_shifts.len())
        .zip(&counts)
        .map(|(i, ct)| {
            c.new_var(
                &ns.fqn(format!("hayi{i}")),
                sort.clone(),
                PROVER_VIS,
                Some(term![PF_MUL; ct.clone(), term_c![Op::Field(i); hay_invs_tup]]),
            )
        })
        .collect();

    assertions.extend(
        hay_divs
            .iter()
            .zip(hay_shifts)
            .zip(counts)
            .map(|((div, hay_shift), ct)| term![EQ; term_c![PF_MUL; div, hay_shift.clone()], ct]),
    );

    let needlesum = term(PF_ADD, needle_invs);
    let haysum = term(PF_ADD, hay_divs);
    assertions.push(term![Op::Eq; haysum, needlesum]);
    term(AND, assertions)
}

/// Returns a term to assert.
pub fn check_covering_rom(c: &mut Computation, ns: Namespace, ram: Ram) -> Term {
    assert!(ram.cfg.covering_rom);
    let f = &ram.cfg.field;
    if ram.accesses.is_empty() {
        return bool_lit(true);
    }
    // (addr, value)
    let mut reads: Vec<Vec<Term>> = Default::default();
    let mut writes: Vec<Vec<Term>> = Default::default();
    for a in &ram.accesses {
        let mut access = vec![a.idx.clone()];
        Access::val_to_field_elements(&a.val, &ram.cfg, &mut access);
        match fold(&a.write.b, &[]).as_bool_opt() {
            Some(true) => writes.push(access),
            Some(false) => reads.push(access),
            None => panic!(),
        }
    }
    assert!(!writes.is_empty());
    let uhf = UniversalHasher::new(
        ns.fqn("uhf_key"),
        f,
        reads.iter().chain(&writes).flatten().cloned().collect(),
        writes[0].len(),
    );
    let write_hashes = writes.into_iter().map(|a| uhf.hash(a)).collect();
    let read_hashes = reads.into_iter().map(|a| uhf.hash(a)).collect();
    lookup(c, ns.subspace("scalar"), write_hashes, read_hashes)
}
