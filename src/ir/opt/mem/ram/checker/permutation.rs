use super::super::hash::{MsHasher, UniversalHasher};
use crate::ir::opt::mem::ram::{Access, AccessCfg, Order};
use crate::ir::term::*;
use crate::util::ns::Namespace;
use std::collections::VecDeque;

/// Permute the accesses into sorted order using a Waksman network.
pub(super) fn waksman(
    accesses: &VecDeque<Access>,
    cfg: &AccessCfg,
    val_sort: &Sort,
    new_var: &mut impl FnMut(&str, Term) -> Term,
) -> Vec<Access> {
    let f = &cfg.field;
    let f_s = Sort::Field(f.clone());
    // (1) sort the transcript
    let field_tuples: Vec<Term> = accesses.iter().map(|a| a.to_field_tuple(cfg)).collect();
    let switch_settings_tuple = term![Op::ExtOp(ExtOp::Waksman); make_array(f_s.clone(), check(&field_tuples[0]), field_tuples.clone())];
    let n = check(&switch_settings_tuple).as_tuple().len();
    let mut switch_settings: VecDeque<Term> = (0..n)
        .map(|i| {
            new_var(
                &format!("sw{}", i),
                term![Op::Field(i); switch_settings_tuple.clone()],
            )
        })
        .collect();

    let sorted_field_tuple_values: Vec<Term> =
        circ_waksman::symbolic_apply(field_tuples, &mut switch_settings, &mut crossbar);

    assert!(switch_settings.is_empty());

    let sorted_accesses: Vec<Access> = sorted_field_tuple_values
        .into_iter()
        .map(|v| {
            let len = check(&v).as_tuple().len();
            let elems = (0..len)
                .map(|idx| term![Op::Field(idx); v.clone()])
                .collect();
            let mut access = Access::from_field_elems_trusted(elems, val_sort, cfg, Order::Sort);
            assert!(
                check(&access.val).is_scalar(),
                "Waksman only supports scalar values; got {}",
                check(&access.val)
            );
            access.val_hash = Some(super::scalar_to_field(&access.val, cfg));
            access
        })
        .collect();
    sorted_accesses
}

fn crossbar(top: &Term, bot: &Term, switch: Term) -> (Term, Term) {
    debug_assert_eq!(check(top), check(bot));
    (
        term_c![Op::Ite; &switch, bot, top],
        term_c![Op::Ite; &switch, top, bot],
    )
}

/// Permute the accesses into sorted order using a multi-set hash argument.
pub(super) fn msh(
    accesses: &VecDeque<Access>,
    ns: &Namespace,
    cfg: &AccessCfg,
    new_var: &mut impl FnMut(&str, Term) -> Term,
    val_sort: &Sort,
    assertions: &mut Vec<Term>,
) -> Vec<Access> {
    let f = &cfg.field;
    let f_s = Sort::Field(f.clone());
    // (1) sort the transcript
    let field_tuples: Vec<Term> = accesses.iter().map(|a| a.to_field_tuple(cfg)).collect();
    let sorted_field_tuple_values: Vec<Term> = unmake_array(
        term![Op::ExtOp(ExtOp::Sort); make_array(f_s.clone(), check(&field_tuples[0]), field_tuples.clone())],
    );
    let mut sorted_accesses: Vec<Access> = sorted_field_tuple_values
        .into_iter()
        .enumerate()
        .map(|(i, v)| {
            Access::declare_trusted(
                cfg,
                |name: &str, term: Term| new_var(&format!("sort_a{i}_{name}"), term),
                val_sort,
                v,
            )
        })
        .collect();
    let uhf_inputs: Vec<Term> = field_tuples
        .into_iter()
        .chain(sorted_accesses.iter().map(|a| a.to_field_tuple(cfg)))
        .collect();
    let uhf = UniversalHasher::new(ns.fqn("uhf_key"), f, uhf_inputs.clone(), cfg.len(val_sort));
    let msh = MsHasher::new(ns.fqn("ms_hash_key"), f, uhf_inputs);

    // (2) permutation argument
    let univ_hashes_unsorted: Vec<Term> = accesses
        .iter()
        .map(|a| a.universal_hash(cfg, val_sort, &uhf).0)
        .collect();
    let (univ_hashes_sorted, val_hashes_sorted): (Vec<Term>, Vec<Term>) = sorted_accesses
        .iter()
        .map(|a| a.universal_hash(cfg, val_sort, &uhf))
        .unzip();
    let ms_hash_passes = term![EQ; msh.hash(univ_hashes_unsorted), msh.hash(univ_hashes_sorted)];
    assertions.push(ms_hash_passes);
    for (access, hash) in sorted_accesses.iter_mut().zip(val_hashes_sorted) {
        access.val_hash = Some(hash);
    }

    sorted_accesses
}
