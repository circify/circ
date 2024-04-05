//! Set lookup arguments
use super::*;
use crate::util::ns::Namespace;
use log::debug;

use std::convert::TryInto;

/// Do set lookup arguments
pub fn apply(c: &mut Computation) {
    let mut asserted_map_contains_keys = TermSet::default();
    assert_eq!(c.outputs.len(), 1);
    extras::collect_asserted_ops(
        &c.outputs[0],
        &|o: &Op| o == &Op::ExtOp(ExtOp::MapContainsKey),
        &mut asserted_map_contains_keys,
    );
    if asserted_map_contains_keys.is_empty() {
        return;
    }
    let mut maps_to_keys: TermMap<Vec<Term>> = TermMap::default();
    for containment in &asserted_map_contains_keys {
        let [map, key]: &[Term; 2] = containment.cs().try_into().unwrap();
        maps_to_keys
            .entry(map.clone())
            .or_default()
            .push(key.clone());
    }
    let ns = Namespace::new();
    let mut to_assert = Vec::new();
    for (i, (map, keys)) in maps_to_keys.into_iter().enumerate() {
        assert!(
            map.is_const(),
            "set membership only supported for constant sets"
        );
        debug!(
            "set membership argument; set size {}, key count {}",
            map.as_map_opt().unwrap().map.len(),
            keys.len()
        );
        let haystack: Vec<Term> = map
            .as_map_opt()
            .unwrap()
            .map
            .keys()
            .cloned()
            .map(Op::Const)
            .map(leaf_term)
            .collect();
        to_assert.push(super::checker::rom::lookup(
            c,
            ns.subspace(format!("setmem{}", i)),
            haystack,
            keys,
        ));
    }
    to_assert.push(c.outputs[0].clone());
    let subs: TermMap<Term> = asserted_map_contains_keys
        .into_iter()
        .map(|c| (c, bool_lit(true)))
        .collect();
    c.outputs = vec![extras::substitute(&term(AND, to_assert), subs)];
}
