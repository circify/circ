//! Machinery for assigning operations to sharing schemes

use crate::ir::term::{Computation, PostOrderIter, TermMap};

/// The sharing scheme used for an operation
pub enum SharingType {
    /// Arithmetic sharing (additive mod `Z_(2^l)`)
    Arithmetic,
    /// Boolean sharing (additive mod `Z_2`)
    Boolean,
    /// Yao sharing (one party holds `k_a`, `k_b`, other knows the `{k_a, k_b} <-> {0, 1}` mapping)
    Yao,
}

/// A map from terms (operations or inputs) to sharing schemes they use
pub type SharingMap = TermMap<SharingType>;

/// Assigns boolean sharing to all terms
pub fn all_boolean_sharing(c: &Computation) -> SharingMap {
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| (term.clone(), SharingType::Boolean))
        })
        .collect()
}
