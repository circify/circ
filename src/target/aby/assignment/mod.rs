//! Machinery for assigning operations to sharing schemes

use crate::ir::term::{BvNaryOp, Computation, Op, PostOrderIter, TermMap};

pub mod ilp;

/// The sharing scheme used for an operation
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum ShareType {
    /// Arithmetic sharing (additive mod `Z_(2^l)`)
    Arithmetic,
    /// Boolean sharing (additive mod `Z_2`)
    Boolean,
    /// Yao sharing (one party holds `k_a`, `k_b`, other knows the `{k_a, k_b} <-> {0, 1}` mapping)
    Yao,
}

/// List of share types.
pub const SHARE_TYPES: [ShareType; 3] = [ShareType::Arithmetic, ShareType::Boolean, ShareType::Yao];

impl ShareType {
    fn char(&self) -> char {
        match self {
            &ShareType::Arithmetic => 'a',
            &ShareType::Yao => 'y',
            &ShareType::Boolean => 'b',
        }
    }
}

/// A map from terms (operations or inputs) to sharing schemes they use
pub type SharingMap = TermMap<ShareType>;

/// Assigns boolean sharing to all terms
pub fn all_boolean_sharing(c: &Computation) -> SharingMap {
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| (term.clone(), ShareType::Boolean))
        })
        .collect()
}

/// Assigns arithmetic sharing to addition and multiplication
pub fn some_arith_sharing(c: &Computation) -> SharingMap {
    c.outputs
        .iter()
        .flat_map(|output| {
            PostOrderIter::new(output.clone()).map(|term| match &term.op {
                Op::BvNaryOp(o) => match o {
                    BvNaryOp::Add => (term.clone(), ShareType::Arithmetic),
                    BvNaryOp::Mul => (term.clone(), ShareType::Arithmetic),
                    _ => (term.clone(), ShareType::Boolean),
                },
                _ => (term.clone(), ShareType::Boolean),
            })
        })
        .collect()
}
