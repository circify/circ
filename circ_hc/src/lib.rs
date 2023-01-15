use std::cmp::{PartialEq, Eq, PartialOrd, Ord};
use std::hash::Hash;

pub mod raw;
pub mod hashconsing;
pub mod rc;
pub use rc::generate_hashcons;

#[cfg(test)]
mod test;


/// A hash-cons table
pub trait Table<Op> {
    /// The type of nodes
    type Node: Node<Op> + 'static;

    /// Create a new node
    fn create(op: &Op, children: Vec<Self::Node>) -> Self::Node;
    /// Create a new node
    fn create_ref<'a>(op: &Op, children: impl IntoIterator<Item=&'a Self::Node> + Clone) -> Self::Node {
        Self::create(op, children.into_iter().cloned().collect())
    }
    /// Run garbage collection
    fn gc() -> usize;
    /// Measure the number of stored elements
    fn table_size() -> usize;

    /// Ensure there is space for this many additional nodes
    fn reserve(num_nodes: usize);

    /// The name of the implementation
    fn name() -> &'static str;
}

/// A hash-cons node
pub trait Node<Op>: Sized + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    /// Get the ref count of this node.
    fn ref_cnt(&self) -> u64;
    /// Get the unique ID of this node.
    fn id(&self) -> Id;
    /// Get the operator of this node.
    fn op(&self) -> &Op;
    /// Get the children of this node.
    fn cs(&self) -> &[Self];
}

/// A unique term ID.
#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Id(pub u64);

mod hash {
    use super::Id;
    use std::hash::{Hash, Hasher};

    // 64 bit primes
    const PRIME_1: u64 = 15124035408605323001;
    const PRIME_2: u64 = 15133577374253939647;

    impl Hash for Id {
        fn hash<H: Hasher>(&self, state: &mut H) {
            let id_hash = self.0.wrapping_mul(PRIME_1).wrapping_add(PRIME_2);
            state.write_u64(id_hash);
        }
    }
}
