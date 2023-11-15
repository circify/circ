use std::cmp::{Eq, Ord, PartialEq, PartialOrd};
use std::hash::Hash;

#[cfg(feature = "hashconsing")]
pub mod hashconsing;
#[cfg(feature = "raw")]
pub mod raw;
#[cfg(feature = "rc")]
pub mod rc;

pub mod collections;

#[cfg(test)]
mod test;

/// A hash-cons table
pub trait Table<Op> {
    /// The type of nodes
    type Node: Node<Op, Weak = Self::Weak> + 'static;
    type Weak: Weak<Op, Node = Self::Node> + 'static;

    /// Create a new node
    fn create(op: &Op, children: Vec<Self::Node>) -> Self::Node;
    /// Create a new node
    fn create_ref<'a>(
        op: &Op,
        children: impl IntoIterator<Item = &'a Self::Node> + Clone,
    ) -> Self::Node {
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

    /// Fun a function on every node
    fn for_each(f: impl FnMut(&Op, &[Self::Node]));

    /// When the table garbage-collects a node with ID `id`, it will call `f(id)`. `f(id)` might
    /// clear caches, etc., but instead of droping `Node`s, it should return them.
    ///
    /// They'll be dropped by the GC routine.
    ///
    /// The idea is to implement Node-keyed caches that should not retain Nodes in their keys (or
    /// values!) by keying them on Node IDs, and then returning any nodes in the value when the GC
    /// hook is called.
    #[allow(unused_variables)]
    fn gc_hook_add(name: &'static str, f: impl Fn(Id) -> Vec<Self::Node> + 'static) {}
    /// Remove a GC hook
    #[allow(unused_variables)]
    fn gc_hook_remove(name: &'static str) {}
    fn gc_hooks_clear() {}
}

/// A hash-cons node
pub trait Node<Op>: Sized + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    type Weak: Weak<Op, Node = Self>;
    /// Get the ref count of this node.
    fn ref_cnt(&self) -> u64;
    /// Get the unique ID of this node.
    fn id(&self) -> Id;
    /// Get the operator of this node.
    fn op(&self) -> &Op;
    /// Get the children of this node.
    fn cs(&self) -> &[Self];
    /// Get the operator and children of this node.
    fn parts(&self) -> (&Op, &[Self]) {
        (self.op(), self.cs())
    }
    /// Get a token that does not retain this node during GC.
    fn downgrade(&self) -> Self::Weak;
}

/// A hash-cons node that may have been dropped
pub trait Weak<Op>: Sized + Clone + PartialEq + Eq + PartialOrd + Ord + Hash {
    type Node: Node<Op, Weak = Self>;
    /// Get the unique ID of this node.
    fn id(&self) -> Id;
    /// Is this upgradeable?
    fn live(&self) -> bool {
        self.upgrade().is_some()
    }
    /// Attempt to get the node itself.
    fn upgrade(&self) -> Option<Self::Node>;
}

/// A unique term ID.
#[repr(transparent)]
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct Id(pub u64);

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "id{}", self.0)
    }
}

impl std::fmt::Debug for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "id{}", self.0)
    }
}

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
