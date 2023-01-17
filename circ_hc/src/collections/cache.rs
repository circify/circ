//! A cache from terms that does not retain its keys.

use fxhash::FxHashMap as HashMap;

use crate::{Table, Weak, Node};

/// A cache from terms that does not retain its keys.
pub struct NodeCache<Op, T: Table<Op>, V> {
    inner: HashMap<T::Weak, V>,
}

impl<Op, T: Table<Op>, V> NodeCache<Op, T, V> {
    /// Create an empty cache.
    pub fn new() -> Self {
        Self {
            inner: HashMap::default(),
        }
    }
    /// Create an empty cache with room for `n` items before allocation.
    pub fn with_capacity(n: usize) -> Self {
        Self {
            inner: HashMap::with_capacity_and_hasher(n, fxhash::FxBuildHasher::default()),
        }
    }
    /// Remove entries with free'd keys.
    pub fn collect(&mut self) {
        self.inner.retain(|k, _| k.upgrade().is_some());
    }
    /// Lookup; free entry if deallocated.
    pub fn get(&self, k: &T::Node) -> Option<&V> {
        self.get_weak(&k.downgrade())
    }
    /// Lookup; free entry if deallocated.
    pub fn get_weak(&self, k: &T::Weak) -> Option<&V> {
        self.inner.get(k)
    }
    /// Insert
    pub fn insert(&mut self, k: T::Node, v: V) -> Option<V> {
        self.inner.insert(k.downgrade(), v)
    }
}
