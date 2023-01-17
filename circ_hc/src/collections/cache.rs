//! A cache from terms that does not retain its keys.

use fxhash::FxHashMap as HashMap;

use crate::{Table, Weak};

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
}

impl<Op, T: Table<Op>, V> std::ops::Deref for NodeCache<Op, T, V> {
    type Target = HashMap<T::Weak, V>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<Op, T: Table<Op>, V> std::ops::DerefMut for NodeCache<Op, T, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
