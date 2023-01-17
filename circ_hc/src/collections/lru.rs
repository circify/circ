//! A LRU cache from terms to values which does not retain its keys.

use crate::Table;

/// A LRU cache from terms to values which does not retain its keys.
pub struct NodeLruCache<Op, T: Table<Op>, V> {
    inner: lru::LruCache<T::Weak, V>,
}

impl<Op, T: Table<Op>, V> NodeLruCache<Op, T, V> {
    /// Create an empty cache with room for `n` items.
    pub fn with_capacity(n: usize) -> Self {
        Self {
            inner: lru::LruCache::new(n),
        }
    }
}

impl<Op, T: Table<Op>, V> std::ops::Deref for NodeLruCache<Op, T, V> {
    type Target = lru::LruCache<T::Weak, V>;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<Op, T: Table<Op>, V> std::ops::DerefMut for NodeLruCache<Op, T, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
