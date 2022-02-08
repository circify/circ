//! A queue which does not contains duplications.
//!
//! A "once queue".

use fxhash::FxHashSet;
use std::collections::VecDeque;
use std::hash::Hash;

/// A "once queue", which contains any element at most once.
///
/// It's a FIFO queue, which ignores insertions of elements already present.
pub struct OnceQueue<T> {
    queue: VecDeque<T>,
    set: FxHashSet<T>,
}

impl<T: Eq + Hash + Clone> Default for OnceQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Eq + Hash + Clone> OnceQueue<T> {
    /// Add to the queue. If `t` is already present, it is dropped.
    pub fn push(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t)
        }
    }
    /// Remove the oldest element from the queue.
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front().map(|t| {
            self.set.remove(&t);
            t
        })
    }
    /// Make an empty queue.
    pub fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            set: FxHashSet::default(),
        }
    }
}

impl<A: Eq + Hash + Clone> std::iter::FromIterator<A> for OnceQueue<A> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = A>,
    {
        iter.into_iter().fold(Self::new(), |mut q, i| {
            q.push(i);
            q
        })
    }
}

impl<A: Eq + Hash + Clone> std::iter::Extend<A> for OnceQueue<A> {
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = A>,
    {
        for i in iter.into_iter() {
            self.push(i);
        }
    }
}
