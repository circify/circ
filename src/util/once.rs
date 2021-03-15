use ahash::AHashSet;
use std::hash::Hash;
use std::collections::VecDeque;

pub struct OnceQueue<T> {
    queue: VecDeque<T>,
    set: AHashSet<T>,
}

impl<T: Eq + Hash + Clone> OnceQueue<T> {
    pub fn push(&mut self, t: T) {
        if self.set.insert(t.clone()) {
            self.queue.push_back(t)
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        self.queue.pop_front().map(|t| {
            self.set.remove(&t);
            t
        })
    }
    pub fn new() -> Self {
        Self {
            queue: VecDeque::new(),
            set: AHashSet::new(),
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
