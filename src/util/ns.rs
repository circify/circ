//! Tools for namespacing and ensuring name uniqueness.

use std::fmt::Display;

use fxhash::FxHashSet;

/// A namespace. Used to create unique names.
///
/// Doesn't check for uniqueness: just a helper.
#[derive(Default)]
pub struct Namespace(String);

impl Namespace {
    /// The root namespace
    pub fn new() -> Self {
        Namespace("".to_owned())
    }
    /// Get a subspace
    pub fn subspace(&self, ext: impl Display) -> Self {
        Namespace(format!("{}__{ext}", self.0))
    }
    /// Get a (fully qualified) name in this space
    pub fn fqn(&self, ext: impl Display) -> String {
        format!("{}_{ext}", self.0)
    }
}

/// A tool for ensuring name uniqueness.
pub struct Uniquer {
    used: FxHashSet<String>,
}

impl Uniquer {
    /// Create a new [Uniquer] with these names already used.
    pub fn new(used: impl IntoIterator<Item = String>) -> Self {
        Uniquer {
            used: used.into_iter().collect(),
        }
    }
    /// Make a unique name prefixed by `prefix`, store it, and return it.
    pub fn mk_uniq(&mut self, prefix: &str) -> String {
        if !self.used.contains(prefix) {
            self.used.insert(prefix.into());
            return prefix.into();
        }
        for i in 0.. {
            let name = format!("{prefix}_{i}");
            if !self.used.contains(&name) {
                self.used.insert(name.clone());
                return name;
            }
        }
        unreachable!()
    }
}
