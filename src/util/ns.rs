//! Namespacing

use std::fmt::Display;

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
