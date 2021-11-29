//! Language-agnostic machinery for recursively loading files

use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

/// A trait which defines a graph of files that can be recursively loaded
pub trait Loader: Sized {
    /// A parsed file
    type AST;
    /// A parser error
    type ParseError;
    /// Given a file's path, parse it
    fn parse<P: AsRef<Path>>(&self, p: &P) -> Result<Self::AST, Self::ParseError>;
    /// Given a file's AST and path, return a list of paths that should be loaded
    fn includes<P: AsRef<Path>>(&self, ast: &Self::AST, p: &P) -> Vec<PathBuf>;
    /// Recursively load all referenced paths.
    ///
    /// ## Returns
    ///
    /// Returns a map from loaded paths to ASTs.
    fn recursive_load<P: AsRef<Path>>(
        &self,
        p: &P,
    ) -> Result<HashMap<PathBuf, Self::AST>, Self::ParseError> {
        let mut m = HashMap::default();
        let mut q = VecDeque::new();
        q.push_back(p.as_ref().to_path_buf());
        while let Some(p) = q.pop_front() {
            if !m.contains_key(&p) {
                let ast = self.parse(&p)?;
                for c in self.includes(&ast, &p) {
                    if !m.contains_key(&c) {
                        q.push_back(c);
                    }
                }
                m.insert(p, ast);
            }
        }
        Ok(m)
    }
}
