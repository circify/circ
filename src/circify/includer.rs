use std::collections::{HashMap, VecDeque};
use std::path::{Path, PathBuf};

pub trait Loader: Sized {
    type AST;
    type ParseError;
    fn parse<P: AsRef<Path>>(&self, p: &P) -> Result<Self::AST, Self::ParseError>;
    fn includes<P: AsRef<Path>>(&self, ast: &Self::AST, p: &P) -> Vec<PathBuf>;
    fn recursive_load<P: AsRef<Path>>(
        &self,
        p: &P,
    ) -> Result<HashMap<PathBuf, Self::AST>, Self::ParseError> {
        let mut m = HashMap::new();
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
