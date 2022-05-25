//! Parsing and recursively loading Z#.
//!
//! Based on the original ZoKrates parser, with extra machinery for recursive loading and locating
//! the standard library.

use zokrates_pest_ast as ast;

use log::debug;
use std::collections::HashMap;
use std::env::var_os;

use crate::circify::includer::Loader;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use typed_arena::Arena;

/// A representation of the standard libary's location.
#[derive(Default)]
pub struct ZStdLib {
    path: PathBuf,
}

impl ZStdLib {
    /// Looks for a "ZoKrates/zokrates_stdlib/stdlib" path in some ancestor of the current
    /// directory.
    pub fn new() -> Self {
        if let Some(p) = var_os("ZSHARP_STDLIB_PATH") {
            let p = PathBuf::from(p);
            if p.exists() {
                return Self { path: p };
            } else {
                panic!(
                    "ZStdLib: ZSHARP_STDLIB_PATH {:?} does not appear to exist",
                    p
                );
            }
        }

        let p = std::env::current_dir().unwrap().canonicalize().unwrap();
        assert!(p.is_absolute());
        let stdlib_subdirs = vec![
            "ZoKrates/zokrates_stdlib/stdlib",
            "third_party/ZoKrates/zokrates_stdlib/stdlib",
        ];
        for a in p.ancestors() {
            for subdir in &stdlib_subdirs {
                let mut q = a.to_path_buf();
                q.push(subdir);
                if q.exists() {
                    return Self { path: q };
                }
            }
        }
        panic!("Could not find ZoKrates/Z# stdlib from {}", p.display())
    }
    /// Turn `child`, relative to `parent` (or to the standard libary!), into an absolute path.
    pub fn canonicalize(&self, parent: &Path, child: &str) -> PathBuf {
        debug!("Looking for {} from {}", child, parent.display());
        let paths = [parent.to_path_buf(), self.path.clone()];
        for mut p in paths {
            p.push(child);
            debug!("Checking {}", p.display());
            if p.exists() {
                return p;
            }
            if p.extension().is_some() {
                continue;
            }
            for ext in ["zok", "zx"] {
                p.set_extension(ext);
                debug!("Checking {}", p.display());
                if p.exists() {
                    return p;
                }
            }
        }
        panic!("Could not find {} from {}", child, parent.display())
    }
    /// check if this path is the EMBED prototypes path
    pub fn is_embed<P: AsRef<Path>>(&self, p: P) -> bool {
        p.as_ref().starts_with(&self.path)
            && p.as_ref().file_stem().and_then(|s| s.to_str()) == Some("EMBED")
    }
}

/// A recrusive Z# loader
#[derive(Default)]
pub struct ZLoad {
    sources: Arena<String>,
    stdlib: ZStdLib,
}

impl ZLoad {
    /// Make a new Z# loader, looking for the standard library somewhere above the current
    /// dirdirectory. See [ZStdLib::new].
    pub fn new() -> Self {
        Self {
            sources: Arena::new(),
            stdlib: ZStdLib::new(),
        }
    }

    /// Recursively load a Z# file.
    ///
    /// ## Returns
    ///
    /// Returns a map from file paths to parsed files.
    pub fn load<P: AsRef<Path>>(&self, p: &P) -> HashMap<PathBuf, ast::File> {
        self.recursive_load(p).unwrap()
    }

    /// Get ref to contained ZStdLib
    pub fn stdlib(&self) -> &ZStdLib {
        &self.stdlib
    }
}

impl<'a> Loader for &'a ZLoad {
    type ParseError = ();
    type AST = zokrates_pest_ast::File<'a>;

    fn parse<P: AsRef<Path>>(&self, p: &P) -> Result<Self::AST, Self::ParseError> {
        let mut s = String::new();
        File::open(p).unwrap().read_to_string(&mut s).unwrap();
        debug!("Parsing: {}", p.as_ref().display());
        let s = self.sources.alloc(s);
        let ast = ast::generate_ast(s);
        if ast.is_err() {
            panic!("{}", ast.unwrap_err());
        }
        Ok(ast.unwrap())
    }
    fn includes<P: AsRef<Path>>(&self, ast: &Self::AST, p: &P) -> Vec<PathBuf> {
        let mut c = p.as_ref().to_path_buf();
        c.pop();
        ast.declarations
            .iter()
            .filter_map(|d| {
                if let ast::SymbolDeclaration::Import(i) = d {
                    let ext = match i {
                        ast::ImportDirective::Main(m) => &m.source.value,
                        ast::ImportDirective::From(m) => &m.source.value,
                    };
                    Some(self.stdlib.canonicalize(&c, ext))
                } else {
                    None
                }
            })
            .collect()
    }
}
