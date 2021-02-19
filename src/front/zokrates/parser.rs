use zokrates_pest_ast as ast;

use log::debug;
use std::collections::HashMap;

use crate::circify::includer::Loader;
use rug::Integer;
use std::fs::File;
use std::io::{BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use typed_arena::Arena;

pub fn parse_inputs(p: PathBuf) -> HashMap<String, Integer> {
    let mut m = HashMap::new();
    for l in BufReader::new(File::open(p).unwrap()).lines() {
        let l = l.unwrap();
        let l = l.trim();
        if l.len() > 0 {
            let mut s = l.split_whitespace();
            let key = s.next().unwrap().to_owned();
            let value = Integer::from(Integer::parse_radix(&s.next().unwrap(), 10).unwrap());
            m.insert(key, value);
        }
    }
    m
}

pub struct ZStdLib {
    path: PathBuf,
}

impl ZStdLib {
    pub fn new() -> Self {
        let p = std::env::current_dir().unwrap().canonicalize().unwrap();
        assert!(p.is_absolute());
        for a in p.ancestors() {
            let mut q = a.to_path_buf();
            q.push("ZoKrates/zokrates_stdlib/stdlib");
            if q.exists() {
                return Self { path: q };
            }
        }
        panic!("Could not find ZoKrates stdlibfrom {}", p.display())
    }
    pub fn canonicalize(&self, parent: &Path, child: &str) -> PathBuf {
        if parent.to_str().map(|s| s.contains("EMBED")).unwrap_or(false) {
            return PathBuf::from("EMBED");
        }
        let paths = vec![parent.to_path_buf(), self.path.clone()];
        for mut p in paths {
            p.push(child);
            if p.extension().is_none() {
                p.set_extension("zok");
            }
            if p.exists() {
                return p;
            }
        }
        panic!("Could not find {} from {}", child, parent.display())
    }
}

pub struct ZLoad {
    sources: Arena<String>,
    stdlib: ZStdLib,
}

impl ZLoad {
    pub fn new() -> Self {
        Self {
            sources: Arena::new(),
            stdlib: ZStdLib::new(),
        }
    }

    pub fn load<P: AsRef<Path>>(&self, p: &P) -> HashMap<PathBuf, ast::File> {
        self.recursive_load(p).unwrap()
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
        Ok(ast::generate_ast(s).unwrap())
    }
    fn includes<P: AsRef<Path>>(&self, ast: &Self::AST, p: &P) -> Vec<PathBuf> {
        let mut c = p.as_ref().to_path_buf();
        c.pop();
        ast.imports
            .iter()
            .map(|i| {
                let ext = match i {
                    ast::ImportDirective::Main(m) => &m.source.value,
                    ast::ImportDirective::From(m) => &m.source.value,
                };
                self.stdlib.canonicalize(&c, ext)
            })
            .filter(|p| p.to_str().map(|s| !s.contains("EMBED")).unwrap_or(true))
            .collect()
    }
}
