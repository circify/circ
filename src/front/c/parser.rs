//! Parsing and recursively loading C.

use std::path::PathBuf;
use lang_c::driver::{Config, parse, Parse};
use lang_c::driver::Error;

pub struct CParser {
    config: Config,
}

impl CParser {
    pub fn new() -> Self {
        Self {
            config: Config::default(),
        }
    }

    pub fn parse_file(&self, path: &PathBuf) -> Result<Parse, Error> {
        Ok(parse(&self.config, path)?)
    }
}