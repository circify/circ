//! Parsing and recursively loading C.

use lang_c::driver::Error;
use lang_c::driver::{parse, Config, Parse};
use std::path::PathBuf;

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
