//! Parsing and recursively loading C.

use lang_c::driver::Error;
use lang_c::driver::{parse, Config, Parse};
use std::path::Path;

pub struct CParser {
    config: Config,
}

impl CParser {
    pub fn new() -> Self {
        Self {
            config: Config::default(),
        }
    }

    pub fn parse_file(&self, path: &Path) -> Result<Parse, Error> {
        parse(&self.config, path)
    }
}
