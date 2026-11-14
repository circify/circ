//! Parsing and recursively loading C.

use lang_c::driver::Error;
use lang_c::driver::{parse, Config, Parse};
use std::path::Path;

pub struct CParser {
    config: Config,
}

impl CParser {
    pub fn new() -> Self {
        let mut config = Config::default();
        // lang-c parses C11; keep the preprocessor in the same language mode.
        config.cpp_options.push("-std=gnu11".into());
        Self { config }
    }

    pub fn parse_file(&self, path: &Path) -> Result<Parse, Error> {
        parse(&self.config, path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_stdbool_example() {
        CParser::new()
            .parse_file(Path::new(
                "examples/C/mpc/unit_tests/arithmetic_tests/2pc_int_equals.c",
            ))
            .unwrap();
    }
}
