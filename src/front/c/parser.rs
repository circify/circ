//! Parsing and recursively loading C.

use log::debug;
use std::collections::HashMap;

use crate::circify::includer::Loader;
use std::path::{Path, PathBuf};

// // A recursive c loader
// pub struct CLoad {

// }

// impl CLoad {
//     pub fn new() -> Self {
//         Self {

//         }
//     }

//     // Load and parse a C file
//     /// Returns a map from file paths to parsed files.
//     pub fn load<P: AsRef<Path>>(&self, p: &P) {
//         println!("{}", p);
//         let config = Config::default();
//         // println!("{:?}", parse(&config, "example.c"));
//     }
// }