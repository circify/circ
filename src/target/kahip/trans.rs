use crate::ir::term::*;

use crate::target::aby::assignment::ShareType;
use crate::target::aby::assignment::SharingMap;

use std::collections::HashMap;
use std::path::Path;
use std::time::Duration;
use std::time::Instant;

use std::fs;

// Get file path to write Chaco graph to
fn get_graph_path(path: &Path, lang: &str) -> String {
    let filename = Path::new(&path.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap();
    let name = format!("{}_{}", filename, lang);
    let mut path = format!("scripts/aby_tests/tests/{}.graph", name);
    if Path::new(&path).exists() {
        fs::remove_file(&path).expect("Failed to remove old graph file");
    }
    path
}
