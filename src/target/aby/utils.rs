//! Utility functions to write compiler output to ABY

use std::fs;
use std::io::prelude::*;
use std::path::Path;

/// Given Path `path` and String denominator `lang`, return the filename of the path
pub fn get_path(path: &Path, lang: &str, t: &str) -> String {
    let filename = Path::new(&path.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap();

    let name = format!("{}_{}", filename, lang);

    // TODO: clean
    let path = format!("third_party/ABY/src/examples/{}_{}_tmp.txt", name, t);

    if Path::new(&path).exists() {
        fs::remove_file(&path).expect("Failed to remove old circuit_tmp file");
    }
    path
}

/// Write circuit output to temporary file
pub fn write_line_to_file(path: &str, line: &str) {
    if !Path::new(&path).exists() {
        fs::File::create(&path).expect("Failed to create tmp file");
    }

    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open(path)
        .expect("Failed to open circuit_tmp file");

    file.write_all(line.as_bytes())
        .expect("Failed to write to circuit_tmp file");
}
