//! Utility functions to write compiler output to ABY

use std::env;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::Path;

/// Get ABY source directory
pub fn get_aby_source() -> String {
    let key = "ABY_SOURCE";
    match env::var(key) {
        Ok(val) => val,
        Err(e) => panic!("Missing env variable: ABY_SOURCE, {}", e),
    }
}

/// Given Path `path` and String denominator `lang`, return the filename of the path
pub fn get_path(path: &Path, lang: &str, t: &str, create: bool) -> String {
    let filename = Path::new(&path.iter().last().unwrap())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap();

    let name = format!("{}_{}", filename, lang);
    let dir_path = format!("scripts/aby_tests/tests/{}", name);
    match fs::create_dir_all(&dir_path) {
        Err(why) => panic!("couldn't create {}: {}", dir_path, why),
        Ok(file) => file,
    };

    let file_path = format!("{}/{}_{}.txt", dir_path, name, t);
    if create {
        match File::create(&file_path) {
            Err(why) => panic!("couldn't create {}: {}", file_path, why),
            Ok(file) => file,
        };
    }
    file_path
}

/// Write lines to a path
pub fn write_lines(path: &str, lines: &[String]) {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap_or_else(|_| panic!("Failed to open file: {}", path));

    let data = lines.join("");
    file.write_all(data.as_bytes())
        .unwrap_or_else(|_| panic!("Failed to write to file: {}", path));
}
