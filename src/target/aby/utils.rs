//! Utility functions to write compiler output to ABY

use std::env;
use std::fs;
use std::io::prelude::*;
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
pub fn get_path(path: &Path, lang: &str, t: &str) -> String {
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
    match fs::File::create(&file_path) {
        Err(why) => panic!("couldn't create {}: {}", file_path, why),
        Ok(file) => file,
    };
    file_path
}

/// Write lines to a path
pub fn write_l(file: &mut fs::File, path: &str, lines: &[String]) {
    let data = lines.join("");
    file.write_all(data.as_bytes())
        .expect(&format!("Failed to write to file: {}", path));
}

/// Write lines to a path
pub fn write_lines(path: &str, lines: &[String]) {
    if !Path::new(&path).exists() {
        fs::File::create(&path).expect(&*format!("Failed to create: {}", path));
    }

    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open(&path)
        .expect(&format!("Failed to open file: {}", path));

    let data = lines.join("");
    file.write_all(data.as_bytes())
        .expect(&format!("Failed to write to file: {}", path));
}
