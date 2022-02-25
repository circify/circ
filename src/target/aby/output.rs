//! Utility functions to write compiler output to ABY

use crate::target::aby::utils::get_aby_source;
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{prelude::*, BufRead, BufReader};
use std::path::Path;

/// Given Path `path`, return the filename of the path
fn get_filename(path: &Path) -> String {
    Path::new(&path.iter().last().unwrap())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap()
}

/// Given Path `path` and &str `content`, check if the file contents match
fn check_file_contents_match(path: &str, content: &str) -> bool {
    if !Path::new(path).exists() {
        false
    } else {
        let old_content = fs::read_to_string(path).expect("Failed to read file");
        old_content.trim() == content.trim()
    }
}

/// Create a new directory to write ABY test case
fn create_dir_in_aby(filename: &str) {
    let path = format!("{}/src/examples/{}", get_aby_source(), filename);
    fs::create_dir_all(format!("{}/common", path)).expect("Failed to create directory");
}

/// Update the CMake file in ABY
fn update_cmake_file(filename: &str) {
    let cmake_filename = format!("{}/src/examples/CMakeLists.txt", get_aby_source());
    let file = File::open(&cmake_filename).expect("Failed to open cmake file");
    let reader = BufReader::new(file);
    let mut flag = false;

    for line in reader.lines() {
        let line = line.unwrap();
        if line.contains(&*filename) {
            flag = true
        }
    }

    if !flag {
        let mut file = OpenOptions::new()
            .write(true)
            .append(true)
            .open(cmake_filename)
            .unwrap();

        writeln!(file, "add_subdirectory({})", filename).expect("Failed to write to cmake file");
    }
}

/// Create a CMake file for the corresponding filename (testcase)
/// in the ABY examples directory
fn write_test_cmake_file(filename: &str) {
    let path = format!(
        "{}/src/examples/{}/CMakeLists.txt",
        get_aby_source(),
        filename
    );

    let content = format!(
        concat!(
            "add_executable({}_test {}_test.cpp common/{}.cpp)\n",
            "target_link_libraries({}_test ABY::aby ENCRYPTO_utils::encrypto_utils)"
        ),
        filename, filename, filename, filename
    );

    if !check_file_contents_match(&path, &content) {
        fs::write(&path, content).expect("Failed to write to cmake file");
    }
}

/// Write the testcase in the ABY examples directory
fn write_test_file(filename: &str) {
    let template = fs::read_to_string("third_party/ABY_templates/test_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "{}/src/examples/{}/{}_test.cpp",
        get_aby_source(),
        filename,
        filename
    );

    let content = template.replace("{fn}", filename);

    if !check_file_contents_match(&path, &content) {
        fs::write(&path, content).expect("Failed to write to test file");
    }
}

/// Using the h_template.txt, write the .h file for the new test case
fn write_h_file(filename: &str) {
    let template = fs::read_to_string("third_party/ABY_templates/h_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "{}/src/examples/{}/common/{}.h",
        get_aby_source(),
        filename,
        filename
    );

    let content = template.replace("{fn}", filename);

    if !check_file_contents_match(&path, &content) {
        fs::write(&path, content).expect("Failed to write to h file");
    }
}

/// Using the cpp_template.txt, write the .cpp file for the new test case
fn write_circ_file(filename: &str) {
    let setup_file_path = format!(
        "{}/src/examples/{}_setup_tmp.txt",
        get_aby_source(),
        filename
    );
    let mut setup_file = File::open(setup_file_path).expect("Unable to open the file");
    let mut setup = String::new();
    setup_file
        .read_to_string(&mut setup)
        .expect("Unable to read the file");

    let circuit_file_path = format!(
        "{}/src/examples/{}_circuit_tmp.txt",
        get_aby_source(),
        filename
    );
    let mut circuit_file = File::open(circuit_file_path).expect("Unable to open the file");
    let mut circuit = String::new();
    circuit_file
        .read_to_string(&mut circuit)
        .expect("Unable to read the file");

    let complete_circuit = format!("{}\n{}", setup, circuit);

    let template = fs::read_to_string("third_party/ABY_templates/cpp_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "{}/src/examples/{}/common/{}.cpp",
        get_aby_source(),
        filename,
        filename
    );

    let content = template
        .replace("{fn}", filename)
        .replace("{circ}", &complete_circuit);

    if !check_file_contents_match(&path, &content) {
        fs::write(&path, content).expect("Failed to write to cpp file");
    }
}

/// Write circuit output from translation later to ABY
pub fn write_aby_exec(path: &Path, lang: &str) {
    let filename = get_filename(path);
    let name = format!("{}_{}", filename, lang);
    create_dir_in_aby(&name);
    update_cmake_file(&name);
    write_test_cmake_file(&name);
    write_test_file(&name);
    write_h_file(&name);
    write_circ_file(&name);
}
