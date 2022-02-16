//! Utility functions to write compiler output to ABY

use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{prelude::*, BufRead, BufReader};
use std::path::Path;

/// Given Path `path`, return the filename of the path
fn get_filename(path: &Path) -> String {
    Path::new(&path.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap()
}

/// In ABY examples, remove the existing directory and create a directory
/// in order to write the new test case
fn create_dir_in_aby(filename: &str) {
    let path = format!("third_party/ABY/src/examples/{}", filename);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(format!("{}/common", path)).expect("Failed to create directory");
}

/// Update the CMake file in ABY
fn update_cmake_file(filename: &str) {
    let cmake_filename = "third_party/ABY/src/examples/CMakeLists.txt";
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
    let path = format!("third_party/ABY/src/examples/{}/CMakeLists.txt", filename);

    fs::write(
        &path,
        format!(
            concat!(
                "add_executable({}_test {}_test.cpp common/{}.cpp)\n",
                "target_link_libraries({}_test ABY::aby ENCRYPTO_utils::encrypto_utils)"
            ),
            filename, filename, filename, filename
        ),
    )
    .expect("Failed to write to cmake file");
}

/// Write the testcase in the ABY examples directory
fn write_test_file(filename: &str) {
    let template = fs::read_to_string("third_party/ABY_templates/test_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/{}_test.cpp",
        filename, filename
    );

    fs::write(&path, template.replace("{fn}", filename)).expect("Failed to write to test file");
}

/// Using the h_template.txt, write the .h file for the new test case
fn write_h_file(filename: &str) {
    let template = fs::read_to_string("third_party/ABY_templates/h_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/common/{}.h",
        filename, filename
    );

    fs::write(&path, template.replace("{fn}", &*filename)).expect("Failed to write to h file");
}

/// Using the cpp_template.txt, write the .cpp file for the new test case
fn write_circ_file(filename: &str) {
    let setup_file_path = format!("third_party/ABY/src/examples/{}_setup_tmp.txt", filename);
    let mut setup_file = File::open(setup_file_path).expect("Unable to open the file");
    let mut setup = String::new();
    setup_file
        .read_to_string(&mut setup)
        .expect("Unable to read the file");

    let circuit_file_path = format!("third_party/ABY/src/examples/{}_circuit_tmp.txt", filename);
    let mut circuit_file = File::open(circuit_file_path).expect("Unable to open the file");
    let mut circuit = String::new();
    circuit_file
        .read_to_string(&mut circuit)
        .expect("Unable to read the file");

    let content = format!("{}\n{}", setup, circuit);

    let template = fs::read_to_string("third_party/ABY_templates/cpp_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/common/{}.cpp",
        filename, filename
    );

    fs::write(
        &path,
        template
            .replace("{fn}", &*filename)
            .replace("{circ}", &content),
    )
    .expect("Failed to write to cpp file");
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
