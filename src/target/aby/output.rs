//! Utility functions to write compiler output to ABY

use crate::target::aby::*;
use std::fs;
use std::fs::{File, OpenOptions};
use std::io::{prelude::*, BufRead, BufReader};
use std::path::Path;
use std::path::PathBuf;

fn get_filename(path_buf: PathBuf) -> String {
    Path::new(&path_buf.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap()
}

fn create_dir_in_aby(filename: &String) {
    let path = format!("third_party/ABY/src/examples/{}", *filename);
    fs::remove_dir_all(path.clone());
    fs::create_dir_all(format!("{}/common", path.clone())).expect("Failed to create directory");
}

fn update_cmake_file(filename: &String) {
    let cmake_filename = "third_party/ABY/src/examples/CMakeLists.txt";
    let file = File::open(cmake_filename.clone()).expect("Failed to open cmake file");
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

        writeln!(file, "{}", format!("add_subdirectory({})", *filename))
            .expect("Failed to write to cmake file");
    }
}

fn write_test_cmake_file(filename: &String) {
    let path = format!("third_party/ABY/src/examples/{}/CMakeLists.txt", *filename);

    fs::write(
        path.clone(),
        format!(
            concat!(
                "add_executable({}_test {}_test.cpp common/{}.cpp)\n",
                "target_link_libraries({}_test ABY::aby ENCRYPTO_utils::encrypto_utils)"
            ),
            *filename, *filename, *filename, *filename
        ),
    )
    .expect("Failed to write to cmake file");
}

fn write_test_file(filename: &String) {
    let template = fs::read_to_string("third_party/ABY_templates/test_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/{}_test.cpp",
        *filename, *filename
    );

    fs::write(path.clone(), template.replace("{fn}", &*filename))
        .expect("Failed to write to cmake file");
}

fn write_h_file(filename: &String) {
    let template = fs::read_to_string("third_party/ABY_templates/h_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/common/{}.h",
        *filename, *filename
    );

    fs::write(path.clone(), template.replace("{fn}", &*filename))
        .expect("Failed to write to cmake file");
}

fn write_circ_file(filename: &String, circ: String) {
    let template = fs::read_to_string("third_party/ABY_templates/cpp_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/ABY/src/examples/{}/common/{}.cpp",
        *filename, *filename
    );

    fs::write(
        path.clone(),
        template
            .replace("{fn}", &*filename)
            .replace("{circ}", &circ),
    )
    .expect("Failed to write to cmake file");
}

/// Write circ-aby output to ABY to compile executables
pub fn write_aby_exec(aby: ABY, path_buf: PathBuf) {
    let filename = get_filename(path_buf);
    create_dir_in_aby(&filename);
    update_cmake_file(&filename);
    write_test_cmake_file(&filename);
    write_test_file(&filename);
    write_h_file(&filename);
    let circ_str = aby.setup.join("\n\t") + &aby.circs.join("\n\t") + &aby.closer.join("\n\t");
    write_circ_file(&filename, circ_str);
}
