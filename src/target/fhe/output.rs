//! Utility functions to write compiler output to FHE

use crate::target::fhe::*;
use std::fs;
//use std::fs::{File, OpenOptions};
//use std::io::{prelude::*, BufRead, BufReader};
use std::path::Path;
use std::path::PathBuf;

/// Given PathBuf `path_buf`, return the filename of the path
fn get_filename(path_buf: PathBuf) -> String {
    Path::new(&path_buf.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap()
}

/// In ABY examples, remove the existing directory and create a directory
/// in order to write the new test case
fn create_dir_in_seal(filename: &str) {
    let path = format!("third_party/SEAL/native/examples/{}", filename);
    let _ = fs::remove_dir_all(&path);
    fs::create_dir_all(format!("{}/common", path)).expect("Failed to create directory");
}

/// Using the cpp_template.txt, write the .cpp file for the new test case
fn write_circ_file(
    filename: &str,
    header_inputs: &str,
    server: &str,
    setup: &str,
    call_inputs: &str,
    post_computation: &str,
    main_inputs: &str,
) {
    let template = fs::read_to_string("third_party/SEAL_templates/cpp_template.txt")
        .expect("Unable to read file");
    let path = format!(
        "third_party/SEAL/native/examples/{}/common/{}.cpp",
        filename, filename
    );

    fs::write(
        &path,
        template
            .replace("{header_inputs}", header_inputs)
            .replace("{server}", server)
            .replace("{setup}", setup)
            .replace("{call_inputs}", call_inputs)
            .replace("{post_computation}", post_computation)
            .replace("{main_inputs}", main_inputs),
    )
    .expect("Failed to write to cpp file");
}

/// Write cpp output from translation later to FHE
pub fn write_fhe_exec(fhe: FHE, path_buf: PathBuf) {
    let filename = get_filename(path_buf);
    create_dir_in_seal(&filename);
    //update_cmake_file(&filename);
    //write_test_cmake_file(&filename);
    //write_test_file(&filename);
    //write_h_file(&filename);
    write_circ_file(
        &filename,
        &fhe.header_inputs.join(""),
        &fhe.server.join("\n\t"),
        &fhe.setup.join("\n\t"),
        &fhe.call_inputs.join(""),
        &fhe.post_computation.join("\n\t"),
        &fhe.main_inputs.join(""),
    );
}
