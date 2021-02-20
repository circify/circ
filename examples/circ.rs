use std::env::args;
use circ::front::FrontEnd;
use circ::front::zokrates::{Zokrates, Inputs};
use std::path::PathBuf;
use env_logger;

fn main() {
    env_logger::Builder::from_default_env().format_level(false).format_timestamp(None).init();
    let inputs = Inputs {
        file: PathBuf::from(args().nth(1).unwrap()),
        inputs: None,
    };
    let cs = Zokrates::gen(inputs);
}
