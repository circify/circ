use std::env::args;
use circ::front::FrontEnd;
use circ::front::zokrates::{Zokrates, Inputs};
use std::path::PathBuf;
use env_logger;

fn main() {
    env_logger::init();
    let inputs = Inputs {
        file: PathBuf::from(args().nth(1).unwrap()),
        inputs: None,
    };
    let cs = Zokrates::gen(inputs);
}
