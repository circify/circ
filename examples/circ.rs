use std::env::args;
use circ::front::FrontEnd;
use circ::front::zokrates::{Zokrates, Inputs};
use circ::ir::opt::{opt,Opt};
use circ::ir::term::extras::Letified;
use circ::ir::term::*;
use circ::target::r1cs::trans::to_r1cs;
use circ::target::r1cs::opt::reduce_linearities;
use std::path::PathBuf;
use env_logger;

fn main() {
    env_logger::Builder::from_default_env().format_level(false).format_timestamp(None).init();
    let inputs = Inputs {
        file: PathBuf::from(args().nth(1).unwrap()),
        inputs: None,
    };
    let cs = Zokrates::gen(inputs);
    let cs = opt(cs, vec![Opt::ConstantFold, Opt::Flatten, Opt::FlattenAssertions, Opt::Inline, Opt::Mem, Opt::Flatten, Opt::FlattenAssertions, Opt::ConstantFold, Opt::Inline]);
    let r1cs = to_r1cs(cs, circ::front::zokrates::term::ZOKRATES_MODULUS.clone());
    println!("R1cs size: {}", r1cs.constraints().len());
    let r1cs = reduce_linearities(r1cs);
    println!("R1cs size: {}", r1cs.constraints().len());
}
