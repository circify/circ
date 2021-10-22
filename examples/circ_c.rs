#![allow(unused_imports)]
use bellman::gadgets::test::TestConstraintSystem;
use bellman::Circuit;
use bls12_381::Scalar;
use circ::front::c::{Inputs, Mode, C};
use circ::front::FrontEnd;
use circ::ir::opt::{opt, Opt};
use circ::target::aby::output::write_aby_exec;
use circ::target::aby::trans::to_aby;
use circ::target::ilp::trans::to_ilp;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use env_logger;
use good_lp::default_solver;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[structopt(parse(from_os_str))]
    input_file_path: PathBuf,

    /// File with input witness
    #[structopt(short, long, name = "FILE", parse(from_os_str))]
    inputs: Option<PathBuf>,

    /// Number of parties for an MPC. If missing, generates a proof circuit.
    #[structopt(short, long, name = "PARTIES")]
    parties: Option<u8>,

    /// Whether to maximize the output
    #[structopt(short, long)]
    maximize: bool,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();
    let path_buf = options.input_file_path.clone();
    println!("{:?}", options);
    let mode = if options.maximize {
        Mode::Opt
    } else {
        match options.parties {
            Some(p) => Mode::Mpc(p),
            None => Mode::Proof,
        }
    };
    let inputs = Inputs {
        file: options.input_file_path,
        inputs: options.inputs,
        mode: mode.clone(),
    };

    let cs = C::gen(inputs);
    println!("{:#?}", cs);
    let cs = match mode {
        Mode::Mpc(_) => opt(
            cs,
            vec![Opt::Sha, Opt::ConstantFold, Opt::Mem, Opt::ConstantFold],
        ),
        _ => unimplemented!(),
    };
    println!("Done with IR optimization");

    match mode {
        Mode::Mpc(_) => {
            println!("Converting to aby");
            let aby = to_aby(cs);
            write_aby_exec(aby, "c".to_string(), path_buf);
        }
        _ => unimplemented!(),
    }
}
