#![allow(unused_imports)]
use bellman::gadgets::test::TestConstraintSystem;
use bellman::Circuit;
use bls12_381::Scalar;
use circ::front::zokrates::{Inputs, Zokrates, Mode};
use circ::front::FrontEnd;
use circ::ir::opt::{opt, Opt};
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use env_logger;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[structopt(parse(from_os_str))]
    zokrates_path: PathBuf,

    /// File with input witness
    #[structopt(short, long, name = "FILE", parse(from_os_str))]
    inputs: Option<PathBuf>,

    /// Number of parties for an MPC. If missing, generates a proof circuit.
    #[structopt(short, long, name = "PARTIES")]
    parties: Option<u8>,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();
    println!("{:?}", options);
    let inputs = Inputs {
        file: options.zokrates_path,
        inputs: options.inputs,
        mode: match options.parties {
            Some(p) => Mode::Mpc(p),
            None => Mode::Proof,
        }
    };
    let cs = Zokrates::gen(inputs);
    let cs = opt(
        cs,
        vec![
            Opt::Flatten,
            Opt::Sha,
            Opt::ConstantFold,
            Opt::Flatten,
            Opt::FlattenAssertions,
            Opt::Inline,
            Opt::Mem,
            Opt::Flatten,
            Opt::FlattenAssertions,
            Opt::ConstantFold,
            Opt::Inline,
        ],
    );
    println!("Done with IR optimization");

    println!("Converting to r1cs");
    let r1cs = to_r1cs(cs, circ::front::zokrates::ZOKRATES_MODULUS.clone());
    println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
    let r1cs = reduce_linearities(r1cs);
    println!("Final R1cs size: {}", r1cs.constraints().len());

    //r1cs.check_all();
    //let mut cs = TestConstraintSystem::<Scalar>::new();
    //r1cs.synthesize(&mut cs).unwrap();
    //println!("Num constraints: {}", cs.num_constraints());
    //println!("{}", cs.pretty_print());
    //if let Some(c) = cs.which_is_unsatisfied() {
    //    panic!("Unsat: {}", c);
    //}
}
