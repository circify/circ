use circ::front::FrontEnd;
use circ::front::zokrates::{Zokrates, Inputs};
use circ::ir::opt::{opt,Opt};
use circ::target::r1cs::trans::to_r1cs;
use circ::target::r1cs::opt::reduce_linearities;
use std::path::PathBuf;
use env_logger;
use bellman::Circuit;
use bellman::gadgets::test::TestConstraintSystem;
use bls12_381::Scalar;
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
}

fn main() {
    env_logger::Builder::from_default_env().format_level(false).format_timestamp(None).init();
    let options = Options::from_args();
    println!("{:?}", options);
    let inputs = Inputs {
        file: options.zokrates_path,
        inputs: options.inputs,
    };
    let cs = Zokrates::gen(inputs);
    let cs = opt(cs, vec![Opt::Flatten, Opt::Sha, Opt::ConstantFold, Opt::Flatten, Opt::FlattenAssertions, Opt::Inline, Opt::Mem, Opt::Flatten, Opt::FlattenAssertions, Opt::ConstantFold, Opt::Inline]);
    println!("Converting to r1cs");
    let r1cs = to_r1cs(cs, circ::front::zokrates::term::ZOKRATES_MODULUS.clone());
    println!("R1cs size: {}", r1cs.constraints().len());
    let r1cs = reduce_linearities(r1cs);
    println!("R1cs size: {}", r1cs.constraints().len());
    r1cs.check_all();
    let mut cs = TestConstraintSystem::<Scalar>::new();
    r1cs.synthesize(&mut cs).unwrap();
    println!("Num constraints: {}", cs.num_constraints());
    println!("{}", cs.pretty_print());
    if let Some(c) = cs.which_is_unsatisfied() {
        panic!("Unsat: {}", c);
    }
}
