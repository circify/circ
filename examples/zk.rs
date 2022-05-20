use bls12_381::Bls12;
use circ::ir::term::text::parse_value_map;
use circ::target::r1cs::bellman::{prove, verify};
use std::path::PathBuf;
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    #[structopt(long, default_value = "P", parse(from_os_str))]
    prover_key: PathBuf,
    #[structopt(long, default_value = "V", parse(from_os_str))]
    verifier_key: PathBuf,
    #[structopt(long, default_value = "pi", parse(from_os_str))]
    proof: PathBuf,
    #[structopt(long, default_value = "in", parse(from_os_str))]
    inputs: PathBuf,
    #[structopt(long)]
    action: ProofAction,
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum ProofAction {
        Prove,
        Verify,
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::from_args();
    let input_map = parse_value_map(&std::fs::read(opts.inputs).unwrap());
    match opts.action {
        ProofAction::Prove => {
            println!("Proving");
            prove::<Bls12, _, _>(opts.prover_key, opts.proof, &input_map).unwrap();
        }
        ProofAction::Verify => {
            println!("Verifying");
            verify::<Bls12, _, _>(opts.verifier_key, opts.proof, &input_map).unwrap();
        }
    }
}
