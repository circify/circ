#[cfg(feature = "r1cs")]
use bls12_381::Bls12;
#[cfg(feature = "r1cs")]
use circ::ir::term::text::parse_value_map;
#[cfg(feature = "r1cs")]
use circ::target::r1cs::bellman::{prove, verify};
#[cfg(feature = "r1cs")]
use std::path::PathBuf;
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    #[cfg(feature = "r1cs")]
    #[structopt(long, default_value = "P", parse(from_os_str))]
    prover_key: PathBuf,
    #[cfg(feature = "r1cs")]
    #[structopt(long, default_value = "V", parse(from_os_str))]
    verifier_key: PathBuf,
    #[cfg(feature = "r1cs")]
    #[structopt(long, default_value = "pi", parse(from_os_str))]
    proof: PathBuf,
    #[cfg(feature = "r1cs")]
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
    #[cfg(feature = "r1cs")]
    let input_map = parse_value_map(&std::fs::read(opts.inputs).unwrap());
    match opts.action {
        ProofAction::Prove => {
            println!("Proving");
            #[cfg(feature = "r1cs")]
            prove::<Bls12, _, _>(opts.prover_key, opts.proof, &input_map).unwrap();
        }
        ProofAction::Verify => {
            println!("Verifying");
            #[cfg(feature = "r1cs")]
            verify::<Bls12, _, _>(opts.verifier_key, opts.proof, &input_map).unwrap();
        }
    }
}
