use bls12_381::Bls12;
use circ::ir::term::text::parse_value_map;
use circ::target::r1cs::bellman;
use circ::target::r1cs::spartan;
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
    #[structopt(long, default_value = "pin", parse(from_os_str))]
    pin: PathBuf,
    #[structopt(long, default_value = "vin", parse(from_os_str))]
    vin: PathBuf,
    #[structopt(long)]
    action: ProofAction,
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    /// `Prove`/`Verify` execute proving/verifying in bellman separately
    /// `Spartan` executes both proving/verifying in spartan
    enum ProofAction {
        Prove,
        Verify,
        Spartan,
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::from_args();
    match opts.action {
        ProofAction::Prove => {
            let input_map = parse_value_map(&std::fs::read(opts.inputs).unwrap());
            println!("Proving");
            bellman::prove::<Bls12, _, _>(opts.prover_key, opts.proof, &input_map).unwrap();
        }
        ProofAction::Verify => {
            let input_map = parse_value_map(&std::fs::read(opts.inputs).unwrap());
            println!("Verifying");
            bellman::verify::<Bls12, _, _>(opts.verifier_key, opts.proof, &input_map).unwrap();
        }
        ProofAction::Spartan => {
            let prover_input_map = parse_value_map(&std::fs::read(opts.pin).unwrap());
            println!("Spartan Proving");
            let (gens, inst, proof) = spartan::prove(opts.prover_key, &prover_input_map).unwrap();

            let verifier_input_map = parse_value_map(&std::fs::read(opts.vin).unwrap());
            println!("Spartan Verifying");
            spartan::verify(opts.verifier_key, &verifier_input_map, &gens, &inst, proof).unwrap();
        }
    }
}
