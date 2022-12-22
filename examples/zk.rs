use bls12_381::Bls12;
use circ::cfg::clap::{self, Parser, ValueEnum};
use circ::ir::term::text::parse_value_map;
use circ::target::r1cs::bellman;
use circ::target::r1cs::spartan;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(name = "zk", about = "The CirC ZKP runner")]
struct Options {
    #[arg(long, default_value = "P")]
    prover_key: PathBuf,
    #[arg(long, default_value = "V")]
    verifier_key: PathBuf,
    #[arg(long, default_value = "pi")]
    proof: PathBuf,
    #[arg(long, default_value = "in")]
    inputs: PathBuf,
    #[arg(long, default_value = "pin")]
    pin: PathBuf,
    #[arg(long, default_value = "vin")]
    vin: PathBuf,
    #[arg(long)]
    action: ProofAction,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
/// `Prove`/`Verify` execute proving/verifying in bellman separately
/// `Spartan` executes both proving/verifying in spartan
enum ProofAction {
    Prove,
    Verify,
    Spartan,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::parse();
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
