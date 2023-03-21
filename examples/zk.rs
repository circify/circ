use circ::cfg::{
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;

#[cfg(feature = "bellman")]
use bls12_381::Bls12;
#[cfg(feature = "bellman")]
use circ::target::r1cs::{bellman::Bellman, mirage::Mirage, proof::ProofSystem};

#[cfg(feature = "spartan")]
use circ::ir::term::text::parse_value_map;
#[cfg(feature = "spartan")]
use circ::target::r1cs::spartan;

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
    #[arg(long, default_value = "groth16")]
    proof_impl: ProofImpl,
    #[arg(long)]
    action: ProofAction,
    #[command(flatten)]
    circ: CircOpt,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
/// `Prove`/`Verify` execute proving/verifying in bellman separately
/// `Spartan` executes both proving/verifying in spartan
enum ProofAction {
    Prove,
    Verify,
    Spartan,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
/// Whether to use Groth16 or Mirage
enum ProofImpl {
    Groth16,
    Mirage,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::parse();
    circ::cfg::set(&opts.circ);
    match (opts.action, opts.proof_impl) {
        #[cfg(feature = "bellman")]
        (ProofAction::Prove, ProofImpl::Groth16) => {
            println!("Proving");
            Bellman::<Bls12>::prove_fs(opts.prover_key, opts.inputs, opts.proof).unwrap();
        }
        #[cfg(feature = "bellman")]
        (ProofAction::Prove, ProofImpl::Mirage) => {
            println!("Proving");
            Mirage::<Bls12>::prove_fs(opts.prover_key, opts.inputs, opts.proof).unwrap();
        }
        #[cfg(feature = "bellman")]
        (ProofAction::Verify, ProofImpl::Groth16) => {
            println!("Verifying");
            assert!(
                Bellman::<Bls12>::verify_fs(opts.verifier_key, opts.inputs, opts.proof).unwrap(),
                "invalid proof"
            );
        }
        #[cfg(feature = "bellman")]
        (ProofAction::Verify, ProofImpl::Mirage) => {
            println!("Verifying");
            assert!(
                Mirage::<Bls12>::verify_fs(opts.verifier_key, opts.inputs, opts.proof).unwrap(),
                "invalid proof"
            );
        }
        #[cfg(not(feature = "bellman"))]
        (ProofAction::Prove | ProofAction::Verify, _) => panic!("Missing feature: bellman"),
        #[cfg(feature = "spartan")]
        (ProofAction::Spartan, _) => {
            let prover_input_map = parse_value_map(&std::fs::read(opts.pin).unwrap());
            println!("Spartan Proving");
            let (gens, inst, proof) = spartan::prove(opts.prover_key, &prover_input_map).unwrap();

            let verifier_input_map = parse_value_map(&std::fs::read(opts.vin).unwrap());
            println!("Spartan Verifying");
            spartan::verify(opts.verifier_key, &verifier_input_map, &gens, &inst, proof).unwrap();
        }
        #[cfg(not(feature = "spartan"))]
        (ProofAction::Spartan, _) => panic!("Missing feature: spartan"),
    }
}
