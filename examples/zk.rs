use bls12_381::Bls12;
use circ::ir::term::text::parse_value_map;
use circ::target::r1cs::bellman::{prove, verify};
use std::path::PathBuf;
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[cfg(feature = "marlin")]
use ark_bls12_381::{Bls12_381, Fr as BlsFr};
#[cfg(feature = "marlin")]
use ark_marlin::SimpleHashFiatShamirRng;
#[cfg(feature = "marlin")]
use ark_poly::univariate::DensePolynomial;
#[cfg(feature = "marlin")]
use ark_poly_commit::marlin::marlin_pc::MarlinKZG10;
#[cfg(feature = "marlin")]
use circ::target::r1cs::marlin;
#[cfg(feature = "marlin")]
use rand_chacha::ChaChaRng;
#[cfg(feature = "marlin")]
use sha2::Sha256;

#[cfg(feature = "mirage")]
use circ::target::r1cs::mirage;

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
    #[structopt(long, default_value = "groth")]
    proof_system: ProofSystem,
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum ProofAction {
        Prove,
        Verify,
    }
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum ProofSystem {
        Groth,
        Marlin,
        Mirage,
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
            println!("Proving ({})", opts.proof_system);
            match opts.proof_system {
                ProofSystem::Groth => {
                    prove::<Bls12, _, _>(opts.prover_key, opts.proof, &input_map).unwrap();
                }
                #[cfg(feature = "marlin")]
                ProofSystem::Marlin => {
                    marlin::prove::<
                        BlsFr,
                        MarlinKZG10<Bls12_381, DensePolynomial<BlsFr>>,
                        SimpleHashFiatShamirRng<Sha256, ChaChaRng>,
                        _,
                        _,
                    >(opts.prover_key, opts.proof, &input_map)
                    .unwrap();
                }
                #[cfg(not(feature = "marlin"))]
                ProofSystem::Marlin => {
                    panic!("Missing feature: marlin");
                }
                #[cfg(feature = "mirage")]
                ProofSystem::Mirage => {
                    mirage::prove::<Bls12, _, _>(opts.prover_key, opts.proof, &input_map).unwrap();
                }
                #[cfg(not(feature = "mirage"))]
                ProofSystem::Mirage => {
                    panic!("Missing feature: mirage");
                }
            }
        }
        ProofAction::Verify => {
            println!("Verifying ({})", opts.proof_system);
            match opts.proof_system {
                ProofSystem::Groth => {
                    verify::<Bls12, _, _>(opts.verifier_key, opts.proof, &input_map).unwrap();
                }
                #[cfg(feature = "marlin")]
                ProofSystem::Marlin => {
                    marlin::verify::<
                        BlsFr,
                        MarlinKZG10<Bls12_381, DensePolynomial<BlsFr>>,
                        SimpleHashFiatShamirRng<Sha256, ChaChaRng>,
                        _,
                        _,
                    >(opts.verifier_key, opts.proof, &input_map)
                    .unwrap();
                }
                #[cfg(not(feature = "marlin"))]
                ProofSystem::Marlin => {
                    panic!("Missing feature: marlin");
                }
                #[cfg(feature = "mirage")]
                ProofSystem::Mirage => {
                    mirage::verify::<Bls12, _, _>(opts.verifier_key, opts.proof, &input_map)
                        .unwrap();
                }
                #[cfg(not(feature = "mirage"))]
                ProofSystem::Mirage => {
                    panic!("Missing feature: mirage");
                }
            }
        }
    }
}
