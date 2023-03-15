use circ::cfg::{
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;

use bls12_381::Bls12;
use circ::target::r1cs::{mirage, proof::CommitProofSystem};

#[derive(Debug, Parser)]
#[command(name = "zk", about = "The CirC Commit-Prove runner")]
struct Options {
    #[arg(long, default_value = "P")]
    prover_key: PathBuf,
    #[arg(long, default_value = "V")]
    verifier_key: PathBuf,
    #[arg(long, default_value = "pi")]
    proof: PathBuf,
    #[arg(long, default_value = "in")]
    inputs: PathBuf,
    #[arg(long)]
    /// Commitment randomness (path)
    rands: Vec<PathBuf>,
    #[arg(long)]
    /// Commitments (path)
    commits: Vec<PathBuf>,
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
    Commit,
    SampleRand,
}

type Mirage = mirage::Mirage<Bls12>;

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::parse();
    circ::cfg::set(&opts.circ);
    match opts.action {
        ProofAction::SampleRand => {
            for r in &opts.rands {
                Mirage::sample_com_rand_fs(r).unwrap();
            }
        }
        ProofAction::Prove => {
            Mirage::cp_prove_fs(&opts.prover_key, &opts.inputs, &opts.proof, opts.rands).unwrap();
        }
        ProofAction::Verify => {
            assert!(Mirage::cp_verify_fs(
                &opts.verifier_key,
                &opts.inputs,
                &opts.proof,
                opts.commits
            )
            .unwrap());
        }
        ProofAction::Commit => {
            assert_eq!(
                1,
                opts.rands.len(),
                "Must specify *one* commitment randomness path"
            );
            assert_eq!(1, opts.commits.len(), "Must specify *one* commitment path");
            Mirage::cp_commit_fs(
                &opts.verifier_key,
                &opts.inputs,
                &opts.rands[0],
                &opts.commits[0],
            )
            .unwrap();
        }
    }
}
