/*
use bellman::gadgets::test::TestConstraintSystem;
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters, Proof, VerifyingKey,
};
use bellman::Circuit;
use bls12_381::{Bls12, Scalar};
*/
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::opt::{opt, Opt};
/*
use circ::target::r1cs::bellman::parse_instance;
*/
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
/*
use std::fs::File;
use std::io::Read;
use std::io::Write;
*/
use circ::cfg::{
    cfg,
    clap::{self, Parser, ValueEnum},
    CircOpt,
};
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(name = "zxc", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[arg(name = "PATH")]
    path: PathBuf,

    /*
    #[arg(long, default_value = "P", parse(from_os_str))]
    prover_key: PathBuf,

    #[arg(long, default_value = "V", parse(from_os_str))]
    verifier_key: PathBuf,

    #[arg(long, default_value = "pi", parse(from_os_str))]
    proof: PathBuf,

    #[arg(long, default_value = "x", parse(from_os_str))]
    instance: PathBuf,
    */
    #[arg(short = 'L')]
    /// skip linearity reduction entirely
    skip_linred: bool,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,

    #[arg(long, default_value = "count")]
    action: ProofAction,

    #[arg(short = 'q')]
    /// quiet mode: don't print R1CS at the end
    quiet: bool,
}

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum ProofAction {
    Count,
    Setup,
    Prove,
    Verify,
}

#[derive(PartialEq, Debug, Clone, ValueEnum)]
enum ProofOption {
    Count,
    Prove,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    println!("{options:?}");

    let cs = {
        let inputs = zsharp::Inputs {
            file: options.path,
            mode: Mode::Proof,
        };
        ZSharpFE::gen(inputs)
    };

    print!("Optimizing IR... ");
    let cs = opt(
        cs,
        vec![
            Opt::ScalarizeVars,
            Opt::Flatten,
            Opt::Sha,
            Opt::ConstantFold(Box::new([])),
            Opt::Flatten,
            Opt::Inline,
            // Tuples must be eliminated before oblivious array elim
            Opt::Tuple,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            // The obliv elim pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::LinearScan,
            // The linear scan pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
            Opt::Inline,
        ],
    );
    println!("done.");

    let action = options.action;
    /*
    let proof = options.proof;
    let prover_key = options.prover_key;
    let verifier_key = options.verifier_key;
    let instance = options.instance;
    */

    println!("Converting to r1cs");
    let r1cs = to_r1cs(cs.get("main"), cfg());
    let r1cs = if options.skip_linred {
        println!("Skipping linearity reduction, as requested.");
        r1cs
    } else {
        println!(
            "R1cs size before linearity reduction: {}",
            r1cs.constraints().len()
        );
        reduce_linearities(r1cs, cfg())
    };
    println!("Final R1cs size: {}", r1cs.constraints().len());
    match action {
        ProofAction::Count => {
            if !options.quiet {
                eprintln!("{:#?}", r1cs.constraints());
            }
        }
        ProofAction::Prove => {
            unimplemented!()
            /*
            println!("Proving");
            r1cs.check_all();
            let rng = &mut rand::thread_rng();
            let mut pk_file = File::open(prover_key).unwrap();
            let pk = Parameters::<Bls12>::read(&mut pk_file, false).unwrap();
            let pf = create_random_proof(&r1cs, &pk, rng).unwrap();
            let mut pf_file = File::create(proof).unwrap();
            pf.write(&mut pf_file).unwrap();
            */
        }
        ProofAction::Setup => {
            unimplemented!()
            /*
            let rng = &mut rand::thread_rng();
            let p =
                generate_random_parameters::<bls12_381::Bls12, _, _>(&r1cs, rng).unwrap();
            let mut pk_file = File::create(prover_key).unwrap();
            p.write(&mut pk_file).unwrap();
            let mut vk_file = File::create(verifier_key).unwrap();
            p.vk.write(&mut vk_file).unwrap();
            */
        }
        ProofAction::Verify => {
            unimplemented!()
            /*
            println!("Verifying");
            let mut vk_file = File::open(verifier_key).unwrap();
            let vk = VerifyingKey::<Bls12>::read(&mut vk_file).unwrap();
            let pvk = prepare_verifying_key(&vk);
            let mut pf_file = File::open(proof).unwrap();
            let pf = Proof::read(&mut pf_file).unwrap();
            let instance_vec = parse_instance(&instance);
            verify_proof(&pvk, &pf, &instance_vec).unwrap();
            */
        }
    };
}
