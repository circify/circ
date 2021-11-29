#![allow(unused_imports)]
use bellman::gadgets::test::TestConstraintSystem;
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters, VerifyingKey, Proof,
};
use bellman::Circuit;
use bls12_381::{Scalar, Bls12};
use circ::front::zokrates::{Inputs, Mode, Zokrates};
use circ::front::FrontEnd;
use circ::ir::opt::{opt, Opt};
use circ::target::aby::output::write_aby_exec;
use circ::target::aby::trans::to_aby;
use circ::target::ilp::trans::to_ilp;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use env_logger;
use good_lp::default_solver;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use structopt::clap::arg_enum;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options2 {
    /// Input file
    #[structopt(parse(from_os_str), name = "PATH")]
    path: PathBuf,

    #[structopt(flatten)]
    frontend: FrontendOptions,

    /// Number of parties for an MPC.
    #[structopt(long, default_value = "2", name = "PARTIES")]
    parties: u8,

    #[structopt(subcommand)]
    backend: Backend,
}

#[derive(Debug, StructOpt)]
struct FrontendOptions {
    /// Input language
    #[structopt(long, default_value = "auto", name = "LANG")]
    language: Langauge,

    /// Value threshold
    #[structopt(long)]
    value_threshold: Option<u64>,

    /// File with input witness
    #[structopt(long, name = "FILE", parse(from_os_str))]
    inputs: Option<PathBuf>,
}

#[derive(Debug, StructOpt)]
enum Backend {
    R1cs {
        #[structopt(long, default_value = "P", parse(from_os_str))]
        prover_key: PathBuf,
        #[structopt(long, default_value = "V", parse(from_os_str))]
        verifier_key: PathBuf,
        #[structopt(long, default_value = "pi", parse(from_os_str))]
        proof: PathBuf,
        #[structopt(long, default_value = "x", parse(from_os_str))]
        instance: PathBuf,
        #[structopt(long, default_value = "count")]
        action: ProofAction,
    },
    Smt {},
    Ilp {},
    Mpc {},
}

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

    /// Whether to maximize the output
    #[structopt(short, long)]
    maximize: bool,

    /// Whether to find an prove knowledge of inputs that yeild an output of sufficiently large
    /// value.
    #[structopt(long)]
    prove_high_value: Option<u64>,

    /// What do do with the R1CS.
    #[structopt(long, default_value = "count")]
    proof_action: ProofOption,
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum Langauge {
        ZoKrates,
        Datalog,
        Auto,
    }
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum ProofAction {
        Count,
        Prove,
        Setup,
        Verify,
    }
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum ProofOption {
        Count,
        Prove,
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options2::from_args();
    let path_buf = options.path.clone();
    println!("{:?}", options);
    let mode = match options.backend {
        Backend::R1cs { .. } => Mode::Proof,
        Backend::Ilp { .. } => Mode::Opt,
        Backend::Mpc { .. } => Mode::Mpc(options.parties),
        Backend::Smt { .. } => unimplemented!(),
    };
    let inputs = Inputs {
        file: options.path,
        inputs: options.frontend.inputs,
        mode: mode.clone(),
    };
    let cs = Zokrates::gen(inputs);
    let cs = match mode {
        Mode::Opt => opt(cs, vec![Opt::ConstantFold]),
        Mode::Mpc(_) => opt(
            cs,
            vec![],
            // vec![Opt::Sha, Opt::ConstantFold, Opt::Mem, Opt::ConstantFold],
        ),
        Mode::Proof | Mode::ProofOfHighValue(_) => opt(
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
        ),
    };
    println!("Done with IR optimization");

    match options.backend {
        Backend::R1cs { action, proof, prover_key, verifier_key, .. } => {
            println!("Converting to r1cs");
            let r1cs = to_r1cs(cs, circ::front::zokrates::ZOKRATES_MODULUS.clone());
            println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
            let r1cs = reduce_linearities(r1cs);
            match action {
                ProofAction::Count => {
                    println!("Final R1cs size: {}", r1cs.constraints().len());
                }
                ProofAction::Prove => {
                    println!("Proving");
                    let rng = &mut rand::thread_rng();
                    let mut pk_file = File::open(prover_key).unwrap();
                    let pk = Parameters::<Bls12>::read(&mut pk_file, false).unwrap();
                    let pf = create_random_proof(&r1cs, &pk, rng).unwrap();
                    let mut pf_file = File::create(proof).unwrap();
                    pf.write(&mut pf_file).unwrap();
                }
                ProofAction::Setup => {
                    let rng = &mut rand::thread_rng();
                    let p =
                        generate_random_parameters::<bls12_381::Bls12, _, _>(&r1cs, rng).unwrap();
                    let mut pk_file = File::create(prover_key).unwrap();
                    p.write(&mut pk_file).unwrap();
                    let mut vk_file = File::create(verifier_key).unwrap();
                    p.vk.write(&mut vk_file).unwrap();
                }
                ProofAction::Verify => {
                    println!("Verifying");
                    let mut vk_file = File::open(verifier_key).unwrap();
                    let vk = VerifyingKey::<Bls12>::read(&mut vk_file).unwrap();
                    let pvk = prepare_verifying_key(&vk);
                    let mut pf_file = File::open(proof).unwrap();
                    let pf = Proof::read(&mut pf_file).unwrap();
                    verify_proof(&pvk, &pf, &[]).unwrap();
                }
            }
        }
        Backend::Mpc { .. } => {
            println!("Converting to aby");
            let aby = to_aby(cs);
            write_aby_exec(aby, path_buf);
        }
        Backend::Ilp { .. } => {
            println!("Converting to ilp");
            let ilp = to_ilp(cs);
            let solver_result = ilp.solve(default_solver);
            let (max, vars) = solver_result.expect("ILP could not be solved");
            println!("Max value: {}", max.round() as u64);
            println!("Assignment:");

            for (var, val) in &vars {
                println!("  {}: {}", var, val.round() as u64);
            }
            let mut f = File::create("assignment.txt").unwrap();
            for (var, val) in &vars {
                if var.contains("f0") {
                    let i = var.find("f0").unwrap();
                    let s = &var[i + 8..];
                    let e = s.find("_").unwrap();
                    writeln!(f, "{} {}", &s[..e], val.round() as u64).unwrap();
                }
            }
        }
        Backend::Smt { .. } => {
            todo!()
        }
    }
}
