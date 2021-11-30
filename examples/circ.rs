#![allow(unused_imports)]
use bellman::gadgets::test::TestConstraintSystem;
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters, VerifyingKey, Proof,
};
use bellman::Circuit;
use bls12_381::{Scalar, Bls12};
use circ::front::datalog::{self, Datalog};
use circ::front::zokrates::{self, Mode, Zokrates};
use circ::front::FrontEnd;
use circ::ir::{opt::{opt, Opt}, term::extras::Letified};
use circ::target::aby::output::write_aby_exec;
use circ::target::aby::trans::to_aby;
use circ::target::ilp::trans::to_ilp;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use circ::target::smt::find_model;
use env_logger;
use good_lp::default_solver;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;
use structopt::clap::arg_enum;
use std::io::Read;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
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
    language: Language,

    /// Value threshold
    #[structopt(long)]
    value_threshold: Option<u64>,

    /// File with input witness
    #[structopt(long, name = "FILE", parse(from_os_str))]
    inputs: Option<PathBuf>,

    /// How many recursions to allow (datalog)
    #[structopt(short, long, name = "N", default_value = "5")]
    rec_limit: usize,

    /// Lint recursions that are allegedly primitive recursive (datalog)
    #[structopt(long)]
    lint_prim_rec: bool,
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

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum Language {
        Zokrates,
        Datalog,
        Auto,
    }
}

#[derive(PartialEq, Debug)]
enum DeterminedLanguage {
    Zokrates,
    Datalog,
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

fn determine_language(l: &Language, input_path: &PathBuf) -> DeterminedLanguage {
    match l {
        &Language::Datalog => DeterminedLanguage::Datalog,
        &Language::Zokrates => DeterminedLanguage::Zokrates,
        &Language::Auto =>  {
            let p = input_path.to_str().unwrap();
            if p.ends_with(".zok") {
                DeterminedLanguage::Zokrates
            } else if p.ends_with(".pl") {
                DeterminedLanguage::Datalog
            } else {
                println!("Could not deduce the input language from path '{}', please set the language manually", p);
                std::process::exit(2)
            }
        }
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();
    let path_buf = options.path.clone();
    println!("{:?}", options);
    let mode = match options.backend {
        Backend::R1cs { .. } => Mode::Proof,
        Backend::Ilp { .. } => Mode::Opt,
        Backend::Mpc { .. } => Mode::Mpc(options.parties),
        Backend::Smt { .. } => Mode::Proof,
    };
    let language = determine_language(&options.frontend.language, &options.path);
    let cs = match language {
        DeterminedLanguage::Zokrates => {
            let inputs = zokrates::Inputs {
                file: options.path,
                inputs: options.frontend.inputs,
                mode: mode.clone(),
            };
            Zokrates::gen(inputs)
        }
        DeterminedLanguage::Datalog => {
            let inputs = datalog::Inputs {
                file: options.path,
                rec_limit: options.frontend.rec_limit,
                lint_prim_rec: options.frontend.lint_prim_rec,
            };
            Datalog::gen(inputs)
        }
    };
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
                //Opt::FlattenAssertions,
                Opt::Inline,
                Opt::Mem,
                Opt::Flatten,
                //Opt::FlattenAssertions,
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
            if options.frontend.lint_prim_rec {
                assert_eq!(cs.outputs.len(), 1);
                match find_model(&cs.outputs[0]) {
                    Some(m) => {
                        println!("Not primitive recursive!");
                        for (var, val) in m {
                            println!("{} -> {}", var, val);
                        }
                        std::process::exit(1)
                    }
                    None => {
                        println!("Primitive recursive");
                    }
                }
            } else {
                    todo!()
            }
        }
    }
}
