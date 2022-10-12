#![allow(unused_imports)]
#[cfg(feature = "r1cs")]
use bellman::gadgets::test::TestConstraintSystem;
#[cfg(feature = "r1cs")]
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters, Proof, VerifyingKey,
};
#[cfg(feature = "r1cs")]
use bellman::Circuit;
use bls12_381::{Bls12, Scalar};
#[cfg(feature = "c")]
use circ::front::c::{self, C};
use circ::front::datalog::{self, Datalog};
#[cfg(all(feature = "smt", feature = "zok"))]
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::term::{Op, BV_LSHR, BV_SHL};
use circ::ir::{
    opt::{opt, Opt},
    term::{
        check,
        extras::Letified,
        text::{parse_value_map, serialize_value_map},
    },
};
use circ::target::aby::trans::to_aby;
#[cfg(feature = "lp")]
use circ::target::ilp::{assignment_to_values, trans::to_ilp};
#[cfg(feature = "r1cs")]
use circ::target::r1cs::bellman::{gen_params, prove, verify};
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
#[cfg(feature = "smt")]
use circ::target::smt::find_model;
use circ::util::field::DFL_T;
use circ_fields::FieldT;
use fxhash::FxHashMap as HashMap;
#[cfg(feature = "lp")]
use good_lp::default_solver;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::{Path, PathBuf};
use structopt::clap::arg_enum;
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

    /// How many recursions to allow (datalog)
    #[structopt(short, long, name = "N", default_value = "5")]
    rec_limit: usize,

    /// Lint recursions that are allegedly primitive recursive (datalog)
    #[structopt(long)]
    lint_prim_rec: bool,

    #[cfg(feature = "zok")]
    /// In Z#, "isolate" assertions. That is, assertions in if/then/else expressions only take
    /// effect if that branch is active.
    ///
    /// See `--branch-isolation` in
    /// [ZoKrates](https://zokrates.github.io/language/control_flow.html).
    #[structopt(long)]
    z_isolate_asserts: bool,
}

#[derive(Debug, StructOpt)]
enum Backend {
    #[allow(dead_code)]
    R1cs {
        #[structopt(long, default_value = "P", parse(from_os_str))]
        prover_key: PathBuf,
        #[structopt(long, default_value = "V", parse(from_os_str))]
        verifier_key: PathBuf,
        #[structopt(long, default_value = "50")]
        /// linear combination constraints up to this size will be eliminated
        lc_elimination_thresh: usize,
        #[structopt(long, default_value = "count")]
        action: ProofAction,
    },
    Smt {},
    Ilp {},
    Mpc {
        #[structopt(long, default_value = "hycc", name = "cost_model")]
        cost_model: String,
        #[structopt(long, default_value = "lp", name = "selection_scheme")]
        selection_scheme: String,
    },
}

arg_enum! {
    #[derive(PartialEq, Eq, Debug)]
    enum Language {
        Zsharp,
        Datalog,
        C,
        Auto,
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum DeterminedLanguage {
    Zsharp,
    Datalog,
    C,
}

#[derive(PartialEq, Eq, Debug)]
pub enum CostModelType {
    Opa,
    Hycc,
}

arg_enum! {
    #[derive(PartialEq, Eq, Debug)]
    enum ProofAction {
        Count,
        Setup,
    }
}

fn determine_language(l: &Language, input_path: &Path) -> DeterminedLanguage {
    match *l {
        Language::Datalog => DeterminedLanguage::Datalog,
        Language::Zsharp => DeterminedLanguage::Zsharp,
        Language::C => DeterminedLanguage::C,
        Language::Auto => {
            let p = input_path.to_str().unwrap();
            if p.ends_with(".zok") {
                DeterminedLanguage::Zsharp
            } else if p.ends_with(".pl") {
                DeterminedLanguage::Datalog
            } else if p.ends_with(".c") || p.ends_with(".cpp") || p.ends_with(".cc") {
                DeterminedLanguage::C
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
        Backend::R1cs { .. } => match options.frontend.value_threshold {
            Some(t) => Mode::ProofOfHighValue(t),
            None => Mode::Proof,
        },
        Backend::Ilp { .. } => Mode::Opt,
        Backend::Mpc { .. } => Mode::Mpc(options.parties),
        Backend::Smt { .. } => Mode::Proof,
    };
    let language = determine_language(&options.frontend.language, &options.path);
    let cs = match language {
        #[cfg(all(feature = "smt", feature = "zok"))]
        DeterminedLanguage::Zsharp => {
            let inputs = zsharp::Inputs {
                file: options.path,
                mode,
                isolate_asserts: options.frontend.z_isolate_asserts,
            };
            ZSharpFE::gen(inputs)
        }
        #[cfg(not(all(feature = "smt", feature = "zok")))]
        DeterminedLanguage::Zsharp => {
            panic!("Missing feature: smt,zok");
        }
        DeterminedLanguage::Datalog => {
            let inputs = datalog::Inputs {
                file: options.path,
                rec_limit: options.frontend.rec_limit,
                lint_prim_rec: options.frontend.lint_prim_rec,
            };
            Datalog::gen(inputs)
        }
        #[cfg(feature = "c")]
        DeterminedLanguage::C => {
            let inputs = c::Inputs {
                file: options.path,
                mode,
            };
            C::gen(inputs)
        }
        #[cfg(not(feature = "c"))]
        DeterminedLanguage::C => {
            panic!("Missing feature: c");
        }
    };
    let cs = match mode {
        Mode::Opt => opt(
            cs,
            vec![Opt::ScalarizeVars, Opt::ConstantFold(Box::new([]))],
        ),
        Mode::Mpc(_) => {
            let ignore = [BV_LSHR, BV_SHL];
            opt(
                cs,
                vec![
                    Opt::ScalarizeVars,
                    Opt::Flatten,
                    Opt::Sha,
                    Opt::ConstantFold(Box::new(ignore.clone())),
                    Opt::Flatten,
                    Opt::Obliv,
                    // The obliv elim pass produces more tuples, that must be eliminated
                    Opt::Tuple,
                    Opt::LinearScan,
                    // The linear scan pass produces more tuples, that must be eliminated
                    Opt::Tuple,
                    Opt::ConstantFold(Box::new(ignore)),
                    // Binarize nary terms
                    Opt::Binarize,
                ],
                // vec![Opt::Sha, Opt::ConstantFold, Opt::Mem, Opt::ConstantFold],
            )
        }
        Mode::Proof | Mode::ProofOfHighValue(_) => opt(
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
        ),
    };
    println!("Done with IR optimization");

    match options.backend {
        #[cfg(feature = "r1cs")]
        Backend::R1cs {
            action,
            prover_key,
            verifier_key,
            lc_elimination_thresh,
            ..
        } => {
            println!("Converting to r1cs");
            let (r1cs, mut prover_data, verifier_data) = to_r1cs(cs, FieldT::from(DFL_T.modulus()));
            println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
            let r1cs = reduce_linearities(r1cs, Some(lc_elimination_thresh));
            println!("Final R1cs size: {}", r1cs.constraints().len());
            // save the optimized r1cs: the prover needs it to synthesize.
            prover_data.r1cs = r1cs;
            match action {
                ProofAction::Count => (),
                ProofAction::Setup => {
                    println!("Generating Parameters");
                    gen_params::<Bls12, _, _>(
                        prover_key,
                        verifier_key,
                        &prover_data,
                        &verifier_data,
                    )
                    .unwrap();
                }
            }
        }
        #[cfg(not(feature = "r1cs"))]
        Backend::R1cs { .. } => {
            panic!("Missing feature: r1cs");
        }
        Backend::Mpc {
            cost_model,
            selection_scheme,
        } => {
            println!("Converting to aby");
            let lang_str = match language {
                DeterminedLanguage::C => "c".to_string(),
                DeterminedLanguage::Zsharp => "zok".to_string(),
                _ => panic!("Language isn't supported by MPC backend: {:#?}", language),
            };
            println!("Cost model: {}", cost_model);
            println!("Selection scheme: {}", selection_scheme);
            to_aby(cs, &path_buf, &lang_str, &cost_model, &selection_scheme);
        }
        #[cfg(feature = "lp")]
        Backend::Ilp { .. } => {
            println!("Converting to ilp");
            let inputs_and_sorts: HashMap<_, _> = cs
                .metadata
                .input_vis
                .iter()
                .map(|(name, (sort, _))| (name.clone(), check(sort)))
                .collect();
            let ilp = to_ilp(cs);
            let solver_result = ilp.solve(default_solver);
            let (max, vars) = solver_result.expect("ILP could not be solved");
            println!("Max value: {}", max.round() as u64);
            println!("Assignment:");
            for (var, val) in &vars {
                println!("  {}: {}", var, val.round() as u64);
            }
            let values = assignment_to_values(&vars, &inputs_and_sorts);
            let values_as_str = serialize_value_map(&values);
            std::fs::write("assignment.txt", values_as_str).unwrap();
        }
        #[cfg(not(feature = "lp"))]
        Backend::Ilp { .. } => {
            panic!("Missing feature: lp");
        }
        #[cfg(feature = "smt")]
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
        #[cfg(not(feature = "smt"))]
        Backend::Smt { .. } => {
            panic!("Missing feature: smt");
        }
    }
}
