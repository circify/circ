#![allow(unused_imports)]
#![allow(clippy::vec_init_then_push)]
#[cfg(feature = "bellman")]
use bellman::{
    gadgets::test::TestConstraintSystem,
    groth16::{
        create_random_proof, generate_parameters, generate_random_parameters,
        prepare_verifying_key, verify_proof, Parameters, Proof, VerifyingKey,
    },
    Circuit,
};
#[cfg(feature = "bellman")]
use bls12_381::{Bls12, Scalar};
use circ::cfg::{
    cfg,
    clap::{self, Args, Parser, Subcommand, ValueEnum},
    CircOpt,
};
#[cfg(feature = "c")]
use circ::front::c::{self, C};
#[cfg(all(feature = "smt", feature = "datalog"))]
use circ::front::datalog::{self, Datalog};
#[cfg(all(feature = "smt", feature = "zok"))]
use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::term::{Node, Op, BV_LSHR, BV_SHL};
use circ::ir::{
    opt::{opt, Opt},
    term::{
        check,
        text::{parse_value_map, serialize_value_map},
    },
};
#[cfg(feature = "aby")]
use circ::target::aby::trans::to_aby;
#[cfg(feature = "lp")]
use circ::target::ilp::{assignment_to_values, trans::to_ilp};
#[cfg(feature = "spartan")]
use circ::target::r1cs::spartan::write_data;
#[cfg(feature = "bellman")]
use circ::target::r1cs::{
    bellman::Bellman,
    mirage::Mirage,
    proof::{CommitProofSystem, ProofSystem},
};
#[cfg(feature = "r1cs")]
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs};
#[cfg(feature = "smt")]
use circ::target::smt::find_model;
use circ_fields::FieldT;
use fxhash::FxHashMap as HashMap;
#[cfg(feature = "lp")]
use good_lp::default_solver;
use log::trace;
use std::fs::File;
use std::io::Read;
use std::io::Write;
use std::path::{Path, PathBuf};

#[derive(Debug, Parser)]
#[command(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[arg(name = "PATH")]
    path: PathBuf,

    #[command(flatten)]
    frontend: FrontendOptions,

    #[command(flatten)]
    circ: CircOpt,

    /// Number of parties for an MPC.
    #[arg(long, default_value = "2", name = "PARTIES")]
    parties: u8,

    #[structopt(subcommand)]
    backend: Backend,
}

#[derive(Debug, Args)]
struct FrontendOptions {
    /// Input language
    #[arg(long, default_value = "auto", name = "LANG")]
    language: Language,

    /// Value threshold
    #[arg(long)]
    value_threshold: Option<u64>,
}

#[derive(Debug, Subcommand)]
enum Backend {
    #[allow(dead_code)]
    R1cs {
        #[arg(long, default_value = "P")]
        prover_key: PathBuf,
        #[arg(long, default_value = "V")]
        verifier_key: PathBuf,
        #[arg(long, default_value = "50")]
        /// linear combination constraints up to this size will be eliminated
        lc_elimination_thresh: usize,
        #[arg(long, default_value = "count")]
        action: ProofAction,
        #[arg(long, default_value = "groth16")]
        proof_impl: ProofImpl,
    },
    Smt {},
    Ilp {},
    Mpc {
        #[arg(long, default_value = "hycc", name = "cost_model")]
        cost_model: String,
        #[arg(long, default_value = "lp", name = "selection_scheme")]
        selection_scheme: String,
    },
}

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum Language {
    Zsharp,
    Datalog,
    C,
    Auto,
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

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum ProofAction {
    Count,
    Setup,
    CpSetup,
    SpartanSetup,
}

#[derive(PartialEq, Eq, Debug, Clone, ValueEnum)]
enum ProofImpl {
    Groth16,
    Mirage,
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
                println!("Could not deduce the input language from path '{p}', please set the language manually");
                std::process::exit(2)
            }
        }
    }
}

#[allow(unused_variables, unreachable_code)]
fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    let path_buf = options.path.clone();
    println!("{options:?}");
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
            };
            ZSharpFE::gen(inputs)
        }
        #[cfg(not(all(feature = "smt", feature = "zok")))]
        DeterminedLanguage::Zsharp => {
            panic!("Missing feature: smt,zok");
        }
        #[cfg(all(feature = "smt", feature = "datalog"))]
        DeterminedLanguage::Datalog => {
            let inputs = datalog::Inputs { file: options.path };
            Datalog::gen(inputs)
        }
        #[cfg(not(all(feature = "smt", feature = "datalog")))]
        DeterminedLanguage::Datalog => {
            panic!("Missing feature: smt,datalog");
        }
        #[cfg(feature = "c")]
        DeterminedLanguage::C => {
            let inputs = c::Inputs {
                file: options.path,
                mode,
                sv_functions: options.circ.c.sv_functions,
                assert_no_ub: options.circ.c.assert_no_ub,
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
                    // Function calls return tuples
                    Opt::Tuple,
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
        Mode::Proof | Mode::ProofOfHighValue(_) => {
            let mut opts = Vec::new();

            opts.push(Opt::ScalarizeVars);
            opts.push(Opt::Flatten);
            opts.push(Opt::Sha);
            opts.push(Opt::ConstantFold(Box::new([])));
            opts.push(Opt::ParseCondStores);
            // Tuples must be eliminated before oblivious array elim
            opts.push(Opt::ConstantFold(Box::new([])));
            opts.push(Opt::Obliv);
            // The obliv elim pass produces more tuples, that must be eliminated
            opts.push(Opt::PersistentRam);
            opts.push(Opt::VolatileRam);
            opts.push(Opt::SkolemizeChallenges);
            opts.push(Opt::ScalarizeVars);
            opts.push(Opt::ConstantFold(Box::new([])));
            opts.push(Opt::Obliv);
            opts.push(Opt::LinearScan);
            // The linear scan pass produces more tuples, that must be eliminated
            opts.push(Opt::Tuple);
            opts.push(Opt::Flatten);
            opts.push(Opt::ConstantFold(Box::new([])));
            opt(cs, opts)
        }
    };
    println!("Done with IR optimization");

    match options.backend {
        #[cfg(feature = "r1cs")]
        Backend::R1cs {
            action,
            prover_key,
            verifier_key,
            proof_impl,
            ..
        } => {
            println!("Converting to r1cs");
            let cs = cs.get("main");
            trace!("IR: {}", circ::ir::term::text::serialize_computation(cs));
            let mut r1cs = to_r1cs(cs, cfg());

            println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
            r1cs = reduce_linearities(r1cs, cfg());

            println!("Final R1cs size: {}", r1cs.constraints().len());
            let (prover_data, verifier_data) = r1cs.finalize(cs);
            match action {
                ProofAction::Count => (),
                #[cfg(feature = "bellman")]
                ProofAction::Setup => {
                    println!("Generating Parameters");
                    match proof_impl {
                        ProofImpl::Groth16 => Bellman::<Bls12>::setup_fs(
                            prover_data,
                            verifier_data,
                            prover_key,
                            verifier_key,
                        )
                        .unwrap(),
                        ProofImpl::Mirage => Mirage::<Bls12>::setup_fs(
                            prover_data,
                            verifier_data,
                            prover_key,
                            verifier_key,
                        )
                        .unwrap(),
                    };
                }
                #[cfg(not(feature = "bellman"))]
                ProofAction::Setup => panic!("Missing feature: bellman"),
                #[cfg(feature = "bellman")]
                ProofAction::CpSetup => {
                    println!("Generating Parameters");
                    match proof_impl {
                        ProofImpl::Groth16 => panic!("Groth16 is not CP"),
                        ProofImpl::Mirage => Mirage::<Bls12>::cp_setup_fs(
                            prover_data,
                            verifier_data,
                            prover_key,
                            verifier_key,
                        )
                        .unwrap(),
                    };
                }
                #[cfg(not(feature = "bellman"))]
                ProofAction::CpSetup => panic!("Missing feature: bellman"),
                #[cfg(feature = "spartan")]
                ProofAction::SpartanSetup => {
                    write_data::<_, _>(prover_key, verifier_key, &prover_data, &verifier_data)
                        .unwrap();
                }
                #[cfg(not(feature = "spartan"))]
                ProofAction::SpartanSetup => panic!("Missing feature: spartan"),
            }
        }
        #[cfg(not(feature = "r1cs"))]
        Backend::R1cs { .. } => {
            panic!("Missing feature: r1cs");
        }
        #[cfg(feature = "aby")]
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
            println!("Cost model: {cost_model}");
            println!("Selection scheme: {selection_scheme}");
            to_aby(cs, &path_buf, &lang_str, &cost_model, &selection_scheme);
        }
        #[cfg(not(feature = "aby"))]
        Backend::Mpc { .. } => {
            panic!("Missing feature: aby");
        }
        #[cfg(feature = "lp")]
        Backend::Ilp { .. } => {
            println!("Converting to ilp");
            let inputs_and_sorts: HashMap<_, _> = cs
                .get("main")
                .clone()
                .metadata
                .ordered_inputs()
                .iter()
                .map(|term| match term.op() {
                    Op::Var(n, s) => (n.clone(), s.clone()),
                    _ => unreachable!(),
                })
                .collect();
            let ilp = to_ilp(cs.get("main").clone());
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
            let main_comp = cs.get("main").clone();
            assert_eq!(main_comp.outputs.len(), 1);
            let model = find_model(&main_comp.outputs[0]);
            if options.circ.datalog.lint_prim_rec {
                match model {
                    Some(m) => {
                        println!("Not primitive recursive!");
                        for (var, val) in m {
                            println!("{var} -> {val}");
                        }
                        std::process::exit(1)
                    }
                    None => {
                        println!("Primitive recursive");
                    }
                }
            } else {
                match model {
                    Some(m) => {
                        println!("Property does not hold!\nCounterexample:");
                        for (var, val) in m {
                            println!("{var} -> {val}");
                        }
                        std::process::exit(1)
                    }
                    None => {
                        println!("Property holds");
                    }
                }
            }
        }
        #[cfg(not(feature = "smt"))]
        Backend::Smt { .. } => {
            panic!("Missing feature: smt");
        }
    }
}
