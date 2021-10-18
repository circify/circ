#![allow(unused_imports)]
use bellman::gadgets::test::TestConstraintSystem;
use bellman::groth16::{
    create_random_proof, generate_parameters, generate_random_parameters, prepare_verifying_key,
    verify_proof, Parameters,
};
use bellman::Circuit;
use bls12_381::Scalar;
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
    let options = Options::from_args();
    let path_buf = options.zokrates_path.clone();
    println!("{:?}", options);
    let mode = if options.maximize {
        Mode::Opt
    } else {
        if let Some(v) = options.prove_high_value {
            Mode::ProofOfHighValue(v)
        } else {
            match options.parties {
                Some(p) => Mode::Mpc(p),
                None => Mode::Proof,
            }
        }
    };
    let inputs = Inputs {
        file: options.zokrates_path,
        inputs: options.inputs,
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
        Mode::Proof |
        Mode::ProofOfHighValue(_) => opt(
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

    match mode {
        Mode::Proof | Mode::ProofOfHighValue(_) => {
            println!("Converting to r1cs");
            let r1cs = to_r1cs(cs, circ::front::zokrates::ZOKRATES_MODULUS.clone());
            println!("Pre-opt R1cs size: {}", r1cs.constraints().len());
            let r1cs = reduce_linearities(r1cs);
            match options.proof_action {
                ProofOption::Count => {
                    println!("Final R1cs size: {}", r1cs.constraints().len());
                }
                ProofOption::Prove => {
                    println!("Proving");
                    let rng = &mut rand::thread_rng();
                    let p = generate_random_parameters::<bls12_381::Bls12, _, _>(&r1cs, rng).unwrap();
                    let pf = create_random_proof(&r1cs, &p, rng).unwrap();
                    println!("Verifying");
                    let pvk = prepare_verifying_key(&p.vk);
                    verify_proof(&pvk, &pf, &[]).unwrap();
                }
            }
        }
        Mode::Mpc(_) => {
            println!("Converting to aby");
            let aby = to_aby(cs);
            write_aby_exec(aby, path_buf);
        }
        Mode::Opt => {
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
    }

    //r1cs.check_all();
    //let mut cs = TestConstraintSystem::<Scalar>::new();
    //r1cs.synthesize(&mut cs).unwrap();
    //println!("Num constraints: {}", cs.num_constraints());
    //println!("{}", cs.pretty_print());
    //if let Some(c) = cs.which_is_unsatisfied() {
    //    panic!("Unsat: {}", c);
    //}
}
