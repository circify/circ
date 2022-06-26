use circ::front::zsharp::{self, ZSharpFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::opt::{opt, Opt};
use circ_fields::FieldT;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use circ::util::field::DFL_T;
use std::fs::File;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "zxc", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[structopt(parse(from_os_str), name = "PATH")]
    path: PathBuf,

    #[structopt(short, long)]
    /// write JSON format if true, otherwise bincode
    json: bool,

    #[structopt(short, long, default_value = "out", parse(from_os_str))]
    /// output r1cs file
    outfile: PathBuf,

    #[structopt(short = "L", long)]
    /// skip linearity reduction entirely
    skip_linred: bool,

    #[structopt(short, long, default_value = "50")]
    /// linear combination constraints up to this size will be eliminated (if the pass is enabled)
    lc_elimination_thresh: usize,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();
    // open input file now so we don't waste a lot of time only to panic later
    let (mut p_out, mut v_out) = {
        let mut p_file = options.outfile.into_os_string();
        let mut v_file = p_file.clone();
        p_file.push(".pdat");
        v_file.push(".vdat");
        let p_out = File::options()
            .write(true)
            .create_new(true)
            .open(p_file)
            .expect("Could not open prover outfile for writing");
        let v_out = File::options()
            .write(true)
            .create_new(true)
            .open(v_file)
            .expect("Could not open verifier outfile for writing");
        (p_out, v_out)
    };

    let cs = {
        let inputs = zsharp::Inputs {
            file: options.path,
            mode: Mode::Proof,
            isolate_asserts: false,
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

    println!("Converting to r1cs");
    let (mut pd, vd) = to_r1cs(cs.get("main").clone(), FieldT::from(DFL_T.modulus()));
    pd.r1cs = if options.skip_linred {
        println!("Skipping linearity reduction, as requested.");
        pd.r1cs
    } else {
        println!(
            "R1cs size before linearity reduction: {}",
            pd.r1cs.constraints().len()
        );
        reduce_linearities(pd.r1cs, Some(options.lc_elimination_thresh))
    };
    println!("Final R1cs size: {}", pd.r1cs.constraints().len());

    print!("Writing outfile... ");
    if options.json {
        serde_json::to_writer(&mut p_out, &pd).unwrap();
        serde_json::to_writer(&mut v_out, &vd).unwrap();
    } else {
        bincode::serialize_into(&mut p_out, &pd).unwrap();
        bincode::serialize_into(&mut v_out, &vd).unwrap();
    }
    println!("done.");
}
