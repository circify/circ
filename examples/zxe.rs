use circ::ir::term::text::{parse_value_map, serialize_value_map};
use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use circ::target::r1cs::ProverData;
use std::fs::File;
use std::io::Write;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[structopt(name = "zxe", about = "CirC: the circuit compiler")]
struct Options {
    /// Input pdat file
    #[arg(name = "PATH")]
    path: PathBuf,

    #[arg(short, long, default_value = "in")]
    /// input values
    inputs: PathBuf,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();

    print!("Opening pdat and inputs... ");
    let input_map = {
        let mdat_in = std::fs::read(&options.inputs).expect("Error opening input map file");
        parse_value_map(&mdat_in)
    };
    let prover_data: ProverData =
        bincode::deserialize_from(File::open(&options.path).expect("Error opening pdat"))
            .or_else(|_| serde_json::from_reader(File::open(&options.path).unwrap()))
            .expect("Could not deserialize prover data as either json or bincode");
    println!("done.");

    let eval_map = prover_data.precompute.eval(&input_map);
    std::io::stdout()
        .lock()
        .write_all(serialize_value_map(&eval_map, Some(prover_data.r1cs.field_t())).as_bytes())
        .unwrap();
}
