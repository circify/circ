use circ::ir::term::text::parse_value_map;
use circ::target::r1cs::ProverData;
use std::fs::File;
use std::path::PathBuf;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "zxe", about = "CirC: the circuit compiler")]
struct Options {
    /// Input pdat file
    #[structopt(parse(from_os_str), name = "PATH")]
    path: PathBuf,

    #[structopt(short, long, default_value = "in", parse(from_os_str))]
    /// input values
    inputs: PathBuf,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();

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

    for (k, v) in prover_data.precompute.eval(&input_map) {
        println!("{} : {:?}", k, v);
    }
}
