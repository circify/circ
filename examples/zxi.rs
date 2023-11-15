use circ::front::zsharp::{Inputs, ZSharpFE};
use circ::ir::term::text::parse_value_map;

use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use circ::front::Mode;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(name = "zxi", about = "The Z# interpreter")]
struct Options {
    /// Input file
    #[arg()]
    zsharp_path: PathBuf,

    /// Scalar input values
    #[arg()]
    inputs_path: Option<PathBuf>,

    #[command(flatten)]
    /// CirC options
    circ: CircOpt,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let mut options = Options::parse();
    options.circ.ir.field_to_bv = circ_opt::FieldToBv::Panic;
    circ::cfg::set(&options.circ);
    let inputs = Inputs {
        file: options.zsharp_path,
        mode: Mode::Proof,
    };
    let scalar_input_values = match options.inputs_path.as_ref() {
        Some(p) => parse_value_map(&std::fs::read(p).unwrap()),
        None => Default::default(),
    };
    let cs = ZSharpFE::interpret(inputs, scalar_input_values);
    cs.pretty(&mut std::io::stdout().lock())
        .expect("error pretty-printing value");
    println!();
}
