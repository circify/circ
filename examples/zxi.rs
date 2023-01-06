use circ::front::zsharp::{Inputs, ZSharpFE};

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
    let cs = ZSharpFE::interpret(inputs);
    cs.pretty(&mut std::io::stdout().lock())
        .expect("error pretty-printing value");
    println!();
}
