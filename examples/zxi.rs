use circ::front::zsharp::{Inputs, ZSharpFE};
use circ::cfg::{
    clap::{self, Parser},
    CircOpt,
};
use circ::front::Mode;
use std::io::Write;
use std::path::PathBuf;

#[derive(Debug, Parser)]
#[command(name = "zxi", about = "The Z# interpreter")]
struct Options {
    /// Input file
    #[arg()]
    zsharp_path: PathBuf,

    /// Generate a value map from the inputs, rather than interpreting
    #[arg(short, long)]
    value_map: bool,

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
    if options.value_map {
        let vm = ZSharpFE::value_map(inputs);
        std::io::stdout().lock().write_all(vm.as_bytes()).unwrap();
    } else {
        let cs = ZSharpFE::interpret(inputs);
        cs.pretty(&mut std::io::stdout().lock())
            .expect("error pretty-printing value");
        println!();
    }
}
