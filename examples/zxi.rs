use circ::front::zsharp::{Inputs, ZSharpFE};
use circ::front::Mode;
use std::path::PathBuf;
use structopt::StructOpt;
use std::io::Write;

#[derive(Debug, StructOpt)]
#[structopt(name = "circ", about = "CirC: the circuit compiler")]
struct Options {
    /// Input file
    #[structopt(parse(from_os_str))]
    zsharp_path: PathBuf,

    /// Number of parties for an MPC. If missing, generates a proof circuit.
    #[structopt(short, long, name = "PARTIES")]
    parties: Option<u8>,

    /// Whether to maximize the output
    #[structopt(short, long)]
    maximize: bool,

    /// Generate a value map from the input rather than interpreting
    #[structopt(short, long)]
    value_map: bool,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::from_args();
    //println!("{:?}", options);
    let mode = if options.maximize {
        Mode::Opt
    } else {
        match options.parties {
            Some(p) => Mode::Mpc(p),
            None => Mode::Proof,
        }
    };
    let inputs = Inputs {
        file: options.zsharp_path,
        mode,
        isolate_asserts: false,
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
