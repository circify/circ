use circ::cfg::clap::{self, Parser};
use circ::ir::term::*;
use circ::target::aby::assignment::ilp;
use circ::term;

#[derive(Debug, Parser)]
#[command(
    name = "opa_bench",
    about = "Optimal Protocol Assignment via ILP benchmarker"
)]
struct Options {
    /// Number of parties for an MPC. If missing, generates a proof circuit.
    #[arg(name = "MULTS")]
    n_mults: u32,
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    let v = leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32)));
    let mut t = v.clone();
    for _i in 0..options.n_mults {
        t = term![BV_MUL; t.clone(), t.clone()];
    }
    let cs = Computation {
        outputs: vec![term![Op::Eq; t, v]],
        ..Default::default()
    };
    let _assignment = ilp::assign(&cs, "hycc");
    //dbg!(&assignment);
}
