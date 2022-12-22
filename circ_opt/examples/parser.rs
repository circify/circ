use circ_opt::CircOpt;
use clap::Parser;

#[derive(Parser, Debug)]
struct BinaryOpt {
    #[command(flatten)]
    pub circ: CircOpt,
}

fn main() {
    let opt = BinaryOpt::parse();
    println!("{:#?}", opt);
}
