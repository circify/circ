use clap::Parser;
use circ_opt::CircOpt;

#[derive(Parser, Debug)]
struct BinaryOpt {
    #[command(flatten)]
    pub circ: CircOpt,
}

fn main() {
    let opt = BinaryOpt::parse();
    println!("{:#?}", opt);
}
