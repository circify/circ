use circ::front::regex::{Regex, regex_parser};

use structopt::StructOpt;
use std::path::PathBuf;
use std::fmt::Display;

#[derive(Debug, StructOpt)]
#[structopt(name = "rezk", about = "Rezk: The regex to circuit compiler")]
struct Options {
    /// regular expression
    #[structopt(short = "r", long = "regex", parse(from_str = regex_parser))]
    regex: Regex<char>,

    #[structopt(short = "i", long = "input", parse(from_os_str))]
    input: PathBuf,
}

fn main() {
  let opt = Options::from_args();
  println!("Your regex {:?}", opt.regex);
}
