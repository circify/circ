use circ::front::regex::{regex_parser};

use structopt::StructOpt;
use std::path::PathBuf;

#[derive(Debug, StructOpt)]
#[structopt(name = "rezk", about = "Rezk: The regex to circuit compiler")]
struct Options {
    #[structopt(short = "ab", long = "alphabet", parse(from_str))]
    alphabet: String,

    /// regular expression
    #[structopt(short = "r", long = "regex", parse(from_str))]
    regex: String,

    #[structopt(short = "i", long = "input", parse(from_os_str))]
    input: PathBuf,
}

fn main() {
  let opt = Options::from_args();
  let ab = &opt.alphabet;
  let r = regex_parser(&opt.regex, ab);
  let _input = opt.input;
  println!("Your regex {:?}", r);
}
