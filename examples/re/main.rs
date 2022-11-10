use circ::front::regex::poly::mk_poly;
use circ::front::regex::parser::regex_parser;

use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "rezk", about = "Rezk: The regex to circuit compiler")]
struct Options {
    #[structopt(short = "ab", long = "alphabet", parse(from_str))]
    alphabet: String,

    /// regular expression
    #[structopt(short = "r", long = "regex", parse(from_str))]
    regex: String,

    #[structopt(short = "i", long = "input", parse(from_str))]
    input: String,
}

fn main() {
  let opt = Options::from_args();
  let ab = opt.alphabet;
  let r = regex_parser(&opt.regex, &ab);
  let pdfa = mk_poly(&r, &ab);

  let doc = opt.input;
  println!("Your regex {:?} matches input {}: {}", r, doc, pdfa.is_match(&doc));
}
