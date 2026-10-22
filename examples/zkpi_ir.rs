//! Compiles a zkPi dump from zkPi's CirC fork with this CirC's back end.
//!
//! ```text
//! zkpi_ir DUMP [--check [--perturb NAME]]   # reads DUMP.ir, DUMP.ir.inputs, and DUMP.pin
//! ```
//!
//! zkPi's fork dumps its computation right before RAM extraction (see `artifact/zkpi` in
//! paper-ip-semantics). The dump's metadata is `(metadata (PARTIES) ((NAME SORT) ..) ((NAME PARTY
//! ROUND) ..))`, and `DUMP.ir.inputs` lists each input as tab-separated name, sort, party (`prover`
//! or `public`), round, and whether it is random. We take the inputs from `DUMP.ir.inputs`, make
//! each random input a challenge term over the round-0 prover inputs (as `sample_challenge` would),
//! mark every array for RAM extraction, and run the passes that follow `Obliv` in
//! `examples/circ.rs`.

#![allow(clippy::mutable_key_type)]

use circ::cfg::{
    cfg,
    clap::{self, Parser},
    CircOpt,
};
use circ::ir::opt::{opt, Opt};
use circ::ir::term::extras::substitute_cache;
use circ::ir::term::precomp::PreComp;
use circ::ir::term::text::{parse_computation, parse_value_map};
use circ::ir::term::{
    term, ComputationMetadata, Computations, Node, Op, Sort, Term, TermMap, TermSet, Value,
};
use circ::target::r1cs::{opt::reduce_linearities, trans::to_r1cs};
use std::time::Instant;

#[derive(Debug, Parser)]
#[command(name = "zkpi_ir", about = "Compile a zkPi dump from zkPi's CirC fork")]
struct Options {
    /// The dump's path, without `.ir`
    #[arg(name = "DUMP")]
    dump: String,
    /// Check that the witness from DUMP.pin satisfies the R1CS
    #[arg(long)]
    check: bool,
    /// Add one to this input before checking
    #[arg(long)]
    perturb: Option<String>,
    #[command(flatten)]
    circ: CircOpt,
}

/// An input, as `DUMP.ir.inputs` lists it.
struct Input {
    name: String,
    sort: String,
    prover: bool,
    round: u8,
    random: bool,
}

fn inputs(src: &str) -> Vec<Input> {
    src.lines()
        .map(|l| {
            let [name, sort, party, round, random] = l.split('\t').collect::<Vec<_>>()[..] else {
                panic!("bad input line {}", l)
            };
            Input {
                name: name.into(),
                sort: sort.into(),
                prover: party == "prover",
                round: round.parse().unwrap(),
                random: random == "true",
            }
        })
        .collect()
}

/// The end of the list that starts at `start`.
fn list_end(s: &[u8], start: usize) -> usize {
    let mut depth = 0;
    for (i, c) in s[start..].iter().enumerate() {
        match c {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return start + i + 1;
                }
            }
            _ => {}
        }
    }
    panic!("unbalanced list at {}", start)
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let options = Options::parse();
    circ::cfg::set(&options.circ);
    let t = Instant::now();
    let inputs = inputs(&std::fs::read_to_string(format!("{}.ir.inputs", options.dump)).unwrap());
    let src = std::fs::read(format!("{}.ir", options.dump)).unwrap();
    let start = src.windows(9).position(|w| w == b"(metadata").unwrap();
    let end = list_end(&src, start);
    let mut md = String::from("(metadata (parties prover verifier) (inputs");
    for i in &inputs {
        let party = if i.prover { " (party 0)" } else { "" };
        md += &format!(" ({} {}{party})", i.name, i.sort);
    }
    md += ") (commitments))";
    let mut c = parse_computation(&[&src[..start], md.as_bytes(), &src[end..]].concat());
    println!("Parsed in {:?}", t.elapsed());

    // Each random input becomes a challenge, after the round-0 prover inputs.
    let committed: Vec<Term> = inputs
        .iter()
        .filter(|i| i.prover && i.round == 0)
        .map(|i| c.metadata.lookup(&*i.name).term())
        .collect();
    let mut subs = TermMap::default();
    for i in inputs.iter().filter(|i| i.random) {
        assert_eq!(
            i.round, 0,
            "we expect challenges only in round 0, not {}",
            i.name
        );
        let Sort::Field(f) = c.metadata.input_sort(&i.name) else {
            panic!("random input {} is not a field element", i.name)
        };
        let chall = term(Op::new_chall(i.name.clone(), f), committed.clone());
        subs.insert(c.metadata.lookup(&*i.name).term(), chall);
    }
    c.outputs = c
        .outputs
        .iter()
        .map(|o| substitute_cache(o, &mut subs))
        .collect();
    // The instance gives the public inputs, though the fork's precompute also computes `return`.
    let mut precomputes = PreComp::new();
    for (name, sort) in c.precomputes.inputs() {
        precomputes.add_input(name.clone(), sort.clone());
    }
    for (name, _) in c.precomputes.sequence() {
        if inputs.iter().any(|i| &i.name == name && !i.prover) {
            continue;
        }
        let value = substitute_cache(&c.precomputes.outputs()[name], &mut subs);
        precomputes.add_output(name.clone(), value);
    }
    c.precomputes = precomputes;
    let mut metadata = ComputationMetadata::default();
    metadata.add_party("prover".into());
    metadata.add_party("verifier".into());
    for i in inputs.iter().filter(|i| !i.random) {
        metadata.new_input_from_meta(c.metadata.lookup(&*i.name).clone());
    }
    c.metadata = metadata;
    // RAM extraction takes the arrays a program marks `transcript`; the fork's took them all.
    let arrays: TermSet = c
        .terms_postorder()
        .filter(|t| matches!(t.op(), Op::Array(..)))
        .collect();
    c.ram_arrays = arrays;

    let t = Instant::now();
    let mut cs = Computations::new();
    cs.comps.insert("main".into(), c);
    let cs = opt(
        cs,
        vec![
            Opt::SetMembership,
            Opt::PersistentRam,
            Opt::VolatileRam,
            Opt::SkolemizeChallenges,
            Opt::ScalarizeVars,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            Opt::LinearScan,
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
        ],
    );
    println!("Optimized in {:?}", t.elapsed());
    let t = Instant::now();
    let c = cs.get("main");
    let r1cs = reduce_linearities(to_r1cs(c, cfg()), cfg());
    let stats = r1cs.stats();
    let (constraints, vars, entries) = (stats.n_constraints, stats.n_vars, stats.n_entries());
    let (prover_data, _) = r1cs.finalize(c);
    println!("Lowered in {:?}", t.elapsed());
    let rounds = prover_data.precompute.stage_sizes().count() - 1;
    println!(
        "Final r1cs: {constraints} constraints, {vars} variables, {entries} entries, {rounds} rounds"
    );

    if options.check {
        let t = Instant::now();
        let pin = std::fs::read(format!("{}.pin", options.dump)).unwrap();
        let mut values = parse_value_map(&pin);
        if let Some(x) = &options.perturb {
            let Value::Field(v) = &values[x] else {
                panic!("{} is not a field element", x)
            };
            let bumped = v.clone() + &v.ty().new_v(1);
            values.insert(x.clone(), Value::Field(bumped));
        }
        prover_data.check_all(&values);
        println!("Satisfied, checked in {:?}", t.elapsed());
    }
}
