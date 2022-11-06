use std::path::PathBuf;
use bls12_381::Bls12;
use circ::front::{FrontEnd, Mode};
use circ::front::zsharp::{ZSharpFE, Inputs};
use circ::ir::term::precomp::PreComp;
use circ::target::r1cs::bellman::test_prove;
use circ::target::r1cs::opt::reduce_linearities;
use circ::target::r1cs::trans::to_r1cs;
use circ::util::field::DFL_T;
use circ::ir::opt::{opt, Opt, precomp_opt};
use std::time::{Instant};
use circ::ir::term::{Value, BitVector, Computation, Computations};
use fxhash::FxHashMap as HashMap;
use rug::Integer;
use circ_fields::FieldT;

fn main() {
    env_logger::init();
    test_sha_round();
}

fn test_sha_round() {
    let inputs = Inputs {
        file: PathBuf::from("./third_party/ZoKrates/zokrates_stdlib/stdlib/hashes/sha256/shaRound.zok"),
        mode: Mode::Proof,
        isolate_asserts: true,
    };
    let cs = ZSharpFE::gen(inputs);
    println!("gen finish");
    let timer = Instant::now();
    let cs = default_opt(cs);
    println!("opt finish {}", timer.elapsed().as_millis());
    let mut input_map = HashMap::<String, Value>::default();
    map_u32_arr(&[1; 16], "input", &mut input_map);
    map_u32_arr(&[0; 8], "current", &mut input_map);
    evaluate_cs(cs.comps["main"].clone(), &input_map);
}

fn evaluate_cs(cs: Computation, input_map: &HashMap::<String, Value>) {
    println!("will generate r1cs");
    let (r1cs, prover_data, _) = to_r1cs(cs, FieldT::from(DFL_T.modulus()));
    let r1cs = reduce_linearities(r1cs, Some(50));
    let timer = Instant::now();
    let _ = prover_data.precompute.eval(input_map);
    println!("original eval: {}", timer.elapsed().as_millis());
    println!("r1cs timer {}", timer.elapsed().as_millis());
    println!("r1cs constraints {}", r1cs.constraints().len());
    let precomp = precomp_opt(
        prover_data.precompute,
        vec![
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
        ]
    ); 
    println!("after precomp opt");
    let (term_arr, name_idxes) = precomp.eval_preprocess(&r1cs);
    let map = PreComp::real_eval(&name_idxes, &term_arr, input_map);
    test_prove::<Bls12>(&r1cs, &map);
}

fn map_u32_arr(u32_arr: &[u32], name: &str, input_map: &mut HashMap::<String, Value>) {
    for (i, b) in u32_arr.iter().enumerate() {
        input_map.insert(format!("{}.{}", name, i), u32_to_value(*b as u32));
    }
}

fn u32_to_value(num: u32) -> Value {
    Value::BitVector(BitVector::new(Integer::from(num), 32))
}

fn default_opt(cs: Computations) -> Computations {
    opt(
        cs,
        vec![
            Opt::ScalarizeVars,
            Opt::Flatten,
            // Opt::Sha,
            Opt::ConstantFold(Box::new([])),
            Opt::Flatten,
            Opt::Inline,
            // Tuples must be eliminated before oblivious array elim
            Opt::Tuple,
            Opt::ConstantFold(Box::new([])),
            Opt::Obliv,
            // The obliv elim pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::LinearScan,
            // The linear scan pass produces more tuples, that must be eliminated
            Opt::Tuple,
            Opt::Flatten,
            Opt::ConstantFold(Box::new([])),
            Opt::Inline,
        ],
    )
}