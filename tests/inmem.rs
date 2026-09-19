use bls12_381::Bls12;
use circ::front::zsharpcurly::{self, ZSharpCurlyFE};
use circ::front::{FrontEnd, Mode};
use circ::ir::term::text;
use circ::target::r1cs::mirage::Mirage;
use circ::target::r1cs::proof::ProofSystem;
use std::path::PathBuf;

#[test]
fn mul_setup_prove_verify_in_memory() {
    circ::cfg::set_default();

    // 1. Compile the .zok file into an in-memory circuit.
    let inputs = zsharpcurly::Inputs {
        file: PathBuf::from("examples/ZoKratesCurly/pf/mul.zok"),
        entry: "main".to_string(),
        mode: Mode::Proof,
    };
    let comps = ZSharpCurlyFE::gen(inputs);
    let cs = comps.get("main");

    // 2. Lower it to R1CS and produce the prover/verifier data
    //    (the third value is R1CS stats, which the test doesn't need).
    let (p_data, v_data, _stats) = circ::compile::to_proof_data(cs, circ::cfg::cfg());

    // 3. Hardcode the inputs in memory (no .pin / .vin files!).
    //    Prover knows x and y; verifier only knows the public output `return`.
    let p_input = text::parse_value_map(
        b"(set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
          (let ((x #f4) (y #f5)) true))",
    );
    let v_input = text::parse_value_map(
        b"(set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
          (let ((return #f20)) true))",
    );

    // 4. Run the full proof pipeline in memory.
    let (pk, vk) = Mirage::<Bls12>::setup(p_data, v_data);
    let pf = Mirage::<Bls12>::prove(&pk, &p_input);
    assert!(Mirage::<Bls12>::verify(&vk, &v_input, &pf));

    // Sanity check: a wrong public output must NOT verify.
    let wrong_v_input = text::parse_value_map(
        b"(set_default_modulus 52435875175126190479447740508185965837690552500527637822603658699938581184513
          (let ((return #f21)) true))",
    );
    assert!(!Mirage::<Bls12>::verify(&vk, &wrong_v_input, &pf));

    println!("in-memory setup/prove/verify succeeded for mul.zok");
}
