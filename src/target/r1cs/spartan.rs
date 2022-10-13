//! Export circ R1cs to Spartan
use libspartan::*;
use crate::target::r1cs::*;
use curve25519_dalek::scalar::Scalar;
use rug::{Integer};
use core::clone::Clone;

use std::collections::HashMap;
use fxhash::FxHashMap;
use gmp_mpfr_sys::gmp::limb_t;

/// Hold Spartan variables
#[derive(Debug)]
pub struct Variable {
    sid: usize,
    value: [u8; 32],
}


/// circ R1cs -> spartan R1CSInstance
pub fn r1cs_to_spartan<S: Eq + Hash + Clone + Display>(r1cs: R1cs<S>,prover_data: ProverData, verifier_data: VerifierData, inputs_map: &FxHashMap<String, Value>) -> (Instance, Assignment, Assignment, usize, usize, usize)
{
// todo hashmap v fxhashmap

    println!("{:#?}", verifier_data);

// spartan format mapper: CirC -> Spartan
    let mut wit = Vec::new();
    let mut inp = Vec::new();
    let mut trans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids
    let mut itrans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids

    let values = eval_inputs(inputs_map, prover_data);

    for (idx,sig) in r1cs.idxs_signals {
        
        let scalar = match values.get(&sig.to_string()) {
            Some(v) => val_to_scalar(v),
            None => panic!("Input/witness variable does not have matching evaluation")
        };

        if r1cs.public_idxs.contains(&idx) {
            // input
            println!("As public io: {}", sig);

            itrans.insert(idx, inp.len());
            inp.push(scalar.to_bytes());
        } else {
             // witness
            println!("As private witness: {}", sig);

            trans.insert(idx, wit.len());
            wit.push(scalar.to_bytes());

        }

    }

    assert_eq!(wit.len() + inp.len(), r1cs.next_idx);

    let num_vars = wit.len();
    let const_id = wit.len();

    let assn_witness = VarsAssignment::new(&wit).unwrap();

    let num_inputs = inp.len();
    let assn_inputs = InputsAssignment::new(&inp).unwrap();

    
    for (cid,sid) in itrans{
        trans.insert(cid, sid + const_id + 1);
    }

    // circuit
    let mut m_a: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut m_b: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut m_c: Vec<(usize, usize, [u8; 32])> = Vec::new();

    let mut i = 0; // constraint #
    for (lc_a, lc_b, lc_c) in r1cs.constraints.iter() {

        // circ Lc (const, monomials <Integer>) -> Vec<Variable>
        let a = lc_to_v(&lc_a, const_id, &trans);
        let b = lc_to_v(&lc_b, const_id, &trans);
        let c = lc_to_v(&lc_c, const_id, &trans);

        // constraint # x identifier (vars, 1, inp)
        for Variable { sid, value } in a {
            m_a.push((i, sid, value));
        }
        for Variable { sid, value } in b {
            m_b.push((i, sid, value));
        }
        for Variable { sid, value } in c {
            m_c.push((i, sid, value));
        }

        i += 1;

    }


    let num_cons = i;
    let inst = Instance::new(num_cons, num_vars, num_inputs, &m_a, &m_b, &m_c).unwrap();

    // check if the instance we created is satisfiable
    let res = inst.is_sat(&assn_witness, &assn_inputs);
    assert_eq!(res.unwrap(), true);

    (inst, assn_witness, assn_inputs, num_cons, num_vars, num_inputs)
}

fn eval_inputs(inputs_map: &FxHashMap<String, Value>, prover_data: ProverData) -> FxHashMap<String, Value>{
    for (input, sort) in &prover_data.precompute_inputs {
        let value = inputs_map
            .get(input)
            .unwrap_or_else(|| panic!("No input for {}", input));
        let sort2 = value.sort();
        assert_eq!(
            sort, &sort2,
            "Sort mismatch for {}. Expected\n\t{} but got\n\t{}",
            input, sort, sort2
        );
    }
    let new_map = prover_data.precompute.eval(inputs_map);
    prover_data.r1cs.check_all(&new_map);

    return new_map;
}

fn val_to_scalar(v: &Value) -> Scalar {
    println!("val: {:#?}", v);
    match v.sort() {
        Sort::Field(_) => return int_to_scalar(&v.as_pf().i()),
        //Sort::Int => return int_to_scalar(&v.as_int()),
        _ => panic!("Underlying value should be a field")
    };

}

fn int_to_scalar(i: &Integer) -> Scalar {
    let mut accumulator = Scalar::zero();
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    assert_eq!(limb_bits, 64);

    let two: u64 = 2;
    let mut m = Scalar::from(two.pow(63) as u64);
    m = m * Scalar::from(2 as u64);

    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        accumulator *= m;
        accumulator += Scalar::from(*digit as u64);
    }
    return accumulator;

}


// circ Lc (const, monomials <Integer>) -> Vec<Variable>
fn lc_to_v(lc: &Lc, const_id: usize, trans: &HashMap<usize,usize>) -> Vec<Variable> {
    let mut v: Vec<Variable> = Vec::new();

    for (k,m) in &lc.monomials {
        let scalar = int_to_scalar(&m.i());
        
        let var = Variable {
            sid: trans.get(k).unwrap().clone(),
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    if lc.constant.i() != Integer::from(0 as u32) {
        let scalar = int_to_scalar(&lc.constant.i());
        let var = Variable {
            sid: const_id,
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    v
}

