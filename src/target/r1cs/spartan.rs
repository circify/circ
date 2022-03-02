//! Export circ R1cs to Spartan
use libspartan::*;
use crate::target::r1cs::*;
use curve25519_dalek::scalar::Scalar;
use rug::{Assign, Integer};
use core::clone::Clone;
use core::ops::Shr;

use log::debug;
use std::collections::HashMap;
use gmp_mpfr_sys::gmp::limb_t;
use lazy_static::lazy_static;

lazy_static! {
    pub static ref SPARTAN_MODULUS: Integer = Integer::from_str_radix(
        "7237005577332262213973186563042994240857116359379907606001950938285454250989",
         10
    ).unwrap();

}


#[derive(Debug)]
pub struct Variable {
    sid: usize,
    value: [u8; 32],
}


// circ R1cs -> spartan R1CSInstance
pub fn r1cs_to_spartan<S: Eq + Hash + Clone + Display>(r1cs: R1cs<S>) -> (Instance, Assignment, Assignment, usize, usize, usize)
{

    // spartan format mapper: CirC -> Spartan
    let mut wit = Vec::new();
    let mut inp = Vec::new();
    let mut trans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids
    let mut itrans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids

    // assume no public inputs for now
    assert!(r1cs.public_idxs.len() == 0);

    // TODO if not input?
    match r1cs.values {
        Some(_) =>
            for (k,v) in r1cs.values.as_ref().unwrap() { // CirC id, Integer

                let mut name = r1cs.idxs_signals.get(k).unwrap().to_string();
                let scalar = int_to_scalar(&v);


                if name.contains("main_f0_lex0_w"){
                    // witness
                    //println!("As witness: {}", name);

                    trans.insert(*k, wit.len());
                    wit.push(scalar.to_bytes());

                } else if name.contains("main_f0_lex0_"){
                    // input
                    //println!("As input: {}", name);

                    itrans.insert(*k, inp.len());
                    inp.push(scalar.to_bytes());

                } else {
                    // witness
                    //println!("As witness: {}", name);

                    trans.insert(*k, wit.len());
                    wit.push(scalar.to_bytes());

                }

            }
        None    => panic!("Tried to run Spartan without inputs/witness"),
    }

    assert_eq!(wit.len() + inp.len(), r1cs.next_idx);

    let num_vars = wit.len();
    let const_id = wit.len();

    let assn_witness = VarsAssignment::new(&wit).unwrap();

    let num_inputs = inp.len();
    let assn_inputs = InputsAssignment::new(&inp).unwrap();

    //drop inp and wit vecs
    inp = Vec::new();
    wit = Vec::new();

    for (cid,sid) in itrans{
//        println!("input translation cid, sid = {}, {}", cid, sid);
        trans.insert(cid, sid + const_id + 1);
    }

//    println!("Translation Mapping: {:#?}", trans);
//    println!("const id {}", const_id);

    // circuit
    let mut A: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut B: Vec<(usize, usize, [u8; 32])> = Vec::new();
    let mut C: Vec<(usize, usize, [u8; 32])> = Vec::new();

    let mut i = 0; // constraint #
    for (lc_a, lc_b, lc_c) in r1cs.constraints.iter() {

        // circ Lc (const, monomials <Integer>) -> Vec<Integer> -> Vec<Variable>
        let a = lc_to_v(&lc_a, const_id, &trans);
        let b = lc_to_v(&lc_b, const_id, &trans);
        let c = lc_to_v(&lc_c, const_id, &trans);

        // constraint # x identifier (vars, 1, inp)
        for Variable { sid, value } in a {
            A.push((i, sid, value));
        }
        for Variable { sid, value } in b {
            B.push((i, sid, value));
        }
        for Variable { sid, value } in c {
            C.push((i, sid, value));
        }

        i += 1;

    }


    let num_cons = i;
    let inst = Instance::new(num_cons, num_vars, num_inputs, &A, &B, &C).unwrap();

    // check if the instance we created is satisfiable
    let res = inst.is_sat(&assn_witness, &assn_inputs);
    assert_eq!(res.unwrap(), true);

    (inst, assn_witness, assn_inputs, num_cons, num_vars, num_inputs)

}

fn int_to_scalar(i: &Integer) -> Scalar {
    let mut accumulator = Scalar::zero();
    let limb_bits = (std::mem::size_of::<limb_t>() as u64) << 3;
    assert_eq!(limb_bits, 64);

    let two: u64 = 2;
    let mut m = Scalar::from(two.pow(63) as u64);
    m = m * Scalar::from(2 as u64);
    //println!("in int2scal i={:#?}", i);

    // as_ref yeilds a least-significant-first array.
    for digit in i.as_ref().iter().rev() {
        //println!("digit: {:#?}", digit);
        accumulator *= m;
        accumulator += Scalar::from(*digit as u64);
    }
    return accumulator;

}


// circ Lc (const, monomials <Integer>) -> Vec<Variable>
fn lc_to_v(lc: &Lc, const_id: usize, trans: &HashMap<usize,usize>) -> Vec<Variable> {
    let mut v: Vec<Variable> = Vec::new();

    for (k,m) in &lc.monomials {
        if *k >= const_id { panic!("Error: variable number off") }

        let scalar = int_to_scalar(&m);
        //println!("int to scalar test: {:#?} -> {:#?}", m, scalar.to_bytes());
        let var = Variable {
            sid: trans.get(k).unwrap().clone(),
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    if lc.constant != Integer::from(0 as u32) {
        let scalar = int_to_scalar(&lc.constant);
        let var = Variable {
            sid: const_id,
            value: scalar.to_bytes(),
        };
        v.push(var);
    }
    v
}



