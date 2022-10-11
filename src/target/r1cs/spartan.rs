//! Export circ R1cs to Spartan
use libspartan::*;
use crate::target::r1cs::*;
use curve25519_dalek::scalar::Scalar;
use rug::{Integer};
use core::clone::Clone;

use std::collections::HashMap;
use gmp_mpfr_sys::gmp::limb_t;

/// Hold Spartan variables
#[derive(Debug)]
pub struct Variable {
    sid: usize,
    value: [u8; 32],
}


/// circ R1cs -> spartan R1CSInstance
pub fn r1cs_to_spartan<S: Eq + Hash + Clone + Display>(r1cs: R1cs<S>) -> (Instance, Assignment, Assignment, usize, usize, usize)
{

    // spartan format mapper: CirC -> Spartan
    let mut wit = Vec::new();
    let mut inp = Vec::new();
    let mut trans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids
    let mut itrans: HashMap<usize, usize> = HashMap::new(); // Circ -> spartan ids

    match r1cs.values {
        Some(_) =>
            for (k,v) in r1cs.values.as_ref().unwrap() { // CirC id, Integer

                //let name = r1cs.idxs_signals.get(k).unwrap().to_string();
                let scalar = int_to_scalar(&v.i());

                if r1cs.public_idxs.contains(k) {
                    // input
                    //println!("As public io: {}", name);

                    itrans.insert(*k, inp.len());
                    inp.push(scalar.to_bytes());
                } else {
                     // witness
                    //println!("As private witness: {}", name);

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

