//! Call Site Similarity

use crate::ir::term::*;

use std::collections::HashMap;

/// Determine if call sites are similar based on input and output arguments to the call site
pub fn call_site_similarity(fs: &Functions) {
    // Return a TermMap of (call) --> id for which calls are similar
    // Maybe return a vector of vector of terms

    // Map of Vec<input: Vec<Term>, output: Vec<Term>> --> Vec<Call Term>

    //  map call Term -> (input: Vec<Term>, output: Vec<Term>)
    let mut call_term_map: TermMap<(Vec<Term>, Vec<Term>)> = TermMap::new();

    // map field(i) Term to parent call Term
    let mut field_of_calls: TermMap<Term> = TermMap::new();

    for (_name, comp) in &fs.computations {
        for t in comp.terms_postorder() {
            // see if the call term was used as an argument in another term
            for c in &t.cs {
                if call_term_map.contains_key(c) {
                    field_of_calls.insert(t.clone(), c.clone());
                }
                if field_of_calls.contains_key(c) {
                    let call_term = field_of_calls.get(c).unwrap();
                    call_term_map.get_mut(call_term).unwrap().1.push(t.clone());
                }
            }
            match &t.op {
                Op::Call(..) => {
                    let input: Vec<Term> = t.cs.clone();
                    let output: Vec<Term> = Vec::new();
                    call_term_map.insert(t.clone(), (input, output));
                }
                _ => {
                    // do nothing
                }
            }
        }

        // For each call term
        // Get a list of inputs and output terms based on mutation step size
        // Store input terms into a data structure (vec?)
        // Store output terms into a data structure (vec?)
        // Order terms by operator

        // Create key: Vec<input: Vec<Term>, output: Vec<Term>>
        // SORT OUTPUT TERMS

        // loop through existing call terms:
        // longest prefix matching (edit distance?)

        // if match:
        // append to vec
        // if no match:
        // add as new entry
    }

    // Clean input and output terms
    let mut call_sites: HashMap<(Vec<Op>, Vec<Op>), Vec<Term>> = HashMap::new();
    

    for (c, (i, o)) in call_term_map {
        println!("function: {}", c);
        println!(
            "inputs: {:?}",
            i.iter().map(|x| x.op.clone()).collect::<Vec<Op>>()
        );
        println!(
            "outputs: {:?}\n",
            o.iter().map(|x| x.op.clone()).collect::<Vec<Op>>()
        );
    }
    todo!();


    // return call_sites values 
}
