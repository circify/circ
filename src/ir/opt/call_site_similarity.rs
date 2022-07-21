//! Call Site Similarity

use crate::ir::term::*;

/// Determine if call sites are similar based on input and output arguments to the call site
pub fn call_site_similarity(fs: &mut Functions) {
    // Return a TermMap of (call) --> id for which calls are similar
    // Maybe return a vector of vector of terms

    // Map of Vec<input: Vec<Term>, output: Vec<Term>> --> Vec<Call Term>

    // For each call site, (input: Vec<Term>, output: Vec<Term>) -> Term (call)
    let mut call_sites: TermMap<(Vec<Term>, Vec<Term>)> = TermMap::new();

    for (name, comp) in fs.computations {
        // Post order traversal through each computation

        for t in comp.terms_postorder() {
            match t.op {
                Op::Call(name, arg_names, arg_sorts, ret_sorts) => {
                    let input: Vec<Term> = t.cs;
                    let output: Vec<Term> = Vec::new();
                    call_sites.insert(t.clone(), (input, output));
                }
                _ => {
                    // see if the call term was used as an argument in another term
                    for c in t.cs {
                        if call_sites.contains_key(&c) {
                            call_sites.get(c).1.push(t.clone());
                        }
                    }
                }
            }
        }

        // For each call term
        // Get a list of inputs and output terms based on mutation step size
        // Store input terms into a data structure (vec?)
        // Store output terms into a data structure (vec?)
        // Order terms by operator

        // Create key: Vec<input: Vec<Term>, output: Vec<Term>>

        // loop through existing call terms:
        // longest prefix matching (edit distance?)

        // if match:
        // append to vec
        // if no match:
        // add as new entry
    }
}
