//! Call Site Similarity

use crate::ir::term::*;

/// Determine if call sites are similar based on input and output arguments to the call site
pub fn call_site_similarity(fs: &mut Functions) {
    // Return a TermMap of (call) --> id for which calls are similar
    // Maybe return a vector of vector of terms 

    // Map of Vec<input: Vec<Term>, output: Vec<Term>> --> Vec<Call Term>

    for (name, comp) in fs.computations {

        // Post order traversal through each computation

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
