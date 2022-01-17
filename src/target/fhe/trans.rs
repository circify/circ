//! Lowering IR to FHE

use crate::ir::term::*;
use crate::target::fhe::*;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool(String),
    Bv(String),
}

struct ToFHE {
    fhe: FHE,
    md: ComputationMetadata,
    inputs: TermMap<Option<PartyId>>,
    cache: TermMap<EmbeddedTerm>,
}

impl ToFHE {
    fn new(metadata: ComputationMetadata) -> Self {
        Self {
            fhe: FHE::new(),
            md: metadata,
            inputs: TermMap::new(),
            cache: TermMap::new(),
        }
    }

    ///Initialize ciphertext and plaintext inputs
    fn init_inputs(&mut self) {
        // let mut ciphtertext_inputs = TermSet::new();
        // let mut plaintext_inputs = TermSet::new();
        todo!();
    }

    /// Given term `t`, type-check `t` is of type Bool and return the variable name for
    /// `t`
    fn get_bool(&self, t: &Term) -> String {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bool(b) => b.clone(),
            _ => panic!("Non-bool for {:?}", t),
        }
    }

    fn embed_bool(&mut self, t: Term) -> String {
        //TODO Matching stuff
        self.get_bool(&t)
    }

    /// Given term `t`, type-check `t` is of type Bv and return the variable name for
    /// `t`
    fn get_bv(&self, t: &Term) -> String {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bv(b) => b.clone(),
            _ => panic!("Non-bv for {:?}", t),
        }
    }

    fn embed_bv(&mut self, t: Term) -> String {
        //TODO Matching Stuff
        self.get_bv(&t)
    }

    fn format_output_circuit(&self, circ: String) -> String {
        format!(
            "TODO: {} \n",
            circ
        )
    }

    fn embed(&mut self, t: Term) -> String {
        let mut circ = String::new();
        for c in PostOrderIter::new(t.clone()){
            println!("Embedding: {:?}", c);
            match check(&c) {
                Sort::Bool => {
                    circ = self.embed_bool(c);
                }
                Sort::BitVector(_) => {
                    circ = self.embed_bv(c);
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }
        }
        self.format_output_circuit(circ)
    }

    /// Given a term `t`, lower `t` to FHE Circuits
    fn lower(&mut self, t: Term) {
        let circ = self.embed(t);
        self.fhe.circs.push(circ);
    }
}

/// Convert this (IR) `ir` to FHE.
pub fn to_aby(ir: Computation) -> FHE {
    let Computation {
        outputs: terms,
        metadata: md,
        values: _,
    } = ir.clone();

    let mut converter = ToFHE::new(md);

    for t in terms {
        println!("Terms: {}", t);
        converter.lower(t.clone());
    }

    // Iterating and lowering the terms populates self.inputs, which
    // are the input parameters for the FHE circuit.
    // Call init_inputs here after self.inputs is populated.
    converter.init_inputs();

    converter.fhe

}