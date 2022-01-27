//! Lowering IR to FHE

//use crate::front::datalog::Inputs;
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
    inputs: TermMap<EncStatus>, 
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

    fn get_var_name(t: Term) -> String {
        match &t.op {
            Op::Var(name, _) => name.to_string(),
            _ => panic!("Term {} is not of type Var", t),
        }
    }

    /// Parse variable name from IR representation of a variable
    fn parse_var_name(&self, full_name: String) -> String {
        let parsed: Vec<String> = full_name.split('_').map(str::to_string).collect();
        if parsed.len() < 2 {
            panic!("Invalid variable name: {}", full_name);
        }
        parsed[parsed.len() - 2].to_string()
    }


    //Writes code for setting up SEAL on the client side.
    fn setup_seal(&mut self) {
        let poly_mod_deg = 4096;
        let plaintext_mod = 1024;

        self.fhe.setup.push(format!(
            "EncryptionParameters parms(scheme_type::bfv);\n\t\
            size_t poly_modulus_degree = {};\n\t\
            parms.set_poly_modulus_degree(poly_modulus_degree);\n\t\
            parms.set_coeff_modulus(CoeffModulus::BFVDefault(poly_modulus_degree));\n\t\
            parms.set_plain_modulus({});\n\t\
            SEALContext context(parms);\n\t\
            \n\t\
            KeyGenerator keygen(context);\n\t\
            SecretKey secret_key = keygen.secret_key();\n\t\
            PublicKey public_key;\n\t\
            keygen.create_public_key(public_key);\n\t\
            Encryptor encryptor(context, public_key);\n\t\
            Evaluator evaluator(context);\n\t\
            Decryptor decryptor(context, secret_key);",
            poly_mod_deg.to_string(),
            plaintext_mod.to_string()
        ));
    }

    //Writes the header for the server_call function in fhe.server
    //Writes the call to server_call with the parameters in fhe.client
    fn add_server_call(&mut self, ptext_in: TermSet, ctext_in: TermSet){
        for t in ptext_in.iter() {
            let name = ToFHE::get_var_name(t.clone());
            self.fhe.header_inputs.push(format!("Plaintext {}_plain, ", name));
            self.fhe.call_inputs.push(format!("{}_plain, ", name));
        }

        for t in ctext_in.iter() {
            let name = ToFHE::get_var_name(t.clone());
            self.fhe.header_inputs.push(format!("Ciphertext_encrypted {}, ", name));
            self.fhe.call_inputs.push(format!("{}_encrypted, ", name));
        }

        match self.fhe.header_inputs.pop() {
            Some(mut input) => {
                input.pop();
                input.pop();
                self.fhe.header_inputs.push(input);
            },
            None => panic!("Vector should not be empty."),
        }

        match self.fhe.call_inputs.pop() {
            Some(mut input) => {
                input.pop();
                input.pop();
                self.fhe.call_inputs.push(input);
            },
            None => panic!("Vector should not be empty."),
        }
    }

    //Writes to fhe.client the computation that runs after the server call
    //ie. Decryption
    fn add_post_computation(&mut self) {
        self.fhe.post_computation.push(
            "cout << output_decrypted.to_string() << endl;".to_string());
    }

    ///Initialize ciphertext and plaintext inputs
    fn init_inputs(&mut self) {
        let mut ptext_inputs = TermSet::new();
        let mut ctext_inputs = TermSet::new();
        
        self.setup_seal();

        // Parse input parameters from command line as uint32_t variables
        // Initialize _____
        for (t, encrypted) in self.inputs.iter() {
            let name = ToFHE::get_var_name(t.clone());
            self.fhe.setup.push(format!(
                "Plaintext {}_plain(uint64_to_hex_string(std::atoi(params[\"{}\"].c_str())));",
                name, 
                self.parse_var_name(name.to_string())
            ));
            if *encrypted {
                self.fhe.setup.push(format!(
                    "Ciphertext {}_encrypted;\n\tencryptor.encrypt({}_plain, {}_encrypted);",
                    name, name, name
                ));
                ctext_inputs.insert(t.clone());
            }
            else {
                ptext_inputs.insert(t.clone());
            }
        }
        self.add_server_call(ptext_inputs, ctext_inputs);
        self.add_post_computation();
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
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                if !self.inputs.contains_key(&t){
                    match *self.md.input_vis.get(name).unwrap(){
                        None => self.inputs.insert(t.clone(), false),
                        Some(_) => self.inputs.insert(t.clone() , true)
                    };
                }
                if !self.cache.contains_key(&t) {
                    self.cache
                    .insert(t.clone(), EmbeddedTerm::Bool(format!("s_{}", name)));
                }
            }
            Op::Const(Value::Bool(b)) => {
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "{}", *b
                    ))
                );
            }
            _ => panic!("Non-field in embed_bool: {:?}", t)
        }
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
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                if !self.inputs.contains_key(&t){
                    match *self.md.input_vis.get(name).unwrap(){
                        None => self.inputs.insert(t.clone(), false),
                        Some(_) => self.inputs.insert(t.clone() , true)
                    };
                }
                if !self.cache.contains_key(&t) {
                    self.cache
                    .insert(t.clone(), EmbeddedTerm::Bv(format!("s_{}", name)));
                }
            }
            Op::Const(Value::BitVector(b)) => {
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "{}", *b
                    ))
                );
            }
            _ => {panic!("Non-field in embed_bv: {:?}", t);}
        }

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
        self.fhe.server.push(circ);
    }
}

/// Convert this (IR) `ir` to FHE.
pub fn to_fhe(ir: Computation) -> FHE {
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