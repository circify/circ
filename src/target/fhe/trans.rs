//! Lowering IR to FHE

//use crate::front::datalog::Inputs;
use crate::ir::term::*;
use crate::target::fhe::*;
use fxhash::FxHashMap;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool(String, bool),
    Bv(String, bool),
}

struct ToFHE {
    fhe: FHE,
    md: ComputationMetadata,
    inputs: TermMap<EncStatus>,
    input_map: Option<FxHashMap<String, Value>>,
    cache: TermMap<EmbeddedTerm>,
    term_cnt: i32,
}

impl ToFHE {
    fn new(metadata: ComputationMetadata, values: Option<FxHashMap<String, Value>>) -> Self {
        Self {
            fhe: FHE::new(),
            md: metadata,
            inputs: TermMap::new(),
            input_map: values,
            cache: TermMap::new(),
            term_cnt: 0,
        }
    }

    fn get_var_name(t: Term) -> String {
        match &t.op {
            Op::Var(name, _) => name.to_string(),
            _ => panic!("Term {} is not of type Var", t),
        }
    }

    fn get_term_name(&mut self) -> String {
        format!("term_{}", self.term_cnt)
    }

    fn inc_term(&mut self) {
        self.term_cnt += 1;
    }

    fn value_to_hex_poly(&self, val: &Value) -> String {
        match *val {
            Value::Bool(true) => "1".to_string(),
            Value::Bool(false) => "0".to_string(),
            _ => panic!("TODO: Unimplemented"),
        }
    }

    /// Handles the inputs to the main function.
    /// If an input's value is provided in the input file, it is initialized
    /// accordingly within the main function
    /// Otherwise, it is listed as an input to the main function
    fn handle_main_inputs(&mut self) {
        match &self.input_map {
            Some(map) => {
                for (t, _) in self.inputs.iter() {
                    let name = ToFHE::get_var_name(t.clone());
                    match map.get(&name) {
                        Some(val) => {
                            //TODO: change val to hex polynomial format
                            self.fhe.setup.push(format!(
                                "Plaintext {}_plain(\"{}\");",
                                name,
                                self.value_to_hex_poly(val)
                            ));
                        }
                        None => {
                            self.fhe.main_inputs.push(format!("Plaintext {}, ", name));
                        }
                    }
                }
            }
            None => {
                for (t, _) in self.inputs.iter() {
                    let name = ToFHE::get_var_name(t.clone());
                    self.fhe.main_inputs.push(format!("Plaintext {}, ", name));
                }
            }
        }

        match self.fhe.main_inputs.pop() {
            Some(mut input) => {
                input.pop();
                input.pop();
                self.fhe.main_inputs.push(input);
            }
            None => (),
        }
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
    fn add_server_call(&mut self, ptext_in: TermSet, ctext_in: TermSet) {
        for t in ptext_in.iter() {
            let name = ToFHE::get_var_name(t.clone());
            self.fhe
                .header_inputs
                .push(format!(", Plaintext {}_plain", name));
            self.fhe.call_inputs.push(format!(", {}_plain", name));
        }

        for t in ctext_in.iter() {
            let name = ToFHE::get_var_name(t.clone());
            self.fhe
                .header_inputs
                .push(format!(", Ciphertext {}_encrypted", name));
            self.fhe.call_inputs.push(format!(", {}_encrypted", name));
        }
    }

    //Writes to fhe.client the computation that runs after the server call
    //ie. Decryption
    fn add_post_computation(&mut self) {
        self.fhe
            .post_computation
            .push("cout << \"Output Value: \" << output_plain.to_string() << endl;".to_string());
    }

    ///Initialize ciphertext and plaintext inputs
    fn init_inputs(&mut self) {
        let mut ptext_inputs = TermSet::new();
        let mut ctext_inputs = TermSet::new();

        self.setup_seal();

        self.handle_main_inputs();

        // Encrypt necessary terms
        for (t, encrypted) in self.inputs.iter() {
            let name = ToFHE::get_var_name(t.clone());
            if *encrypted {
                self.fhe.setup.push(format!(
                    "Ciphertext {}_encrypted;\n\tencryptor.encrypt({}_plain, {}_encrypted);",
                    name, name, name
                ));
                ctext_inputs.insert(t.clone());
            } else {
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
            .unwrap_or_else(|| panic!("Missing expression for {:?}", t))
        {
            EmbeddedTerm::Bool(b, _) => b.clone(),
            _ => panic!("Non-bool for {:?}", t),
        }
    }

    fn get_enc_status(&self, t: &Term) -> bool {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing expression for {:?}", t))
        {
            EmbeddedTerm::Bool(_, e) => e.clone(),
            EmbeddedTerm::Bv(_, e) => e.clone(),
        }
    }

    fn embed_bool_and(&mut self, a: String, a_enc: bool, b: String, b_enc: bool, term: String) {
        self.fhe.server.push(format!("Ciphertext {};", term));
        self.fhe.server.push(match (a_enc, b_enc) {
            (true, true) => format!("evaluator.multiply({}, {}, {});", a, b, term),
            (true, false) => format!("evaluator.multiply_plain({}, {}, {});", a, b, term),
            (false, true) => format!("evaluator.multiply_plain({}, {}, {});", b, a, term),
            (false, false) => format!(
                "encryptor.encrypt({}, {})\n\tevaluator.multiply_plain_inplace({}, {});",
                a, term, term, b
            ),
        });
    }

    fn embed_bool_or(&mut self, a: String, a_enc: bool, b: String, b_enc: bool, term: String) {
        self.fhe.server.push("Ciphertext prod;".to_string());

        self.fhe.server.push(match (a_enc, b_enc) {
            (true, true) => format!("evaluator.multiply({}, {}, prod);", a, b),
            (true, false) => format!("evaluator.multiply_plain({}, {}, prod);", a, b),
            (false, true) => format!("evaluator.multiply_plain({}, {}, prod);", b, a),
            (false, false) => format!(
                "encryptor.encrypt({}, prod)\n\tevaluator.multiply_plain_inplace(prod, {});",
                a, b
            ),
        });

        self.fhe.server.push(format!("Ciphertext {};", term));

        self.fhe.server.push(match (a_enc, b_enc) {
            (true, true) => format!("evaluator.add({}, {}, {});", a, b, term),
            (true, false) => format!("evaluator.add_plain({}, {}, {});", a, b, term),
            (false, true) => format!("evaluator.add_plain({}, {}, {});", b, a, term),
            (false, false) => format!(
                "encryptor.encrypt({}, {})\n\tevaluator.add_plain_inplace({}, {});",
                a, term, term, b
            ),
        });

        self.fhe
            .server
            .push(format!("evaluator.sub_inplace({}, prod);", term));
    }

    fn embed_bool_xor(&mut self, a: String, a_enc: bool, b: String, b_enc: bool, term: String) {
        self.embed_bool_or(a, a_enc, b, b_enc, term.clone());
        self.fhe
            .server
            .push(format!("evaluator.sub_inplace({}, prod);", term));
    }

    fn embed_bool(&mut self, t: Term) -> String {
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                if !self.inputs.contains_key(&t) {
                    match *self.md.input_vis.get(name).unwrap() {
                        None => self.inputs.insert(t.clone(), false),
                        Some(_) => self.inputs.insert(t.clone(), true),
                    };
                }
                if !self.cache.contains_key(&t) {
                    match *self.md.input_vis.get(name).unwrap() {
                        None => self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("{}_plain", name), false),
                        ),
                        Some(_) => self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("{}_encrypted", name), true),
                        ),
                    };
                }
            }
            Op::Const(Value::Bool(b)) => {
                self.cache
                    .insert(t.clone(), EmbeddedTerm::Bool(format!("{}", *b), false));
            }
            Op::BoolNaryOp(o) => {
                let a_circ = self.get_bool(&t.cs[0]);
                let b_circ = self.get_bool(&t.cs[1]);

                let term = self.get_term_name();
                self.inc_term();

                match o {
                    BoolNaryOp::And => {
                        self.embed_bool_and(
                            a_circ,
                            self.get_enc_status(&t.cs[0]),
                            b_circ,
                            self.get_enc_status(&t.cs[1]),
                            term.clone(),
                        );
                    }
                    BoolNaryOp::Or => {
                        self.embed_bool_or(
                            a_circ,
                            self.get_enc_status(&t.cs[0]),
                            b_circ,
                            self.get_enc_status(&t.cs[1]),
                            term.clone(),
                        );
                    }
                    BoolNaryOp::Xor => {
                        self.embed_bool_xor(
                            a_circ,
                            self.get_enc_status(&t.cs[0]),
                            b_circ,
                            self.get_enc_status(&t.cs[1]),
                            term.clone(),
                        );
                    }
                }
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(term, true));
            }
            _ => panic!("Non-field in embed_bool: {:?}", t),
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
            EmbeddedTerm::Bv(b, _) => b.clone(),
            _ => panic!("Non-bv for {:?}", t),
        }
    }

    fn embed_bv(&mut self, t: Term) -> String {
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                if !self.inputs.contains_key(&t) {
                    match *self.md.input_vis.get(name).unwrap() {
                        None => self.inputs.insert(t.clone(), false),
                        Some(_) => self.inputs.insert(t.clone(), true),
                    };
                }
                if !self.cache.contains_key(&t) {
                    match *self.md.input_vis.get(name).unwrap() {
                        None => self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("{}_plain", name), false),
                        ),
                        Some(_) => self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("{}_encrypted", name), true),
                        ),
                    };
                }
            }
            Op::Const(Value::BitVector(b)) => {
                self.cache
                    .insert(t.clone(), EmbeddedTerm::Bool(format!("{}", *b), false));
            }
            _ => {
                panic!("Non-field in embed_bv: {:?}", t);
            }
        }

        self.get_bv(&t)
    }

    fn format_output_circuit(&self, circ: String) -> String {
        //TODO
        format!("{}", circ)
    }

    fn embed(&mut self, t: Term) -> String {
        let mut circ = String::new();
        for c in PostOrderIter::new(t.clone()) {
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

    /// Given a term `t`, lower `t` to FHE program
    fn lower(&mut self, t: Term) {
        let circ = self.embed(t);
        self.fhe.server.push(format!("return {};", circ));
    }
}

/// Convert this (IR) `ir` to FHE.
pub fn to_fhe(ir: Computation) -> FHE {
    let Computation {
        outputs: terms,
        metadata: md,
        values,
    } = ir.clone();

    let mut converter = ToFHE::new(md, values);

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
