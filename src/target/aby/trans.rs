//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use crate::ir::term::*;
use crate::target::aby::*;
use std::collections::HashMap;

const NO_ROLE: u8 = u8::MAX;
const SERVER: u8 = 0;
const CLIENT: u8 = 1;
const BOOLEAN_BITLEN: i32 = 1;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool(String),
    Bv(String),
}

struct ToABY {
    aby: ABY,
    md: ComputationMetadata,
    inputs: HashMap<String, Option<PartyId>>,
    inputs_order: Vec<String>,
    cache: TermMap<EmbeddedTerm>,
    output_gate: String,
}

impl ToABY {
    fn new(metadata: ComputationMetadata) -> Self {
        Self {
            aby: ABY::new(),
            md: metadata,
            inputs: HashMap::new(),
            inputs_order: Vec::new(),
            cache: TermMap::new(),
            output_gate: "out".to_string(),
        }
    }

    /// Initialize the ABY Party, sharing scheme, and Circuit object
    fn setup(&mut self) {
        self.aby.setup.push("ABYParty* party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg);".to_string());
        self.aby
            .setup
            .push("std::vector<Sharing*>& sharings = party->GetSharings();".to_string());
        self.aby
            .setup
            .push("Circuit* circ = sharings[sharing]->GetCircuitBuildRoutine();".to_string());
    }

    /// Initialize private and public inputs from each party
    /// Party inputs are stored in *self.inputs*
    fn init_inputs(&mut self) {
        let mut server_inputs = Vec::<&str>::new();
        let mut client_inputs = Vec::<&str>::new();
        let mut public_inputs = Vec::<&str>::new();
        let mut counter = 0;

        // Parse input parameters from command line as uint32_t variables
        // Initialize shares for each party
        self.inputs_order.reverse();
        for input in self.inputs_order.iter() {
            let visibility = self.inputs.get(input).unwrap();
            self.aby.setup.push(format!(
                "uint32_t {} = std::atoi(params[{}].c_str());",
                input.to_string(),
                counter
            ));
            self.aby
                .setup
                .push(format!("share *s_{};", input).to_string());
            let role = visibility.unwrap_or_else(|| NO_ROLE);
            if role == SERVER {
                server_inputs.push(input);
            } else if role == CLIENT {
                client_inputs.push(input);
            } else if role != SERVER && role != CLIENT && self.md.is_input_public(&input) {
                public_inputs.push(input);
            } else {
                panic!("Unknown role or visibility for input: {}", input);
            }
            counter += 1;
        }

        // Initialize output gate
        self.aby
            .setup
            .push(format!("share *s_{};", self.output_gate).to_string());

        // Initialize public inputs as CONS shares
        for input in public_inputs.iter() {
            self.aby
                .setup
                .push(format!("s_{} = circ->PutCONSGate({}, bitlen);", input, input).to_string());
        }

        // Initialize Server inputs
        self.aby.setup.push("if (role == SERVER) {".to_string());
        for input in server_inputs.iter() {
            self.aby.setup.push(
                format!(
                    "\ts_{} = circ->PutINGate({}, bitlen, SERVER);",
                    input, input
                )
                .to_string(),
            );
        }
        for input in client_inputs.iter() {
            self.aby
                .setup
                .push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.aby.setup.push("}".to_string());

        // Initialize Client inputs
        self.aby.setup.push("if (role == CLIENT) {".to_string());
        for input in client_inputs.iter() {
            self.aby.setup.push(
                format!(
                    "\ts_{} = circ->PutINGate({}, bitlen, CLIENT);",
                    input, input
                )
                .to_string(),
            );
        }
        for input in server_inputs.iter() {
            self.aby
                .setup
                .push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.aby.setup.push("}\n".to_string());
    }

    /// Clean up code to execute circuit, get circuit output, and return
    fn closer(&mut self) {
        self.aby.closer.push("\tparty->ExecCircuit();".to_string());
        self.aby.closer.push(format!(
            "uint32_t output = s_{}->get_clear_value<uint32_t>();\n\tstd::cout << \"output: \" << output << std::endl;",
            self.output_gate
        ));
        self.aby.closer.push("delete party;".to_string());
        self.aby.closer.push("return 0;".to_string());
    }

    /// Return constant gate evaluating to 0
    fn zero() -> String {
        format!("circ->PutCONSGate((uint64_t)0, (uint32_t)1)")
    }

    /// Return constant gate evaluating to 1
    fn one() -> String {
        format!("circ->PutCONSGate((uint64_t)1, (uint32_t)1)")
    }

    fn embed_eq(&mut self, t: Term, a: &Term, b: &Term) -> String {
        match check(a) {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let b = self.get_bool(b).clone();

                let s = format!(
                    "circ->PutXORGate(circ->PutXORGate({}, {}), {})",
                    a,
                    b,
                    ToABY::one()
                );
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(s.clone()));
                s
            }
            Sort::BitVector(_) => {
                let a = self.get_bv(a).clone();
                let b = self.get_bv(b).clone();
                let s = format!(
                    "circ->PutXORGate(circ->PutXORGate(circ->PutGTGate({}, {}), circ->PutGTGate({}, {})), {})",
                    a, b, b, a, ToABY::one()
                );
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(s.clone()));
                s
            }
            e => panic!("Unimplemented sort for Eq: {:?}", e),
        }
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
                if !self.inputs.contains_key(name) {
                    self.inputs
                        .insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                    self.inputs_order.push(name.to_string());
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
                        "circ->PutCONSGate((uint64_t){}, (uint32_t){})",
                        *b as isize, BOOLEAN_BITLEN
                    )),
                );
            }
            Op::Eq => {
                let _s = self.embed_eq(t.clone(), &t.cs[0], &t.cs[1]);
            }
            Op::Ite => {
                let sel = self.get_bool(&t.cs[0]).clone();
                let a = self.get_bool(&t.cs[1]).clone();
                let b = self.get_bool(&t.cs[2]).clone();
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!("circ->PutMUXGate({}, {}, {})", a, b, sel)),
                );
            }
            Op::Not => {
                let a = self.get_bool(&t.cs[0]);
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!("((BooleanCircuit *)circ)->PutINVGate({})", a)),
                );
            }
            Op::BoolNaryOp(o) => {
                let a = self.get_bool(&t.cs[0]).clone();
                let b = self.get_bool(&t.cs[1]).clone();

                let mut circ = "circ";
                if *o == BoolNaryOp::Or {
                    circ = "((BooleanCircuit *)circ)";
                }

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "{}->{}({}, {})",
                        circ,
                        match o {
                            BoolNaryOp::Or => "PutORGate",
                            BoolNaryOp::And => "PutANDGate",
                            BoolNaryOp::Xor => "PutXORGate"
                        },
                        a,
                        b
                    )),
                );
            }
            Op::BvBinPred(op) => {
                let a = self.get_bv(&t.cs[0]);
                let b = self.get_bv(&t.cs[1]);

                match op {
                    BvBinPred::Uge => {
                        let eq = self.embed_eq(t.clone(), &t.cs[0], &t.cs[1]);
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "((BooleanCircuit *)circ)->PutORGate(circ->PutGTGate({}, {}), {})",
                                a, b, eq
                            )),
                        );
                    }
                    BvBinPred::Ugt => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("circ->PutGTGate({}, {})", a, b)),
                        );
                    }
                    BvBinPred::Ule => {
                        let eq = self.embed_eq(t.clone(), &t.cs[0], &t.cs[1]);
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "((BooleanCircuit *)circ)->PutORGate(circ->PutGTGate({}, {}), {})",
                                b, a, eq
                            )),
                        );
                    }
                    BvBinPred::Ult => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("circ->PutGTGate({}, {})", b, a)),
                        );
                    }
                    _ => panic!("Non-field in bool BvBinPred: {}", op),
                }
            }
            _ => panic!("Non-field in embed_bool: {}", t),
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
                if !self.inputs.contains_key(name) {
                    self.inputs
                        .insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                    self.inputs_order.push(name.to_string());
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
                        "circ->PutCONSGate((uint64_t){}, (uint32_t){})",
                        b,
                        b.width()
                    )),
                );
            }
            Op::Ite => {
                let sel = self.get_bool(&t.cs[0]).clone();
                let a = self.get_bv(&t.cs[1]).clone();
                let b = self.get_bv(&t.cs[2]).clone();
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!("circ->PutMUXGate({}, {}, {})", a, b, sel)),
                );
            }
            Op::BvNaryOp(o) => {
                let a = self.get_bv(&t.cs[0]);
                let b = self.get_bv(&t.cs[1]);

                let mut circ = "circ";
                if *o == BvNaryOp::Or {
                    circ = "((BooleanCircuit *)circ)";
                }

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bv(format!(
                        "{}->{}({}, {})",
                        circ,
                        match o {
                            BvNaryOp::Xor => "PutXORGate",
                            BvNaryOp::Or => "PutORGate",
                            BvNaryOp::And => "PutANDGate",
                            BvNaryOp::Add => "PutADDGate",
                            BvNaryOp::Mul => "PutMULGate",
                        },
                        a,
                        b
                    )),
                );
            }
            Op::BvBinOp(o) => {
                let a = self.get_bv(&t.cs[0]);
                let b = self.get_bv(&t.cs[1]);

                match o {
                    BvBinOp::Sub => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutSUBGate({}, {})", a, b)),
                        );
                    }
                    _ => panic!("Invalid bv-op in BvBinOp: {:?}", o),
                }
            }
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }

        self.get_bv(&t)
    }

    fn embed(&mut self, t: Term) -> String {
        let mut output_circ: String = "".to_string();
        for c in PostOrderIter::new(t) {
            match check(&c) {
                Sort::Bool => {
                    output_circ = self.embed_bool(c);
                }
                Sort::BitVector(_) => {
                    output_circ = self.embed_bv(c);
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }
        }
        output_circ
    }

    /// Given a Circuit `circ`, wrap `circ` in an OUT gate to extract the value of
    /// the circuit to a share      
    ///
    /// Return a String of the resulting Circuit
    fn add_output_gate(&mut self, circ: String) -> String {
        format!(
            "\ts_{} = circ->PutOUTGate({}, ALL);\n",
            self.output_gate.clone(),
            circ
        )
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self, t: Term) {
        let mut output_circ = self.embed(t);
        output_circ = self.add_output_gate(output_circ);
        self.aby.circs.push(output_circ);
    }
}

/// Convert this (IR) `ir` to ABY.
pub fn to_aby(ir: Computation) -> ABY {
    let Computation {
        outputs: terms,
        metadata: md,
        values: _,
    } = ir;
    let mut converter = ToABY::new(md);

    converter.setup();
    for t in terms {
        println!("Terms: {}", t);
        converter.lower(t.clone());
    }

    // Iterating and lowering the terms populates self.inputs, which
    // are the input parameters for the ABY circuit.
    // Call init_inputs here after self.inputs is populated.
    converter.init_inputs();
    converter.closer();

    converter.aby
}
