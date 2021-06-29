//! Lowering IR to ABY DSL
//! https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h

use crate::ir::term::*;
use crate::target::aby::*;
use std::collections::HashMap;

const NO_ROLE: u8 = u8::MAX;
const SERVER: u8 = 0;
const CLIENT: u8 = 1;

struct ToABY {
    aby: ABY,
    md: ComputationMetadata,
    seen_party_inputs: HashMap<String, Option<PartyId>>,
    setup: Vec<String>,
    circs: Vec<String>,
    closer: Vec<String>,
    output_gate: String,
}

impl ToABY {
    // Constructor
    fn new(metadata: ComputationMetadata) -> Self {
        Self {
            aby: ABY::new(),
            md: metadata,
            seen_party_inputs: HashMap::new(),
            setup: Vec::new(),
            circs: Vec::new(),
            closer: Vec::new(),
            output_gate: "".to_string(),
        }
    }  

    // Helper Functions
    fn not_in_seen(&mut self, name: &str) -> bool {
        return !self.seen_party_inputs.contains_key(name);
    }

    // Set-up functions
    fn setup(&mut self) {
        self.setup.push("ABYParty* party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg);".to_string());
        self.setup.push("std::vector<Sharing*>& sharings = party->GetSharings();".to_string());
        self.setup.push("Circuit* circ = sharings[sharing]->GetCircuitBuildRoutine();".to_string());
    }

    fn init_inputs(&mut self) {
        let mut server_inputs = Vec::<&str>::new();
        let mut client_inputs = Vec::<&str>::new();

        for (input, visibility) in self.seen_party_inputs.iter() {
            self.setup.push(format!("share *s_{};", input).to_string());
            let role = visibility.unwrap_or_else(|| NO_ROLE);
            if role == SERVER {
                server_inputs.push(input);
            } else if role == CLIENT {
                client_inputs.push(input);
            }
        }

        self.setup.push("if (role == SERVER) {".to_string());
        for input in server_inputs.iter() {
            self.setup.push(format!("\ts_{} = circ->PutINGate({}, bitlen, SERVER);", input, input).to_string());
        }
        for input in client_inputs.iter() {
            self.setup.push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.setup.push("}".to_string());

        self.setup.push("if (role == CLIENT) {".to_string());
        for input in client_inputs.iter() {
            self.setup.push(format!("\ts_{} = circ->PutINGate({}, bitlen, CLIENT);", input, input).to_string());
        }
        for input in server_inputs.iter() {
            self.setup.push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.setup.push("}".to_string());
    }

    fn closer(&mut self) {
        self.closer.push("party->ExecCircuit();".to_string());
        self.closer.push(format!("uint32_t output = s_{}->get_clear_value<uint32_t>();", self.output_gate));
        self.closer.push("delete party;".to_string());
        self.closer.push("return 0;".to_string());
    }

    // Translation functions
    fn embed_bool(&mut self, c: Term) -> String {
        match &c.op {
            Op::Var(name, Sort::Bool) => {
                if self.not_in_seen(&name) {
                    self.seen_party_inputs.insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                }
                
                if self.md.is_input_public(&name) {
                    format!("{}", name)
                } else {
                    format!("s_{}", name)
                }
            },
            Op::Eq => {
                self.output_gate = self.embed(c.cs[0].clone());
                format!("s_{} = circ->PutOUTGate({}, ALL);", self.output_gate.clone(), self.embed(c.cs[1].clone()))
            }, 
            Op::BvBinPred(op) => {
                match op {
                    BvBinPred::Ugt => {
                        let param0 = self.embed(c.cs[0].clone());
                        let param1 = self.embed(c.cs[1].clone());
                        format!("circ->PutGTGate({}, {})", param0, param1)
                    }
                    _ => panic!("Non-field in bool BvBinPred: {}", op),
                }
            },
            _ => panic!("Non-field in embed_bool: {}", c),
        }
    }

    fn embed_bv(&mut self, c: Term) -> String {
        match &c.op {
            Op::Var(name, Sort::BitVector(_)) => {
                if self.not_in_seen(&name) {
                    self.seen_party_inputs.insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                }

                if self.md.is_input_public(&name) {
                    format!("{}", name)
                } else {
                    format!("s_{}", name)
                }
            },
            _ => panic!("Non-field in embed_bv: {}", c),
        }
        
    }

    fn embed(&mut self, t: Term) -> String {
        match check(&t) {
            Sort::Bool => {
                self.embed_bool(t)
            }
            Sort::BitVector(_) => {
                self.embed_bv(t)
            }
            s => panic!("Unsupported sort in embed: {:?}", s),
        }
    }

    fn assert(&mut self, t: Term) {
        let c = self.embed(t);
        self.circs.push(c);
    }
}

/// Convert this (IR) constraint system `cs` to ABY.
pub fn to_aby(cs: Computation) -> ABY {
    println!("");

    let Computation { outputs: terms, metadata: md, values: _ } = cs;

    let mut converter = ToABY::new(md);

    converter.setup();
    for t in terms {
        converter.assert(t.clone());
    }
    converter.init_inputs();
    converter.closer();

    for v in converter.setup.iter() {
        println!("{}", v)
    }
    for v in converter.circs.iter() {
        println!("{}", v)
    }
    for v in converter.closer.iter() {
        println!("{}", v)
    }

    converter.aby
}
