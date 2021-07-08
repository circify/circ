//! Lowering IR to ABY DSL
//! https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h

//! Weird boolean circuit stuff with inv: https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml

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
    seen_party_inputs: HashMap<String, Option<PartyId>>,
    cache: TermMap<EmbeddedTerm>,

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
            cache: TermMap::new(),
            setup: Vec::new(),
            circs: Vec::new(),
            closer: Vec::new(),
            output_gate: "out".to_string(),
        }
    }

    // Helper Functions
    fn not_in_seen(&mut self, name: &str) -> bool {
        return !self.seen_party_inputs.contains_key(name);
    }

    // Set-up functions
    fn setup(&mut self) {
        self.setup.push("ABYParty* party = new ABYParty(role, address, port, seclvl, bitlen, nthreads, mt_alg);".to_string());
        self.setup
            .push("std::vector<Sharing*>& sharings = party->GetSharings();".to_string());
        self.setup
            .push("Circuit* circ = sharings[sharing]->GetCircuitBuildRoutine();".to_string());
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
        self.setup
            .push(format!("share *s_{};", self.output_gate).to_string());

        self.setup.push("if (role == SERVER) {".to_string());
        for input in server_inputs.iter() {
            self.setup.push(
                format!(
                    "\ts_{} = circ->PutINGate({}, bitlen, SERVER);",
                    input, input
                )
                .to_string(),
            );
        }
        for input in client_inputs.iter() {
            self.setup
                .push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.setup.push("}".to_string());

        self.setup.push("if (role == CLIENT) {".to_string());
        for input in client_inputs.iter() {
            self.setup.push(
                format!(
                    "\ts_{} = circ->PutINGate({}, bitlen, CLIENT);",
                    input, input
                )
                .to_string(),
            );
        }
        for input in server_inputs.iter() {
            self.setup
                .push(format!("\ts_{} = circ->PutDummyINGate(bitlen);", input).to_string());
        }
        self.setup.push("}".to_string());
    }

    fn closer(&mut self) {
        self.closer.push("party->ExecCircuit();".to_string());
        self.closer.push(format!(
            "uint32_t output = s_{}->get_clear_value<uint32_t>();",
            self.output_gate
        ));
        self.closer.push("delete party;".to_string());
        self.closer.push("return 0;".to_string());
    }

    // Translation functions

    fn zero() -> String {
        format!("circ->PutCONSGate((uint_64)0, (uint_32)1)")
    }

    fn embed_eq(&mut self, t: Term, a: &Term, b: &Term) -> String {
        match check(a) {
            Sort::Bool => {
                let a = self.get_bool(a).clone();
                let b = self.get_bool(b).clone();

                let s = format!(
                    "((BooleanCircuit *)circ)->PutINVGate(circ->PutXORGate({}, {}))",
                    a, b
                );
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(s.clone()));
                s
            }
            Sort::BitVector(_) => {
                let a = self.get_bv(a).clone();
                let b = self.get_bv(b).clone();
                let s = format!(
                    "circ->PutXORGate(circ->PutGTGate({}, {}), circ->PutGTGate({}, {})) ",
                    a, b, b, a
                );
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(s.clone()));
                s
            }
            e => panic!("Unimplemented sort for Eq: {:?}", e),
        }
    }

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
                if self.not_in_seen(&name) {
                    self.seen_party_inputs
                        .insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                }
                if self.md.is_input_public(&name) {
                    if !self.cache.contains_key(&t) {
                        self.cache
                            .insert(t.clone(), EmbeddedTerm::Bool(format!("{}", name)));
                    }
                } else {
                    if !self.cache.contains_key(&t) {
                        self.cache
                            .insert(t.clone(), EmbeddedTerm::Bool(format!("s_{}", name)));
                    }
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
                let a = self.get_bool(&t.cs[1]).clone();
                let b = self.get_bool(&t.cs[2]).clone();
                match o {
                    BoolNaryOp::Or => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("circ->PutORGate({}, {})", a, b)),
                        );
                    }
                    BoolNaryOp::And => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("circ->PutANDGate({}, {})", a, b)),
                        );
                    }
                    BoolNaryOp::Xor => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!("circ->PutXORGate({}, {})", a, b)),
                        );
                    }
                }
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
                                "circ->OR(circ->PutGTGate({}, {}), {})",
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
                                "circ->OR(circ->PutXORGate(circ->PutGTGate({}, {}), {}), {})",
                                a,
                                b,
                                ToABY::zero(),
                                eq
                            )),
                        );
                    }
                    BvBinPred::Ult => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "circ->PutXORGate(circ->PutGTGate({}, {}), {})",
                                a,
                                b,
                                ToABY::zero(),
                            )),
                        );
                    }
                    _ => panic!("Non-field in bool BvBinPred: {}", op),
                }
            }
            _ => panic!("Non-field in embed_bool: {}", t),
        }

        self.get_bool(&t)
    }

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
                if self.not_in_seen(&name) {
                    self.seen_party_inputs
                        .insert(name.to_string(), *self.md.inputs.get(name).unwrap());
                }
                if self.md.is_input_public(&name) {
                    if !self.cache.contains_key(&t) {
                        self.cache
                            .insert(t.clone(), EmbeddedTerm::Bv(format!("{}", name)));
                    }
                } else {
                    if !self.cache.contains_key(&t) {
                        self.cache
                            .insert(t.clone(), EmbeddedTerm::Bv(format!("s_{}", name)));
                    }
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

                match o {
                    BvNaryOp::Xor => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutXORGate({}, {})", a, b)),
                        );
                    }
                    BvNaryOp::Or => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutORGate({}, {})", a, b)),
                        );
                    }
                    BvNaryOp::And => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutANDGate({}, {})", a, b)),
                        );
                    }
                    BvNaryOp::Add => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutADDGate({}, {})", a, b)),
                        );
                    }
                    BvNaryOp::Mul => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!("circ->PutMULGate({}, {})", a, b)),
                        );
                    }
                }
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

    fn add_output_gate(&mut self, circ: String) -> String {
        format!(
            "s_{} = circ->PutOUTGate({}, ALL);",
            self.output_gate.clone(),
            circ
        )
    }

    fn assert(&mut self, t: Term) {
        let mut output_circ = self.embed(t);
        output_circ = self.add_output_gate(output_circ);
        self.circs.push(output_circ);
    }
}

/// Convert this (IR) constraint system `cs` to ABY.
pub fn to_aby(cs: Computation) -> ABY {
    let Computation {
        outputs: terms,
        metadata: md,
        values: _,
    } = cs;
    let mut converter = ToABY::new(md);

    converter.setup();
    for t in terms {
        println!("Terms: {}", t);
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
