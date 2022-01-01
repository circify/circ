//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use crate::ir::term::*;
// use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::{some_arith_sharing, ShareType, SharingMap};
use crate::target::aby::*;

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
    inputs: TermMap<Option<PartyId>>,
    cache: TermMap<EmbeddedTerm>,
    s_map: SharingMap,
}

impl ToABY {
    fn new(metadata: ComputationMetadata, s_map: SharingMap) -> Self {
        Self {
            aby: ABY::new(),
            md: metadata,
            inputs: TermMap::new(),
            cache: TermMap::new(),
            s_map,
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

    fn get_sharetype_circ(&self, t: Term) -> String {
        if !self.s_map.contains_key(&t) {
            panic!("No sharing type for {:?}", t);
        }
        let s = self.s_map.get(&t).unwrap();
        match *s {
            ShareType::Arithmetic => "acirc".to_string(),
            ShareType::Boolean => "bcirc".to_string(),
            ShareType::Yao => "ycirc".to_string(),
        }
    }

    fn add_conv_gate(&self, p_t: Term, c_t: Term, c_circ: String) -> String {
        let p_share = self.s_map.get(&p_t).unwrap();
        let c_share = self.s_map.get(&c_t).unwrap();

        match (c_share, p_share) {
            (ShareType::Arithmetic, ShareType::Arithmetic) => c_circ,
            (ShareType::Boolean, ShareType::Boolean) => c_circ,
            (ShareType::Yao, ShareType::Yao) => c_circ,
            (ShareType::Arithmetic, ShareType::Boolean) => {
                format!("bcirc->PutY2BGate(ycirc->PutA2YGate({}))", c_circ)
            }
            (ShareType::Arithmetic, ShareType::Yao) => format!("ycirc->PutA2YGate({})", c_circ),
            (ShareType::Boolean, ShareType::Arithmetic) => format!("acirc->PutB2AGate({})", c_circ),
            (ShareType::Boolean, ShareType::Yao) => format!("ycirc->PutB2YGate({})", c_circ),
            (ShareType::Yao, ShareType::Arithmetic) => {
                format!("acirc->PutB2AGate(bcirc->PutY2BGate({}))", c_circ)
            }
            (ShareType::Yao, ShareType::Boolean) => format!("bcirc->PutY2BGate({})", c_circ),
        }
    }

    fn add_cons_gate(&self, t: Term) -> String {
        let name = ToABY::get_var_name(t.clone());
        let s_circ = self.get_sharetype_circ(t);
        format!(
            "s_{} = {}->PutCONSGate((uint64_t){}, bitlen);",
            name, s_circ, name
        )
    }

    fn add_in_gate(&self, t: Term, role: String) -> String {
        let name = ToABY::get_var_name(t.clone());
        let s_circ = self.get_sharetype_circ(t);
        format!(
            "\ts_{} = {}->PutINGate({}, bitlen, {});",
            name, s_circ, name, role
        )
    }

    fn add_dummy_gate(&self, t: Term) -> String {
        let name = ToABY::get_var_name(t.clone());
        let s_circ = self.get_sharetype_circ(t);
        format!("\ts_{} = {}->PutDummyINGate(bitlen);", name, s_circ)
    }

    /// Initialize private and public inputs from each party
    /// Party inputs are stored in *self.inputs*
    fn init_inputs(&mut self) {
        let mut server_inputs = TermSet::new();
        let mut client_inputs = TermSet::new();
        let mut public_inputs = TermSet::new();

        // Parse input parameters from command line as uint32_t variables
        // Initialize shares for each party
        for (t, party) in self.inputs.iter() {
            let name = ToABY::get_var_name(t.clone());
            self.aby.setup.push(format!(
                "uint32_t {} = std::atoi(params[\"{}\"].c_str());",
                name,
                self.parse_var_name(name.to_string())
            ));
            self.aby
                .setup
                .push(format!("share *s_{};", name).to_string());
            let role = party.unwrap_or_else(|| NO_ROLE);
            if role == SERVER {
                server_inputs.insert(t.clone());
            } else if role == CLIENT {
                client_inputs.insert(t.clone());
            } else if role != SERVER && role != CLIENT && self.md.is_input_public(&name) {
                public_inputs.insert(t.clone());
            } else {
                panic!("Unknown role or visibility for variable: {}", name);
            }
        }

        // Initialize public inputs as CONS gateshares
        for t in public_inputs.iter() {
            self.aby.setup.push(self.add_cons_gate(t.clone()));
        }

        // Initialize Server inputs
        self.aby.setup.push("if (role == SERVER) {".to_string());
        for t in server_inputs.iter() {
            self.aby
                .setup
                .push(self.add_in_gate(t.clone(), "SERVER".to_string()));
        }
        for t in client_inputs.iter() {
            self.aby.setup.push(self.add_dummy_gate(t.clone()));
        }
        self.aby.setup.push("}".to_string());

        // Initialize Client inputs
        self.aby.setup.push("if (role == CLIENT) {".to_string());
        for t in client_inputs.iter() {
            self.aby
                .setup
                .push(self.add_in_gate(t.clone(), "CLIENT".to_string()));
        }
        for t in server_inputs.iter() {
            self.aby.setup.push(self.add_dummy_gate(t.clone()));
        }
        self.aby.setup.push("}\n".to_string());
    }

    /// Return constant gate evaluating to 0
    #[allow(dead_code)]
    fn zero() -> &'static str {
        "bcirc->PutCONSGate((uint64_t)0, (uint32_t)1)"
    }

    /// Return constant gate evaluating to 1
    fn one() -> &'static str {
        "bcirc->PutCONSGate((uint64_t)1, (uint32_t)1)"
    }

    fn remove_cons_gate(&self, circ: String) -> String {
        if circ.contains("PutCONSGate(") {
            circ.split("PutCONSGate(")
                .last()
                .unwrap_or("")
                .split(',')
                .next()
                .unwrap_or("")
                .to_string()
        } else {
            panic!("PutCONSGate not found in: {}", circ)
        }
    }

    fn embed_eq(&mut self, t: Term, a: Term, b: Term) -> String {
        let s_circ = self.get_sharetype_circ(t.clone());
        match check(&a) {
            Sort::Bool => {
                let a_circ = self.get_bool(&a);
                let b_circ = self.get_bool(&b);

                let a_conv = self.add_conv_gate(t.clone(), a, a_circ);
                let b_conv = self.add_conv_gate(t.clone(), b, b_circ);

                let s = format!(
                    "{}->PutXORGate({}->PutXORGate({}, {}), {})",
                    s_circ,
                    s_circ,
                    a_conv,
                    b_conv,
                    ToABY::one()
                );
                self.cache.insert(t, EmbeddedTerm::Bool(s.clone()));
                s
            }
            Sort::BitVector(_) => {
                let a_circ = self.get_bv(&a);
                let b_circ = self.get_bv(&b);

                let a_conv = self.add_conv_gate(t.clone(), a, a_circ);
                let b_conv = self.add_conv_gate(t.clone(), b, b_circ);

                let s = format!(
                    "{}->PutXORGate({}->PutXORGate({}->PutGTGate({}, {}), {}->PutGTGate({}, {})), {})",
                    s_circ, s_circ, s_circ, a_conv, b_conv, s_circ, b_conv, a_conv, ToABY::one()
                );
                self.cache.insert(t, EmbeddedTerm::Bool(s.clone()));
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
        let mut s_circ = self.get_sharetype_circ(t.clone());
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                if !self.inputs.contains_key(&t) {
                    self.inputs
                        .insert(t.clone(), *self.md.input_vis.get(name).unwrap());
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
                        "{}->PutCONSGate((uint64_t){}, (uint32_t){})",
                        s_circ, *b as isize, BOOLEAN_BITLEN
                    )),
                );
            }
            Op::Eq => {
                let _s = self.embed_eq(t.clone(), t.cs[0].clone(), t.cs[1].clone());
            }
            Op::Ite => {
                let sel_circ = self.get_bool(&t.cs[0]);
                let a_circ = self.get_bool(&t.cs[1]);
                let b_circ = self.get_bool(&t.cs[2]);

                let sel_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), sel_circ);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[2].clone(), b_circ);

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "{}->PutMUXGate({}, {}, {})",
                        s_circ, a_conv, b_conv, sel_conv
                    )),
                );
            }
            Op::Not => {
                let a_circ = self.get_bool(&t.cs[0]);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "((BooleanCircuit *) {})->PutINVGate({})",
                        s_circ, a_conv
                    )),
                );
            }
            Op::BoolNaryOp(o) => {
                let a_circ = self.get_bool(&t.cs[0]);
                let b_circ = self.get_bool(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                if *o == BoolNaryOp::Or {
                    s_circ = format!("((BooleanCircuit *) {})", s_circ);
                }

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bool(format!(
                        "{}->{}({}, {})",
                        s_circ,
                        match o {
                            BoolNaryOp::Or => "PutORGate",
                            BoolNaryOp::And => "PutANDGate",
                            BoolNaryOp::Xor => "PutXORGate",
                        },
                        a_conv,
                        b_conv
                    )),
                );
            }
            Op::BvBinPred(op) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                match op {
                    BvBinPred::Uge => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "((BooleanCircuit *){})->PutINVGate({}->PutGTGate({}, {}))",
                                s_circ, s_circ, b_conv, a_conv
                            )),
                        );
                    }
                    BvBinPred::Ugt => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "{}->PutGTGate({}, {})",
                                s_circ, a_conv, b_conv
                            )),
                        );
                    }
                    BvBinPred::Ule => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "((BooleanCircuit *){})->PutINVGate({}->PutGTGate({}, {}))",
                                s_circ, s_circ, a_conv, b_conv
                            )),
                        );
                    }
                    BvBinPred::Ult => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bool(format!(
                                "{}->PutGTGate({}, {})",
                                s_circ, b_conv, a_conv
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
        let mut s_circ = self.get_sharetype_circ(t.clone());
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                if !self.inputs.contains_key(&t) {
                    self.inputs
                        .insert(t.clone(), *self.md.input_vis.get(name).unwrap());
                }
                if !self.cache.contains_key(&t) {
                    self.cache
                        .insert(t.clone(), EmbeddedTerm::Bv(format!("s_{}", name)));
                }
            }
            Op::Const(Value::BitVector(b)) => {
                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bv(format!(
                        "{}->PutCONSGate((uint64_t){}, (uint32_t){})",
                        s_circ,
                        format!("{}", b).replace("#", "0"),
                        b.width()
                    )),
                );
            }
            Op::Ite => {
                let sel_circ = self.get_bool(&t.cs[0]);
                let a_circ = self.get_bv(&t.cs[1]);
                let b_circ = self.get_bv(&t.cs[2]);

                let sel_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), sel_circ);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[2].clone(), b_circ);

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bv(format!(
                        "{}->PutMUXGate({}, {}, {})",
                        s_circ, a_conv, b_conv, sel_conv
                    )),
                );
            }
            Op::BvNaryOp(o) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                if *o == BvNaryOp::Or {
                    s_circ = format!("((BooleanCircuit *){})", s_circ);
                }

                self.cache.insert(
                    t.clone(),
                    EmbeddedTerm::Bv(format!(
                        "{}->{}({}, {})",
                        s_circ,
                        match o {
                            BvNaryOp::Xor => "PutXORGate",
                            BvNaryOp::Or => "PutORGate",
                            BvNaryOp::And => "PutANDGate",
                            BvNaryOp::Add => "PutADDGate",
                            BvNaryOp::Mul => "PutMULGate",
                        },
                        a_conv,
                        b_conv
                    )),
                );
            }
            Op::BvBinOp(o) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                match o {
                    BvBinOp::Sub => {
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!(
                                "{}->PutSUBGate({}, {})",
                                s_circ, a_conv, b_conv
                            )),
                        );
                    }
                    BvBinOp::Shl => {
                        let b_val = self.remove_cons_gate(b_conv);
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!(
                                "left_shift({}, {}, {})",
                                s_circ, a_conv, b_val
                            )),
                        );
                    }
                    BvBinOp::Lshr => {
                        let b_val = self.remove_cons_gate(b_conv);
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!(
                                "logical_right_shift({}, {}, {})",
                                s_circ, a_conv, b_val
                            )),
                        );
                    }
                    BvBinOp::Ashr => {
                        let b_val = self.remove_cons_gate(b_conv);
                        self.cache.insert(
                            t.clone(),
                            EmbeddedTerm::Bv(format!(
                                "arithmetic_right_shift({}, {}, {})",
                                s_circ, a_conv, b_val
                            )),
                        );
                    }
                    _ => panic!("Invalid bv-op in BvBinOp: {:?}", o),
                }
            }
            Op::BvExtract(_start, _end) => {}
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }

        self.get_bv(&t)
    }

    /// Given a Circuit `circ`, wrap `circ` in an OUT gate to extract the value of
    /// the circuit to a share      
    ///
    /// Return a String of the resulting Circuit
    fn format_output_circuit(&self, t: Term, circ: String) -> String {
        format!(
            "\tadd_to_output_queue(out_q, {}->PutOUTGate({}, ALL), role, std::cout);\n",
            self.get_sharetype_circ(t),
            circ
        )
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
        self.format_output_circuit(t, circ)
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self, t: Term) {
        let circ = self.embed(t);
        self.aby.circs.push(circ);
    }
}

/// Convert this (IR) `ir` to ABY.
pub fn to_aby(ir: Computation) -> ABY {
    let Computation {
        outputs: terms,
        metadata: md,
        values: _,
    } = ir.clone();
    // let s_map: SharingMap = assign(&ir);
    let s_map: SharingMap = some_arith_sharing(&ir);
    let mut converter = ToABY::new(md, s_map);

    for t in terms {
        println!("Terms: {}", t);
        converter.lower(t.clone());
    }

    // Iterating and lowering the terms populates self.inputs, which
    // are the input parameters for the ABY circuit.
    // Call init_inputs here after self.inputs is populated.
    converter.init_inputs();

    converter.aby
}
