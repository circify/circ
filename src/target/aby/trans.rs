//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use crate::ir::term::*;
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::{ShareType, SharingMap};
use crate::target::aby::utils::*;
use std::fmt;

use std::path::Path;

const NO_ROLE: u8 = u8::MAX;
const SERVER: u8 = 0;
const CLIENT: u8 = 1;
const BOOLEAN_BITLEN: i32 = 1;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool(String),
    Bv(String),
}

impl fmt::Display for EmbeddedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self)
    }
}

struct ToABY {
    md: ComputationMetadata,
    inputs: TermMap<Option<PartyId>>,
    cache: TermMap<EmbeddedTerm>,
    s_map: SharingMap,
    share_cnt: i32,
    setup_fname: String,
    circuit_fname: String,
}

impl ToABY {
    fn new(metadata: ComputationMetadata, s_map: SharingMap, path: &Path, lang: &str) -> Self {
        Self {
            md: metadata,
            inputs: TermMap::new(),
            cache: TermMap::new(),
            s_map,
            share_cnt: 0,
            setup_fname: get_path(path, lang, &String::from("setup")),
            circuit_fname: get_path(path, lang, &String::from("circuit")),
        }
    }

    fn get_var_name(t: Term, b: bool) -> String {
        match &t.op {
            Op::Var(name, _) => {
                if b {
                    name.to_string().replace(".", "_")
                } else {
                    name.to_string()
                }
            }
            _ => panic!("Term {} is not of type Var", t),
        }
    }

    fn get_share_name(&mut self) -> String {
        format!("s_{}", self.share_cnt)
    }

    fn inc_share(&mut self) {
        self.share_cnt += 1;
    }

    /// Parse variable name from IR representation of a variable
    fn parse_var_name(&self, full_name: String) -> String {
        let parsed: Vec<String> = full_name.split('_').map(str::to_string).collect();
        if parsed.len() < 2 {
            panic!("Invalid variable name: {}", full_name);
        }
        let mut name = parsed[parsed.len() - 2].to_string();
        if full_name.contains('.') {
            let index: Vec<String> = full_name.split('.').map(str::to_string).collect();
            if index.is_empty() {
                panic!("Invalid variable name: {}", full_name);
            }
            name += &("_".to_owned() + &index[index.len() - 1].to_string());
        }
        name
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
        let name = ToABY::get_var_name(t.clone(), true);
        let s_circ = self.get_sharetype_circ(t);
        format!(
            "s_{} = {}->PutCONSGate((uint32_t){}, bitlen);\n",
            name, s_circ, name
        )
    }

    fn add_in_gate(&self, t: Term, role: String) -> String {
        let name = ToABY::get_var_name(t.clone(), true);
        let s_circ = self.get_sharetype_circ(t);
        format!(
            "\ts_{} = {}->PutINGate({}, bitlen, {});\n",
            name, s_circ, name, role
        )
    }

    fn add_dummy_gate(&self, t: Term) -> String {
        let name = ToABY::get_var_name(t.clone(), true);
        let s_circ = self.get_sharetype_circ(t);
        format!("\ts_{} = {}->PutDummyINGate(bitlen);\n", name, s_circ)
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
            let name = ToABY::get_var_name(t.clone(), false);
            let name_ = ToABY::get_var_name(t.clone(), true);

            write_line_to_file(
                &self.setup_fname,
                &format!(
                    "uint32_t {} = std::atoi(params[\"{}\"].c_str());\n",
                    name_,
                    self.parse_var_name(name.to_string())
                ),
            );

            write_line_to_file(
                &self.setup_fname,
                &format!("share* s_{};\n", name_).to_string(),
            );

            let role = party.unwrap_or_else(|| NO_ROLE);
            if role == SERVER {
                server_inputs.insert(t.clone());
            } else if role == CLIENT {
                client_inputs.insert(t.clone());
            } else if role != SERVER && role != CLIENT && self.md.is_input_public(&name_) {
                public_inputs.insert(t.clone());
            } else {
                panic!("Unknown role or visibility for variable: {}", name);
            }
        }

        // Initialize public inputs as CONS gateshares
        for t in public_inputs.iter() {
            write_line_to_file(&self.setup_fname, &self.add_cons_gate(t.clone()));
        }

        // Initialize Server inputs
        write_line_to_file(&self.setup_fname, &String::from("if (role == SERVER) {\n"));
        // TODO: add in gates based on type / number of inputs
        for t in server_inputs.iter() {
            write_line_to_file(
                &self.setup_fname,
                &self.add_in_gate(t.clone(), "SERVER".to_string()),
            );
        }
        for t in client_inputs.iter() {
            write_line_to_file(&self.setup_fname, &self.add_dummy_gate(t.clone()));
        }
        write_line_to_file(&self.setup_fname, &String::from("}\n"));

        // Initialize Client inputs
        write_line_to_file(&self.setup_fname, &String::from("if (role == CLIENT) {\n"));
        for t in client_inputs.iter() {
            write_line_to_file(
                &self.setup_fname,
                &self.add_in_gate(t.clone(), "CLIENT".to_string()),
            );
        }
        for t in server_inputs.iter() {
            write_line_to_file(&self.setup_fname, &self.add_dummy_gate(t.clone()));
        }
        write_line_to_file(&self.setup_fname, &String::from("}\n"));
    }

    /// Return constant gate evaluating to 0
    // TODO: const should not be hardcoded to acirc
    #[allow(dead_code)]
    fn zero() -> String {
        "acirc->PutCONSGate((uint64_t)0, (uint32_t)1)".to_string()
    }

    /// Return constant gate evaluating to 1
    fn one(s_type: &str) -> String {
        format!("{}->PutCONSGate((uint64_t)1, (uint32_t)1)", s_type)
    }

    fn embed_eq(&mut self, t: Term, a: Term, b: Term) {
        let s_circ = self.get_sharetype_circ(t.clone());
        match check(&a) {
            Sort::Bool => {
                let a_circ = self.get_bool(&a);
                let b_circ = self.get_bool(&b);

                let a_conv = self.add_conv_gate(t.clone(), a, a_circ);
                let b_conv = self.add_conv_gate(t.clone(), b, b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutXORGate({}->PutXORGate({}, {}), {});\n",
                    share,
                    s_circ,
                    s_circ,
                    a_conv,
                    b_conv,
                    ToABY::one(&s_circ)
                );
                write_line_to_file(&self.circuit_fname, &s);

                self.cache.insert(t, EmbeddedTerm::Bool(share));
            }
            Sort::BitVector(_) => {
                let a_circ = self.get_bv(&a);
                let b_circ = self.get_bv(&b);

                let a_conv = self.add_conv_gate(t.clone(), a, a_circ);
                let b_conv = self.add_conv_gate(t.clone(), b, b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutXORGate({}->PutXORGate({}->PutGTGate({}, {}), {}->PutGTGate({}, {})), {});\n",
                    share, s_circ, s_circ, s_circ, a_conv, b_conv, s_circ, b_conv, a_conv, ToABY::one(&s_circ)
                );
                write_line_to_file(&self.circuit_fname, &s);
                self.cache.insert(t, EmbeddedTerm::Bool(share));
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
                    self.cache.insert(
                        t.clone(),
                        EmbeddedTerm::Bool(format!("s_{}", name.replace(".", "_"))),
                    );
                }
            }
            Op::Const(Value::Bool(b)) => {
                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutCONSGate((uint64_t){}, (uint32_t){});\n",
                    share, s_circ, *b as isize, BOOLEAN_BITLEN
                );
                write_line_to_file(&self.circuit_fname, &s);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::Eq => {
                self.embed_eq(t.clone(), t.cs[0].clone(), t.cs[1].clone());
            }
            Op::Ite => {
                let sel_circ = self.get_bool(&t.cs[0]);
                let a_circ = self.get_bool(&t.cs[1]);
                let b_circ = self.get_bool(&t.cs[2]);

                let sel_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), sel_circ);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[2].clone(), b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutMUXGate({}, {}, {});\n",
                    share, s_circ, a_conv, b_conv, sel_conv
                );
                write_line_to_file(&self.circuit_fname, &s);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::Not => {
                let a_circ = self.get_bool(&t.cs[0]);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = ((BooleanCircuit *) {})->PutINVGate({});\n",
                    share, s_circ, a_conv
                );
                write_line_to_file(&self.circuit_fname, &s);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::BoolNaryOp(o) => {
                if t.cs.len() == 1 {
                    // HACK: Conditionals might not contain two variables
                    // If t.cs len is 1, just output that term
                    // This is to bypass adding an AND gate with a single conditional term
                    // Refer to pub fn condition() in src/circify/mod.rs
                    let a = self.get_bool(&t.cs[0]);
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool(a));
                } else {
                    let a_circ = self.get_bool(&t.cs[0]);
                    let b_circ = self.get_bool(&t.cs[1]);

                    let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                    let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                    if *o == BoolNaryOp::Or {
                        s_circ = format!("((BooleanCircuit *) {})", s_circ);
                    }

                    let share = self.get_share_name();
                    self.inc_share();
                    let s = format!(
                        "share* {} = {}->{}({}, {});\n",
                        share,
                        s_circ,
                        match o {
                            BoolNaryOp::Or => "PutORGate",
                            BoolNaryOp::And => "PutANDGate",
                            BoolNaryOp::Xor => "PutXORGate",
                        },
                        a_conv,
                        b_conv
                    );
                    write_line_to_file(&self.circuit_fname, &s);
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
                }
            }
            Op::BvBinPred(op) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = match op {
                    BvBinPred::Ugt => {
                        format!(
                            "share* {} = {}->PutGTGate({}, {});\n",
                            share, s_circ, a_conv, b_conv
                        )
                    }
                    BvBinPred::Ult => {
                        format!(
                            "share* {} = {}->PutGTGate({}, {});\n",
                            share, s_circ, b_conv, a_conv
                        )
                    }
                    BvBinPred::Uge => {
                        format!(
                            "share* {} = ((BooleanCircuit *){})->PutINVGate({}->PutGTGate({}, {}));\n",
                            share, s_circ, s_circ, b_conv, a_conv
                        )
                    }
                    BvBinPred::Ule => {
                        format!(
                            "share* {} = ((BooleanCircuit *){})->PutINVGate({}->PutGTGate({}, {}));\n",
                            share, s_circ, s_circ, a_conv, b_conv
                        )
                    }
                    _ => panic!("Non-field in bool BvBinPred: {}", op),
                };
                write_line_to_file(&self.circuit_fname, &s);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
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
                    self.cache.insert(
                        t.clone(),
                        EmbeddedTerm::Bv(format!("s_{}", name.replace(".", "_"))),
                    );
                }
            }
            Op::Const(Value::BitVector(b)) => {
                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutCONSGate((uint64_t){}, (uint32_t){});\n",
                    share,
                    s_circ,
                    format!("{}", b).replace("#", "0"),
                    b.width()
                );
                write_line_to_file(&self.circuit_fname, &s);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::Ite => {
                let sel_circ = self.get_bool(&t.cs[0]);
                let a_circ = self.get_bv(&t.cs[1]);
                let b_circ = self.get_bv(&t.cs[2]);

                let sel_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), sel_circ);
                let a_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[2].clone(), b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->PutMUXGate({}, {}, {});\n",
                    share, s_circ, a_conv, b_conv, sel_conv
                );
                write_line_to_file(&self.circuit_fname, &s);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::BvNaryOp(o) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                if *o == BvNaryOp::Or {
                    s_circ = format!("((BooleanCircuit *){})", s_circ);
                }

                let share = self.get_share_name();
                self.inc_share();
                let s = format!(
                    "share* {} = {}->{}({}, {});\n",
                    share,
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
                );
                write_line_to_file(&self.circuit_fname, &s);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::BvBinOp(o) => {
                let a_circ = self.get_bv(&t.cs[0]);
                let b_circ = self.get_bv(&t.cs[1]);

                let a_conv = self.add_conv_gate(t.clone(), t.cs[0].clone(), a_circ);
                let b_conv = self.add_conv_gate(t.clone(), t.cs[1].clone(), b_circ);

                let share = self.get_share_name();
                self.inc_share();
                let s = match o {
                    BvBinOp::Sub => {
                        format!(
                            "share* {} = {}->PutSUBGate({}, {});\n",
                            share, s_circ, a_conv, b_conv
                        )
                    }
                    _ => {
                        format!(
                            "share* {} = {}({}, {}, {});\n",
                            share,
                            match o {
                                BvBinOp::Udiv => "signeddivbl",
                                BvBinOp::Urem => "signedmodbl",
                                BvBinOp::Shl => "left_shift",
                                BvBinOp::Lshr => "logical_right_shift",
                                BvBinOp::Ashr => "arithmetic_right_shift",
                                _ => unreachable!(),
                            },
                            s_circ,
                            a_conv,
                            b_conv,
                        )
                    }
                };
                write_line_to_file(&self.circuit_fname, &s);
                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            // TODO
            Op::BvExtract(_start, _end) => {}
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }

        self.get_bv(&t)
    }

    /// Given a Circuit `circ`, wrap `circ` in an OUT gate to extract the value of
    /// the circuit to a share      
    ///
    /// Return a String of the resulting Circuit
    fn format_output_circuit(&self, t: Term) -> String {
        match self.cache.get(&t) {
            Some(EmbeddedTerm::Bool(s)) | Some(EmbeddedTerm::Bv(s)) => {
                format!(
                    "add_to_output_queue(out_q, {}->PutOUTGate({}, ALL), role, std::cout);\n",
                    self.get_sharetype_circ(t),
                    s
                )
            }
            None => panic!("Term not found in cache: {:#?}", t),
        }
    }

    fn embed(&mut self, t: Term) -> String {
        for c in PostOrderIter::new(t.clone()) {
            match check(&c) {
                Sort::Bool => {
                    self.embed_bool(c);
                }
                Sort::BitVector(_) => {
                    self.embed_bv(c);
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }
        }
        self.format_output_circuit(t)
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self, t: Term) {
        let s = self.embed(t);
        write_line_to_file(&self.circuit_fname, &s);
    }
}

/// Convert this (IR) `ir` to ABY.
pub fn to_aby(ir: Computation, path: &Path, lang: &str, cm: &str) {
    let Computation {
        outputs: terms,
        metadata: md,
        values: _,
    } = ir.clone();
    for t in terms.clone() {
        println!("terms: {}", t);
    }

    let s_map: SharingMap = assign(&ir, cm);
    // let s_map: SharingMap = some_arith_sharing(&ir);
    let mut converter = ToABY::new(md, s_map, path, lang);

    for t in terms {
        println!("terms: {}", t);
        converter.lower(t.clone());
    }

    // Iterating and lowering the terms populates self.inputs, which
    // are the input parameters for the ABY circuit.
    // Call init_inputs here after self.inputs is populated.
    converter.init_inputs();
}
