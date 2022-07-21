//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/&blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use rug::Integer;

use crate::ir::opt::cfold::fold;
use crate::ir::term::*;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::SharingMap;
use crate::target::aby::utils::*;
use std::collections::HashMap;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;
use std::time::Instant;

use crate::target::graph::trans::inline_all_and_assign_glp;

use super::assignment::assign_all_boolean;
use super::assignment::assign_all_yao;
use super::assignment::assign_arithmetic_and_boolean;
use super::assignment::assign_arithmetic_and_yao;
use super::assignment::assign_greedy;

const PUBLIC: u8 = 2;
const WRITE_SIZE: usize = 65536;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool,
    Bv,
    Array,
    Tuple,
}

impl fmt::Display for EmbeddedTerm {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            EmbeddedTerm::Bool => {
                write!(f, "bool")
            }
            EmbeddedTerm::Bv => {
                write!(f, "bv")
            }
            EmbeddedTerm::Array => {
                write!(f, "array")
            }
            EmbeddedTerm::Tuple => {
                write!(f, "tuple")
            }
        }
    }
}

static mut dur_const_arr: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_const_arr: usize = 0;

static mut dur_const_tuple: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_const_tuple: usize = 0;

static mut dur_ite: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_ite: usize = 0;

static mut dur_store: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_store: usize = 0;

static mut dur_field: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_field: usize = 0;

static mut dur_update: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_update: usize = 0;

static mut dur_tuple: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_tuple: usize = 0;

static mut dur_call: std::time::Duration = std::time::Duration::new(0, 0);
static mut num_call: usize = 0;

struct ToABY<'a> {
    fs: Functions,
    s_map: HashMap<String, SharingMap>,
    path: &'a Path,
    lang: String,
    curr_comp: String,
    // Input mapping
    inputs: Vec<Term>,
    // Term cache
    cache: TermMap<EmbeddedTerm>,
    // Term to share id
    term_to_shares: TermMap<Vec<i32>>,
    share_cnt: i32,
    // Outputs
    bytecode_input: Vec<String>,
    bytecode_output: Vec<String>,
    const_output: Vec<String>,
    share_output: Vec<String>,
}

impl Drop for ToABY<'_> {
    fn drop(&mut self) {
        // use std::mem::take;
        // drop everything that uses a Term
        // drop(take(&mut self.md));
        self.inputs.clear();
        self.cache.clear();
        self.term_to_shares.clear();
        // self.s_map.clear();
        // clean up
        garbage_collect();
    }
}

impl<'a> ToABY<'a> {
    fn new(fs: Functions, s_map: HashMap<String, SharingMap>, path: &'a Path, lang: &str) -> Self {
        Self {
            fs,
            s_map,
            path,
            lang: lang.to_string(),
            curr_comp: "".to_string(),
            inputs: Vec::new(),
            cache: TermMap::new(),
            term_to_shares: TermMap::new(),
            share_cnt: 0,
            bytecode_input: Vec::new(),
            bytecode_output: Vec::new(),
            const_output: Vec::new(),
            share_output: Vec::new(),
        }
    }

    fn write_const_output(&mut self, flush: bool) {
        if flush || self.const_output.len() >= WRITE_SIZE {
            let const_output_path = get_path(self.path, &self.lang, "const", false);
            write_lines(&const_output_path, &self.const_output);
            self.const_output.clear();
        }
    }

    fn write_bytecode_output(&mut self, flush: bool) {
        if flush || self.bytecode_output.len() >= WRITE_SIZE {
            let bytecode_output_path = get_path(
                self.path,
                &self.lang,
                &format!("{}_bytecode_output", self.curr_comp),
                false,
            );
            write_lines(&bytecode_output_path, &self.bytecode_output);
            self.bytecode_output.clear();
        }
    }

    fn write_share_output(&mut self, flush: bool) {
        if flush || self.share_output.len() >= WRITE_SIZE {
            let share_output_path = get_path(self.path, &self.lang, "share_map", false);
            write_lines(&share_output_path, &self.share_output);
            self.share_output.clear();
        }
    }

    fn shares_to_string(&self, shares: Vec<i32>) -> String {
        shares
            .iter()
            .map(|&i| i.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    fn get_md(&self) -> ComputationMetadata {
        self.fs
            .computations
            .get(&self.curr_comp)
            .unwrap()
            .metadata
            .clone()
    }

    fn get_var_name(name: &String) -> String {
        let new_name = name.to_string().replace('.', "_");
        let n = new_name.split('_').collect::<Vec<&str>>();
        let offset = n.iter().position(|&r| r == "lex0").unwrap();

        let var_name = &n[offset + 1..];

        match var_name.len() {
            2 => var_name[0].to_string(),
            3.. => {
                let l = var_name.len();
                format!(
                    "{}_{}",
                    &var_name[0..l - 2].to_vec().join("_"),
                    var_name[l - 1]
                )
            }
            _ => {
                panic!("Invalid variable name: {}", name);
            }
        }
    }

    fn get_var_name_from_term(t: &Term) -> String {
        match &t.op {
            Op::Var(name, _) => ToABY::get_var_name(name),
            _ => panic!("Term {} is not of type Var", t),
        }
    }

    fn get_sharing_map(&mut self, name: &str) -> SharingMap {
        match self.s_map.get(name) {
            Some(s) => s.clone(),
            None => panic!("Unknown sharing map for function: {}", name),
        }
    }

    fn write_share(&mut self, t: &Term, s: i32) {
        let s_map = self.s_map.get(&self.curr_comp).unwrap();
        let share_type = s_map.get(&t).unwrap().char();
        let line = format!("{} {}\n", s, share_type);
        self.share_output.push(line);
    }

    fn write_shares(&mut self, t: &Term, shares: &Vec<i32>) {
        let s_map = self.s_map.get(&self.curr_comp).unwrap();
        let share_type = s_map.get(&t).unwrap().char();
        for s in shares {
            let line = format!("{} {}\n", s, share_type);
            self.share_output.push(line);
        }
    }

    // TODO: Rust ENTRY api on maps
    fn get_share(&mut self, t: &Term) -> i32 {
        match self.term_to_shares.get(t) {
            Some(v) => {
                assert!(v.len() == 1);
                v[0]
            }
            None => {
                let s = self.share_cnt;
                self.term_to_shares.insert(t.clone(), [s].to_vec());
                self.share_cnt += 1;

                // Write share
                self.write_share(t, s);

                s
            }
        }
    }

    fn get_shares(&mut self, t: &Term) -> Vec<i32> {
        match self.term_to_shares.get(t) {
            Some(v) => v.clone(),
            None => {
                let sort = check(t);
                let num_shares = self.get_sort_len(&sort) as i32;

                let shares: Vec<i32> = (0..num_shares)
                    .map(|x| x + self.share_cnt)
                    .collect::<Vec<i32>>();
                self.term_to_shares.insert(t.clone(), shares.clone());

                // Write shares
                self.write_shares(t, &shares);

                self.share_cnt += num_shares;

                shares
            }
        }
    }

    fn rewirable(&self, s: &Sort) -> bool {
        match s {
            Sort::Array(..) => true,
            Sort::Bool | Sort::BitVector(..) | Sort::Tuple(..) => false,
            _ => todo!(),
        }
    }

    fn get_sort_len(&mut self, s: &Sort) -> usize {
        let mut len = 0;
        len += match s {
            Sort::Bool => 1,
            Sort::BitVector(_) => 1,
            Sort::Array(_, _, n) => *n,
            Sort::Tuple(sorts) => {
                let mut inner_len = 0;
                for inner_s in sorts.iter() {
                    inner_len += self.get_sort_len(inner_s);
                }
                inner_len
            }
            _ => panic!("Sort is not supported: {:#?}", s),
        };
        len
    }

    fn unwrap_vis(&self, name: &str) -> u8 {
        let md = self.get_md();
        match md.get_input_visibility(name) {
            Some(role) => role,
            None => PUBLIC,
        }
    }

    fn embed_eq(&mut self, t: Term, a_term: Term, b_term: Term) {
        let s = self.get_share(&t);
        let a = self.get_share(&t.cs[0]);
        let b = self.get_share(&t.cs[1]);
        let op = "EQ";
        let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
        self.bytecode_output.push(line);
        match check(&a_term) {
            Sort::Bool => {
                self.check_bool(&a_term);
                self.check_bool(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool);
            }
            Sort::BitVector(_) => {
                self.check_bv(&a_term);
                self.check_bv(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool);
            }
            e => panic!("Unimplemented sort for Eq: {:?}", e),
        }
    }

    /// Given term `t`, type-check `t` is of type Bool
    fn check_bool(&self, t: &Term) {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bool => (),
            _ => panic!("Non-bool for {:?}", t),
        }
    }

    fn embed_bool(&mut self, t: Term) {
        let s = self.get_share(&t);
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.input_vis.contains_key(name) {
                    let term_name = ToABY::get_var_name_from_term(&t);
                    let vis = self.unwrap_vis(name);
                    let s = self.get_share(&t);
                    let op = "IN";

                    if vis == PUBLIC {
                        let bitlen = 1;
                        let line = format!("3 1 {} {} {} {} {}\n", term_name, vis, bitlen, s, op);
                        self.bytecode_input.push(line);
                    } else {
                        let line = format!("2 1 {} {} {} {}\n", term_name, vis, s, op);
                        self.bytecode_input.push(line);
                    }
                    self.inputs.push(t.clone());
                }

                if !self.cache.contains_key(&t) {
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool);
                }
            }
            Op::Const(Value::Bool(b)) => {
                let op = "CONS_bool";
                let line = format!("1 1 {} {} {}\n", *b as i32, s, op);
                self.const_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            Op::Eq => {
                self.embed_eq(t.clone(), t.cs[0].clone(), t.cs[1].clone());
            }
            Op::Ite => {
                let op = "MUX";

                self.check_bool(&t.cs[0]);
                self.check_bool(&t.cs[1]);
                self.check_bool(&t.cs[2]);

                let sel = self.get_share(&t.cs[0]);
                let a = self.get_share(&t.cs[1]);
                let b = self.get_share(&t.cs[2]);

                let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            Op::Not => {
                let op = "NOT";

                self.check_bool(&t.cs[0]);

                let a = self.get_share(&t.cs[0]);
                let line = format!("1 1 {} {} {}\n", a, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            Op::BoolNaryOp(o) => {
                if t.cs.len() == 1 {
                    // HACK: Conditionals might not contain two variables
                    // If t.cs len is 1, just output that term
                    // This is to bypass adding an AND gate with a single conditional term
                    // Refer to pub fn condition() in src/circify/mod.rs
                    self.check_bool(&t.cs[0]);
                    let a = self.get_share(&t.cs[0]);
                    match o {
                        BoolNaryOp::And => self.term_to_shares.insert(t.clone(), vec![a]),
                        _ => {
                            unimplemented!("Single operand boolean operation");
                        }
                    };
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool);
                } else {
                    self.check_bool(&t.cs[0]);
                    self.check_bool(&t.cs[1]);

                    let op = match o {
                        BoolNaryOp::Or => "OR",
                        BoolNaryOp::And => "AND",
                        BoolNaryOp::Xor => "XOR",
                    };

                    let a = self.get_share(&t.cs[0]);
                    let b = self.get_share(&t.cs[1]);
                    let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                    self.bytecode_output.push(line);

                    self.cache.insert(t.clone(), EmbeddedTerm::Bool);
                }
            }
            Op::BvBinPred(o) => {
                let op = match o {
                    BvBinPred::Ugt => "GT",
                    BvBinPred::Ult => "LT",
                    BvBinPred::Uge => "GE",
                    BvBinPred::Ule => "LE",
                    _ => panic!("Non-field in bool BvBinPred: {}", o),
                };

                self.check_bv(&t.cs[0]);
                self.check_bv(&t.cs[1]);

                let a = self.get_share(&t.cs[0]);
                let b = self.get_share(&t.cs[1]);
                let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            _ => panic!("Non-field in embed_bool: {}", t),
        }
    }

    /// Given term `t`, type-check `t` is of type Bv
    fn check_bv(&self, t: &Term) {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t))
        {
            EmbeddedTerm::Bv => (),
            _ => panic!("Non-bv for {:?}", t),
        }
    }

    fn embed_bv(&mut self, t: Term) {
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.input_vis.contains_key(name) {
                    let term_name = ToABY::get_var_name_from_term(&t);
                    let vis = self.unwrap_vis(name);
                    let s = self.get_share(&t);
                    let op = "IN";

                    if vis == PUBLIC {
                        let bitlen = 32;
                        let line = format!("3 1 {} {} {} {} {}\n", term_name, vis, bitlen, s, op);
                        self.bytecode_input.push(line);
                    } else {
                        let line = format!("2 1 {} {} {} {}\n", term_name, vis, s, op);
                        self.bytecode_input.push(line);
                    }
                    self.inputs.push(t.clone());
                }

                if !self.cache.contains_key(&t) {
                    self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                }
            }
            Op::Const(Value::BitVector(b)) => {
                let s = self.get_share(&t);
                let op = "CONS_bv";
                let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                self.const_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::Ite => {
                let s = self.get_share(&t);
                let op = "MUX";

                self.check_bool(&t.cs[0]);
                self.check_bv(&t.cs[1]);
                self.check_bv(&t.cs[2]);

                let sel = self.get_share(&t.cs[0]);
                let a = self.get_share(&t.cs[1]);
                let b = self.get_share(&t.cs[2]);

                let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::BvNaryOp(o) => {
                let s = self.get_share(&t);
                let op = match o {
                    BvNaryOp::Xor => "XOR",
                    BvNaryOp::Or => "OR",
                    BvNaryOp::And => "AND",
                    BvNaryOp::Add => "ADD",
                    BvNaryOp::Mul => "MUL",
                };

                self.check_bv(&t.cs[0]);
                self.check_bv(&t.cs[1]);

                let a = self.get_share(&t.cs[0]);
                let b = self.get_share(&t.cs[1]);

                let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::BvBinOp(o) => {
                let s = self.get_share(&t);
                let op = match o {
                    BvBinOp::Sub => "SUB",
                    BvBinOp::Udiv => "DIV",
                    BvBinOp::Urem => "REM",
                    BvBinOp::Shl => "SHL",
                    BvBinOp::Lshr => "LSHR",
                    _ => panic!("Binop not supported: {}", o),
                };

                match o {
                    BvBinOp::Sub | BvBinOp::Udiv | BvBinOp::Urem => {
                        self.check_bv(&t.cs[0]);
                        self.check_bv(&t.cs[1]);

                        let a = self.get_share(&t.cs[0]);
                        let b = self.get_share(&t.cs[1]);

                        let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                        self.bytecode_output.push(line);

                        self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                    }
                    BvBinOp::Shl | BvBinOp::Lshr => {
                        self.check_bv(&t.cs[0]);
                        self.check_bv(&t.cs[1]);

                        let a = self.get_share(&t.cs[0]);
                        let const_shift_amount_term = fold(&t.cs[1], &[]);
                        let const_shift_amount =
                            const_shift_amount_term.as_bv_opt().unwrap().uint();

                        let line = format!("2 1 {} {} {} {}\n", a, const_shift_amount, s, op);
                        self.bytecode_output.push(line);

                        self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                    }
                    _ => panic!("Binop not supported: {}", o),
                };
            }
            Op::Field(i) => {
                assert!(t.cs.len() == 1);
                let shares = self.get_shares(&t.cs[0]);
                assert!(*i < shares.len());
                self.term_to_shares.insert(t.clone(), vec![shares[*i]]);
                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::Select => {
                assert!(t.cs.len() == 2);
                let array_shares = self.get_shares(&t.cs[0]);

                if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                    let idx = bv.uint().to_usize().unwrap().clone();
                    assert!(
                        idx < array_shares.len(),
                        "idx: {}, shares: {}",
                        idx,
                        array_shares.len()
                    );

                    self.term_to_shares
                        .insert(t.clone(), vec![array_shares[idx]]);
                    self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                } else {
                    let op = "SELECT";
                    let num_inputs = array_shares.len() + 1;
                    let index_share = self.get_share(&t.cs[1]);
                    let output = self.get_share(&t);
                    let line = format!(
                        "{} 1 {} {} {} {}\n",
                        num_inputs,
                        self.shares_to_string(array_shares),
                        index_share,
                        output,
                        op
                    );
                    self.bytecode_output.push(line);
                    self.term_to_shares.insert(t.clone(), vec![output]);
                    self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                }
            }
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }
    }

    fn embed_scalar(&mut self, t: Term) {
        let now = Instant::now();
        match &t.op {
            Op::Const(Value::Array(arr)) => {
                let shares = self.get_shares(&t);
                assert!(shares.len() == arr.size);

                for (i, s) in shares.iter().enumerate() {
                    // TODO: sort of index might not be a 32-bit bitvector
                    let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                    let v = match arr.map.get(&idx) {
                        Some(c) => c,

                        None => &*arr.default,
                    };

                    match v {
                        Value::BitVector(b) => {
                            let op = "CONS_bv";
                            let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                            self.const_output.push(line);
                            self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                        }
                        _ => todo!(),
                    }
                }

                unsafe {
                    num_const_arr += 1;
                    dur_const_arr += now.elapsed();
                };
            }
            Op::Const(Value::Tuple(tup)) => {
                let shares = self.get_shares(&t);
                assert!(shares.len() == tup.len());
                for (val, s) in tup.iter().zip(shares.iter()) {
                    match val {
                        Value::BitVector(b) => {
                            let op = "CONS_bv";
                            let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                            self.const_output.push(line);
                            self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                        }
                        _ => todo!(),
                    }
                }

                unsafe {
                    num_const_tuple += 1;
                    dur_const_tuple += now.elapsed();
                };
            }
            Op::Ite => {
                let op = "MUX";
                let shares = self.get_shares(&t);

                let sel = self.get_share(&t.cs[0]);
                let a = self.get_shares(&t.cs[1]);
                let b = self.get_shares(&t.cs[2]);

                // assert scalar_term share lens are equivalent
                assert!(shares.len() == a.len());
                assert!(shares.len() == b.len());

                let num_inputs = 1 + shares.len() * 2;
                let num_outputs = shares.len();

                let line = format!(
                    "{} {} {} {} {} {} {}\n",
                    num_inputs,
                    num_outputs,
                    sel,
                    self.shares_to_string(a),
                    self.shares_to_string(b),
                    self.shares_to_string(shares),
                    op
                );

                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Array);

                unsafe {
                    num_ite += 1;
                    dur_ite += now.elapsed();
                };
            }
            Op::Store => {
                assert!(t.cs.len() == 3);
                let mut array_shares = self.get_shares(&t.cs[0]).clone();
                let value_share = self.get_share(&t.cs[2]);

                if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                    // constant indexing
                    let idx = bv.uint().to_usize().unwrap().clone();

                    array_shares[idx] = value_share;

                    self.term_to_shares.insert(t.clone(), array_shares.clone());
                    self.cache.insert(t.clone(), EmbeddedTerm::Array);
                } else {
                    let op = "STORE";
                    let num_inputs = array_shares.len() + 2;
                    let outputs = self.get_shares(&t);
                    let num_outputs = outputs.len();
                    let index_share = self.get_share(&t.cs[1]);
                    let line = format!(
                        "{} {} {} {} {} {} {}\n",
                        num_inputs,
                        num_outputs,
                        self.shares_to_string(array_shares),
                        index_share,
                        value_share,
                        self.shares_to_string(outputs),
                        op
                    );

                    self.bytecode_output.push(line);
                }

                unsafe {
                    num_store += 1;
                    dur_store += now.elapsed();
                };
            }
            Op::Field(i) => {
                assert!(t.cs.len() == 1);
                let shares = self.get_shares(&t.cs[0]);
                let tuple_sort = check(&t.cs[0]);
                let (offset, len) = match tuple_sort {
                    Sort::Tuple(t) => {
                        assert!(*i < t.len());

                        // find offset
                        let mut offset = 0;
                        for j in 0..*i {
                            offset += self.get_sort_len(&t[j]);
                        }

                        // find len
                        let len = self.get_sort_len(&t[*i]);

                        (offset, len)
                    }
                    _ => panic!("Field op on non-tuple"),
                };

                // get ret slice
                let field_shares = &shares[offset..offset + len];

                self.term_to_shares.insert(t.clone(), field_shares.to_vec());
                self.cache.insert(t.clone(), EmbeddedTerm::Array);

                unsafe {
                    num_field += 1;
                    dur_field += now.elapsed();
                };
            }
            Op::Update(i) => {
                assert!(t.cs.len() == 2);
                let mut tuple_shares = self.get_shares(&t.cs[0]);
                let value_share = self.get_share(&t.cs[1]);

                // assert the index is in bounds
                assert!(*i < tuple_shares.len());

                // update shares in tuple
                tuple_shares[*i] = value_share;

                // store shares
                self.term_to_shares.insert(t.clone(), tuple_shares);
                self.cache.insert(t.clone(), EmbeddedTerm::Tuple);

                unsafe {
                    num_update += 1;
                    dur_update += now.elapsed();
                };
            }
            Op::Tuple => {
                let mut shares: Vec<i32> = Vec::new();
                for c in t.cs.iter() {
                    shares.append(&mut self.get_shares(c));
                }
                self.term_to_shares.insert(t.clone(), shares);
                self.cache.insert(t.clone(), EmbeddedTerm::Tuple);

                unsafe {
                    num_tuple += 1;
                    dur_tuple += now.elapsed();
                };
            }
            Op::Call(name, _arg_names, arg_sorts, ret_sorts) => {
                let shares = self.get_shares(&t);
                let op = format!("CALL({})", name);
                let num_args: usize = arg_sorts.iter().map(|ret| self.get_sort_len(ret)).sum();
                let num_rets: usize = ret_sorts.iter().map(|ret| self.get_sort_len(ret)).sum();
                // map argument shares
                // define rewireable shares with "r"
                let mut arg_shares: Vec<String> = Vec::new();
                for c in t.cs.iter() {
                    let sort = check(c);
                    if self.rewirable(&sort) {
                        arg_shares.extend(self.get_shares(c).iter().map(|&s| s.to_string()))
                    } else {
                        arg_shares.extend(self.get_shares(c).iter().map(|&s| s.to_string()))
                    }
                }

                let mut ret_shares: Vec<String> = Vec::new();
                let mut idx = 0;
                for sort in ret_sorts {
                    let len = self.get_sort_len(sort);
                    assert!(idx + len <= shares.len());
                    if self.rewirable(sort) {
                        ret_shares.extend(shares[idx..(idx + len)].iter().map(|&s| s.to_string()))
                    } else {
                        ret_shares.extend(shares[idx..(idx + len)].iter().map(|&s| s.to_string()))
                    }
                    idx += len;
                }

                let line = format!(
                    "{} {} {} {} {}\n",
                    num_args,
                    num_rets,
                    arg_shares.join(" "),
                    ret_shares.join(" "),
                    op
                );
                self.bytecode_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Tuple);

                unsafe {
                    num_call += 1;
                    dur_call += now.elapsed();
                };
            }
            _ => {
                panic!("Non-field in embed_scalar: {}", t.op)
            }
        }
    }

    fn embed(&mut self, t: Term) {
        let mut num_bool = 0;
        let mut num_bv = 0;
        let mut num_scalar = 0;

        let mut dur_bool: std::time::Duration = std::time::Duration::new(0, 0);
        let mut dur_bv: std::time::Duration = std::time::Duration::new(0, 0);
        let mut dur_scalar: std::time::Duration = std::time::Duration::new(0, 0);

        unsafe {
            dur_const_arr = std::time::Duration::new(0, 0);
            num_const_arr = 0;

            dur_const_tuple = std::time::Duration::new(0, 0);
            num_const_tuple = 0;

            dur_ite = std::time::Duration::new(0, 0);
            num_ite = 0;

            dur_store = std::time::Duration::new(0, 0);
            num_store = 0;

            dur_field = std::time::Duration::new(0, 0);
            num_field = 0;

            dur_update = std::time::Duration::new(0, 0);
            num_update = 0;

            dur_tuple = std::time::Duration::new(0, 0);
            num_tuple = 0;

            dur_call = std::time::Duration::new(0, 0);
            num_call = 0;
        }

        let mut write_time: std::time::Duration = std::time::Duration::new(0, 0);

        for c in PostOrderIter::new(t) {
            if self.cache.contains_key(&c) {
                continue;
            }

            let b_now = Instant::now(); // check for tuples are long
            match check(&c) {
                Sort::Bool => {
                    let now = Instant::now();
                    self.embed_bool(c);
                    num_bool += 1;
                    dur_bool += now.elapsed();
                }
                Sort::BitVector(_) => {
                    let now = Instant::now();
                    self.embed_bv(c);
                    num_bv += 1;
                    dur_bv += now.elapsed();
                }
                Sort::Array(..) | Sort::Tuple(_) => {
                    let now = Instant::now();
                    self.embed_scalar(c);
                    num_scalar += 1;
                    dur_scalar += now.elapsed();
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }

            let now = Instant::now();
            self.write_bytecode_output(false);
            self.write_const_output(false);
            self.write_share_output(false);
            write_time += now.elapsed();
        }

        println!("bool: {}, bv: {}, scalar: {}", num_bool, num_bv, num_scalar);
        println!(
            "times: bool: {:?}, bv: {:?}, scalar: {:?}",
            dur_bool, dur_bv, dur_scalar
        );
        println!("write time: {:?}", write_time);

        if num_bool > 0 && num_bv > 0 && num_scalar > 0 {
            println!(
                "norm_times: bool: {:?}, bv: {:?}, scalar: {:?}\n",
                dur_bool / num_bool,
                dur_bv / num_bv,
                dur_scalar / num_scalar
            );
        }

        unsafe {
            println!("================================");
            println!("const_arr: {}, const_tuple: {}, ite: {}, store: {}, field: {}, update: {}, tuple: {}, call: {}", num_const_arr, num_const_tuple, num_ite, num_store, num_field, num_update, num_tuple, num_call);
            println!("times: const_arr: {:?}, const_tuple: {:?}, ite: {:?}, store: {:?}, field: {:?}, update: {:?}, tuple: {:?}, call: {:?}", dur_const_arr, dur_const_tuple, dur_ite, dur_store, dur_field, dur_update, dur_tuple, dur_call);
            if num_const_arr > 0 {
                println!("norm_const_arr: {:?}", dur_const_arr / num_const_arr as u32);
            }
            if num_const_tuple > 0 {
                println!(
                    "norm_const_tuple: {:?}",
                    dur_const_tuple / num_const_tuple as u32
                );
            }
            if num_ite > 0 {
                println!("norm_ite: {:?}", dur_ite / num_ite as u32);
            }
            if num_store > 0 {
                println!("norm_store: {:?}", dur_store / num_store as u32);
            }
            if num_field > 0 {
                println!("norm_field: {:?}", dur_field / num_field as u32);
            }
            if num_update > 0 {
                println!("norm_update: {:?}", dur_update / num_update as u32);
            }
            if num_tuple > 0 {
                println!("norm_tuple: {:?}", dur_tuple / num_tuple as u32);
            }
            if num_call > 0 {
                println!("norm_call: {:?}", dur_call / num_call as u32);
            }
            println!("================================\n")
        }
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self) {
        let computations = self.fs.computations.clone();

        // create output files
        get_path(self.path, &self.lang, "const", true);
        get_path(self.path, &self.lang, "share_map", true);

        for (name, comp) in computations.iter() {
            let mut outputs: Vec<String> = Vec::new();
            let mut now = Instant::now();

            // set current computation
            self.curr_comp = name.to_string();

            // create paths
            get_path(
                self.path,
                &self.lang,
                &format!("{}_bytecode_output", name),
                true,
            );

            println!("starting: {}, {}", name, comp.terms());

            for t in comp.outputs.iter() {
                self.embed(t.clone());

                let op = "OUT";
                let shares = self.get_shares(&t);

                for s in shares {
                    let line = format!("1 0 {} {}\n", s, op);
                    outputs.push(line);
                }
            }
            self.bytecode_output.append(&mut outputs);

            println!("Time: lowering {}: {:?}", name, now.elapsed());

            now = Instant::now();

            // reorder inputs
            let mut bytecode_input_map: HashMap<String, String> = HashMap::new();
            for line in &self.bytecode_input {
                let key = line.split(" ").collect::<Vec<&str>>()[2];
                bytecode_input_map.insert(key.to_string(), line.to_string());
            }
            let input_order: Vec<String> = comp
                .metadata
                .get_all_inputs()
                .iter()
                .map(|x| ToABY::get_var_name(x))
                .collect();

            let inputs: Vec<String> = input_order
                .iter()
                .map(|x| {
                    if bytecode_input_map.contains_key(x) {
                        bytecode_input_map.get(x).unwrap().clone()
                    } else {
                        // Unused in gate -- ignored in ABY interpreter but used for maintaining rewiring order
                        format!("1 0 {} {}\n", x, "IN")
                    }
                })
                .filter(|x| !x.is_empty())
                .collect::<Vec<String>>();
            self.bytecode_input = inputs;
            println!("Time: reordering inputs {}: {:?}", name, now.elapsed());

            now = Instant::now();

            // write input bytecode
            let bytecode_path =
                get_path(self.path, &self.lang, &format!("{}_bytecode", name), true);
            write_lines(&bytecode_path, &self.bytecode_input);

            // write output bytecode
            let bytecode_output_path = get_path(
                self.path,
                &self.lang,
                &format!("{}_bytecode_output", name),
                false,
            );
            write_lines(&bytecode_output_path, &self.bytecode_output);

            println!("Time: writing {}: {:?}", name, now.elapsed());

            // combine input and output bytecode files into a single file
            let mut bytecode = fs::OpenOptions::new()
                .append(true)
                .open(&bytecode_path)
                .unwrap();

            let mut bytecode_output = fs::OpenOptions::new()
                .read(true)
                .open(&bytecode_output_path)
                .unwrap();

            io::copy(&mut bytecode_output, &mut bytecode).expect("Failed to merge bytecode files");

            // delete output bytecode files
            fs::remove_file(&bytecode_output_path).expect(&format!(
                "Failed to remove bytecode output: {}",
                &bytecode_output_path
            ));

            //reset for next function
            self.bytecode_input.clear();
            self.bytecode_output.clear();
            self.inputs.clear();
            self.cache.clear();
        }

        // write remaining const variables
        self.write_const_output(true);

        // write remaining shares
        self.write_share_output(true);
    }

    fn convert(&mut self) {
        let mut now = Instant::now();
        // self.map_to_shares();
        // println!("Time: map terms to shares: {:?}", now.elapsed());
        now = Instant::now();
        self.lower();
        println!("Time: lowering: {:?}", now.elapsed());
    }
}

/// Convert this (IR) `ir` to ABY.
pub fn to_aby(
    ir: Functions,
    path: &Path,
    lang: &str,
    cm: &str,
    ss: &str,
    #[allow(unused_variables)] np: &usize,
    #[allow(unused_variables)] ml: &usize,
    #[allow(unused_variables)] mss: &usize,
    #[allow(unused_variables)] hyper: &usize,
    #[allow(unused_variables)] imbalance: &usize,
) {

    // TODO: change ILP to take in Functions instead of individual computations
    
    match ss{
        "gglp" => {
            let (fs, s_map) = inline_all_and_assign_glp(&ir, cm);
            let mut converter = ToABY::new(fs, s_map, path, lang);
            converter.convert();
        }
        _ =>{
            // Protocal Assignments
            let mut s_map: HashMap<String, SharingMap> = HashMap::new();
            for (name, comp) in ir.computations.iter() {
                println!("processing computation: {}", name);
                let assignments = match ss {
                    "b" => assign_all_boolean(&comp, cm),
                    "y" => assign_all_yao(&comp, cm),
                    "a+b" => assign_arithmetic_and_boolean(&comp, cm),
                    "a+y" => assign_arithmetic_and_yao(&comp, cm),
                    "greedy" => assign_greedy(&comp, cm),
                    #[cfg(feature = "lp")]
                    "lp" => assign(&(comp.to_cs()), cm),
                    #[cfg(feature = "lp")]
                    "glp" => assign(&comp.to_cs(), cm),
                    _ => {
                        panic!("Unsupported sharing scheme: {}", ss);
                    }
                };
                s_map.insert(name.to_string(), assignments);
            }
            let mut converter = ToABY::new(ir, s_map, path, lang);
            converter.convert();
        }
    };

}
