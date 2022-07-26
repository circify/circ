//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/&blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use rug::Integer;

use fxhash::FxHashSet;

use crate::ir::opt::cfold::fold;
use crate::ir::term::*;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::SharingMap;
use crate::target::aby::utils::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

#[cfg(feature = "lp")]
use crate::target::graph::trans::*;

use super::assignment::assign_all_boolean;
use super::assignment::assign_all_yao;
use super::assignment::assign_arithmetic_and_boolean;
use super::assignment::assign_arithmetic_and_yao;
use super::assignment::assign_greedy;

// use super::call_site_similarity::call_site_similarity;

const PUBLIC: u8 = 2;
const WRITE_SIZE: usize = 65536;

pub struct PostOrderIter_v2 {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter_v2 {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::new(),
        }
    }
}

impl std::iter::Iterator for PostOrderIter_v2 {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                // for cs in t.cs.iter(){
                //     // if let Op::Const(Value::BitVector(b)) = &cs.op {
                //     //     let bi = b.as_sint();
                //     //     if bi == 99{
                //     //         println!("haha: {}", t);
                //     //     }
                //     // }
                // }
                if let Op::Select = t.op{
                    if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs[0].clone()));
                        continue;
                    }
                } else if let Op::Store = t.op{
                    if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone(); 
                        self.stack.push((false, last.cs[0].clone()));
                        self.stack.push((false, last.cs[2].clone()));
                        continue;
                    }
                }
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs.iter().map(|c| (false, c.clone())));
            } else {
                break;
            }
        }
        self.stack.pop().map(|(_, t)| {
            self.visited.insert(t.clone());
            t
        })
        // while let Some((children_pushed, t)) = self.stack.pop() {
        //     if self.visited.contains(&t) {
        //         continue;
        //     } else if !children_pushed {
        //         // if let Op::Select = t.op{
        //         //     if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
        //         //         self.stack.push((true, t.clone()));
        //         //         self.stack.push((false, t.cs[0].clone()));
        //         //         continue;
        //         //     }
        //         // }
        //         self.stack.push((true, t.clone()));
        //         self.stack
        //             .extend(t.cs.iter().map(|c| (false, c.clone())));
        //     } else {
        //         break;
        //     }
        // }
        // self.stack.pop().map(|(_, t)| {
        //     self.visited.insert(t.clone());
        //     t
        // })
    }
}

// impl std::iter::Iterator for PostOrderIter_v2 {
//     type Item = Term;
//     fn next(&mut self) -> Option<Term> {
//         while let Some(t) = self.stack.pop() {
//             if !self.visited.contains(&t) {
//                 if self.children_added.insert(t.clone()) {
//                     self.stack.push(t.clone());
//                     if let Op::Select = t.op{
//                         if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
//                             self.stack.push(t.cs[0].clone());
//                             continue;
//                         }
//                     }
//                     self.stack.extend(t.cs.iter().cloned());
//                 }
//             } else {
//                 break;
//             }
//         }
//         self.stack.pop().map(|t| {
//             self.visited.insert(t.clone());
//             t
//         })
//     }
// }

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
    // Term to share id
    term_to_shares: TermMap<Vec<i32>>,
    share_cnt: i32,
    // Cache
    cache: HashMap<(Op, Vec<i32>), Vec<i32>>,
    // Outputs
    bytecode_input: Vec<String>,
    bytecode_output: Vec<String>,
    const_output: Vec<String>,
    share_output: Vec<String>,
    term_share_output: Vec<String>,
    const_map: HashMap<(Integer, char), i32>,
    written_const_set: HashSet<i32>
}

impl Drop for ToABY<'_> {
    fn drop(&mut self) {
        // use std::mem::take;
        // drop everything that uses a Term
        // drop(take(&mut self.md));
        self.inputs.clear();
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
            term_to_shares: TermMap::new(),
            share_cnt: 0,
            cache: HashMap::new(),
            bytecode_input: Vec::new(),
            bytecode_output: Vec::new(),
            const_output: Vec::new(),
            share_output: Vec::new(),
            term_share_output: Vec::new(),
            const_map: HashMap::new(),
            written_const_set: HashSet::new(),
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
            let term_share_output_path = get_path(self.path, &self.lang, "term_share_map", false);
            write_lines(&term_share_output_path, &self.term_share_output);
            self.term_share_output.clear();
        }
    }

    fn shares_to_string(&self, shares: Vec<i32>) -> String {
        shares
            .iter()
            .map(|&i| i.to_string())
            .collect::<Vec<String>>()
            .join(" ")
    }

    fn get_md(&self) -> &ComputationMetadata {
        &self.fs.computations.get(&self.curr_comp).unwrap().metadata
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

    fn write_share(&mut self, t: &Term, s: i32) {
        if !self.written_const_set.contains(&s){
            let s_map = self.s_map.get(&self.curr_comp).unwrap();
            let share_type = s_map.get(&t).unwrap().char();
            let line = format!("{} {}\n", s, share_type);
            self.share_output.push(line);
            let line2 = format!("{} {}\n", t.op, share_type);
            self.term_share_output.push(line2);
        }
    }

    fn write_shares(&mut self, t: &Term, shares: &Vec<i32>) {
        let s_map = self.s_map.get(&self.curr_comp).unwrap();
        let share_type = s_map.get(&t).unwrap().char();
        for s in shares {
            if !self.written_const_set.contains(s){
                let line = format!("{} {}\n", s, share_type);
                self.share_output.push(line);
                let line2 = format!("{} {}\n", t.op, share_type);
                self.term_share_output.push(line2);
            }
        }
    }

    // TODO: Rust ENTRY api on maps
    fn get_new_share(&mut self, t: &Term, p: &Term) -> i32 {
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
                let s_map = self.s_map.get(&self.curr_comp).unwrap();
                let share_type = s_map.get(&p).unwrap().char();
                let line = format!("{} {}\n", s, share_type);
                self.share_output.push(line);

                s
            }
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
                match &t.op {
                    Op::Const(Value::BitVector(b)) => {
                        let sort = check(t);
                        let bi = b.as_sint();
                        let s_map = self.s_map.get(&self.curr_comp).unwrap();
                        let share_type = s_map.get(&t).unwrap().char();
                        let key = (bi, share_type);
                        if self.const_map.contains_key(&key) {
                            let s = self.const_map.get(&key).unwrap().clone();
                            self.term_to_shares.insert(t.clone(), [s].to_vec());
                            s
                        } else{
                            let s = self.share_cnt;
                            self.term_to_shares.insert(t.clone(), [s].to_vec());
                            self.share_cnt += 1;
                            self.const_map.insert(key, s);
                            // Write share
                            self.write_share(t, s);

                            s
                        }
                    }
                    _ => {
                        let s = self.share_cnt;
                        self.term_to_shares.insert(t.clone(), [s].to_vec());
                        self.share_cnt += 1;

                        // Write share
                        self.write_share(t, s);
                        if s == 16{
                            println!("#######: {}", t);
                        }

                        s
                    }
                }
            }
        }
    }

    fn get_shares(&mut self, t: &Term) -> Vec<i32> {
        match self.term_to_shares.get(t) {
            Some(v) => v.clone(),
            None => {
                match &t.op {
                    Op::Const(Value::Array(arr)) =>{
                        let sort = check(t);
                        let num_shares = self.get_sort_len(&sort) as i32;
                        let mut shares: Vec<i32> = Vec::new();
                        let s_map = self.s_map.get(&self.curr_comp).unwrap();
                        let share_type = s_map.get(&t).unwrap().char();
                        for i in 0..num_shares{
                            let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                            let v = match arr.map.get(&idx) {
                                Some(c) => c,
        
                                None => &*arr.default,
                            };
        
                            match v {
                                Value::BitVector(b) => {
                                    let bi = b.as_sint();
                                    let key = (bi, share_type);
                                    if self.const_map.contains_key(&key) {
                                        let s = self.const_map.get(&key).unwrap().clone();
                                        shares.push(s);
                                    } else{
                                        let s = self.share_cnt;
                                        self.share_cnt += 1;
                                        self.const_map.insert(key, s);
                                        shares.push(s);
                                    }
                                }
                                _ => todo!(),
                            }
                        }
                        self.term_to_shares.insert(t.clone(), shares.clone());

                        // Write shares
                        self.write_shares(t, &shares);

                        shares
                    }
                    Op::Const(Value::Tuple(tup)) => {
                        check(t);
                        let mut shares: Vec<i32> = Vec::new();
                        let s_map = self.s_map.get(&self.curr_comp).unwrap();
                        let share_type = s_map.get(&t).unwrap().char();
                        for val in tup.iter() {
                            match val {
                                Value::BitVector(b) => {
                                    let bi = b.as_sint();
                                    let key = (bi, share_type);
                                    if self.const_map.contains_key(&key) {
                                        let s = self.const_map.get(&key).unwrap().clone();
                                        shares.push(s);
                                    } else{
                                        let s = self.share_cnt;
                                        self.share_cnt += 1;
                                        self.const_map.insert(key, s);
                                        shares.push(s);
                                    }
                                }
                                _ => todo!(),
                            }
                        }
                        self.term_to_shares.insert(t.clone(), shares.clone());

                        // Write shares
                        self.write_shares(t, &shares);

                        shares
                    }
                    _ =>{
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

    fn embed_eq(&mut self, t: &Term) {
        let op = "EQ";
        let a = self.get_share(&t.cs[0]);
        let b = self.get_share(&t.cs[1]);

        let key = (t.op.clone(), vec![a, b]);
        if self.cache.contains_key(&key) {
            let s = self.cache.get(&key).unwrap().clone();
            self.term_to_shares.insert(t.clone(), s);
        } else {
            let s = self.get_shares(t);
            self.cache.insert(key, s.clone());
            let line = format!("2 1 {} {} {} {}\n", a, b, s[0], op);
            self.bytecode_output.push(line);
        };
    }

    fn embed_bool(&mut self, t: Term) {
        let s = self.get_share(&t);
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.input_vis.contains_key(name) {
                    let term_name = ToABY::get_var_name(&name);
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
            }
            Op::Const(Value::Bool(b)) => {
                let op = "CONS_bool";
                let line = format!("1 1 {} {} {}\n", *b as i32, s, op);
                self.const_output.push(line);
            }
            Op::Eq => {
                self.embed_eq(&t);
            }
            Op::Ite => {
                let op = "MUX";
                let sel = self.get_share(&t.cs[0]);
                let a = self.get_share(&t.cs[1]);
                let b = self.get_share(&t.cs[2]);

                let key = (t.op.clone(), vec![a, b]);
                if self.cache.contains_key(&key) {
                    let s = self.cache.get(&key).unwrap().clone();
                    self.term_to_shares.insert(t.clone(), s);
                } else {
                    let s = self.get_shares(&t);
                    self.cache.insert(key, s.clone());
                    let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s[0], op);
                    self.bytecode_output.push(line);
                };
            }
            Op::Not => {
                let op = "NOT";
                let a = self.get_share(&t.cs[0]);

                let key = (t.op.clone(), vec![a]);
                if self.cache.contains_key(&key) {
                    let s = self.cache.get(&key).unwrap().clone();
                    self.term_to_shares.insert(t.clone(), s);
                } else {
                    let s = self.get_shares(&t);
                    self.cache.insert(key, s.clone());
                    let line = format!("1 1 {} {} {}\n", a, s[0], op);
                    self.bytecode_output.push(line);
                };
            }
            Op::BoolNaryOp(o) => {
                if t.cs.len() == 1 {
                    // HACK: Conditionals might not contain two variables
                    // If t.cs len is 1, just output that term
                    // This is to bypass adding an AND gate with a single conditional term
                    // Refer to pub fn condition() in src/circify/mod.rs
                    let a = self.get_share(&t.cs[0]);
                    match o {
                        BoolNaryOp::And => self.term_to_shares.insert(t.clone(), vec![a]),
                        _ => {
                            unimplemented!("Single operand boolean operation");
                        }
                    };
                } else {
                    let op = match o {
                        BoolNaryOp::Or => "OR",
                        BoolNaryOp::And => "AND",
                        BoolNaryOp::Xor => "XOR",
                    };

                    let a = self.get_share(&t.cs[0]);
                    let b = self.get_share(&t.cs[1]);

                    let key = (t.op.clone(), vec![a, b]);
                    if self.cache.contains_key(&key) {
                        let s = self.cache.get(&key).unwrap().clone();
                        self.term_to_shares.insert(t.clone(), s);
                    } else {
                        let s = self.get_shares(&t);
                        self.cache.insert(key, s.clone());
                        let line = format!("2 1 {} {} {} {}\n", a, b, s[0], op);
                        self.bytecode_output.push(line);
                    };
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

                let a = self.get_share(&t.cs[0]);
                let b = self.get_share(&t.cs[1]);

                let key = (t.op.clone(), vec![a, b]);
                if self.cache.contains_key(&key) {
                    let s = self.cache.get(&key).unwrap().clone();
                    self.term_to_shares.insert(t.clone(), s);
                } else {
                    let s = self.get_shares(&t);
                    self.cache.insert(key, s.clone());
                    let line = format!("2 1 {} {} {} {}\n", a, b, s[0], op);
                    self.bytecode_output.push(line);
                };
            }
            _ => panic!("Non-field in embed_bool: {}", t),
        }
    }

    fn embed_bv(&mut self, t: Term) {
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.input_vis.contains_key(name) {
                    let term_name = ToABY::get_var_name(&name);
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
            }
            Op::Const(Value::BitVector(b)) => {
                let s = self.get_share(&t);
                if !self.written_const_set.contains(&s){
                    self.written_const_set.insert(s);
                    let op = "CONS_bv";
                    let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                    if b.as_sint() == 99{
                        println!("GOtcha: {}", t);
                    }
                    self.const_output.push(line);
                }
                // self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::Ite => {
                let op = "MUX";
                let sel = self.get_share(&t.cs[0]);
                let a = self.get_share(&t.cs[1]);
                let b = self.get_share(&t.cs[2]);

                let key = (t.op.clone(), vec![sel, a, b]);
                if self.cache.contains_key(&key) {
                    let s = self.cache.get(&key).unwrap().clone();
                    self.term_to_shares.insert(t.clone(), s);
                } else {
                    let s = self.get_shares(&t);
                    self.cache.insert(key, s.clone());
                    let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s[0], op);
                    self.bytecode_output.push(line);
                };
            }
            Op::BvNaryOp(o) => {
                let op = match o {
                    BvNaryOp::Xor => "XOR",
                    BvNaryOp::Or => "OR",
                    BvNaryOp::And => "AND",
                    BvNaryOp::Add => "ADD",
                    BvNaryOp::Mul => "MUL",
                };
                let a = self.get_share(&t.cs[0]);
                let b = self.get_share(&t.cs[1]);

                let key = (t.op.clone(), vec![a, b]);
                if self.cache.contains_key(&key) {
                    let s = self.cache.get(&key).unwrap().clone();
                    self.term_to_shares.insert(t.clone(), s);
                } else {
                    let s = self.get_shares(&t);
                    self.cache.insert(key, s.clone());
                    let line = format!("2 1 {} {} {} {}\n", a, b, s[0], op);
                    self.bytecode_output.push(line);
                };
            }
            Op::BvBinOp(o) => {
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
                        let a = self.get_share(&t.cs[0]);
                        let b = self.get_share(&t.cs[1]);

                        let key = (t.op.clone(), vec![a, b]);
                        if self.cache.contains_key(&key) {
                            let s = self.cache.get(&key).unwrap().clone();
                            self.term_to_shares.insert(t, s);
                        } else {
                            let s = self.get_shares(&t);
                            self.cache.insert(key, s.clone());
                            let line = format!("2 1 {} {} {} {}\n", a, b, s[0], op);
                            self.bytecode_output.push(line);
                        };
                    }
                    BvBinOp::Shl | BvBinOp::Lshr => {
                        let a = self.get_share(&t.cs[0]);
                        let const_shift_amount_term = fold(&t.cs[1], &[]);
                        let const_shift_amount =
                            const_shift_amount_term.as_bv_opt().unwrap().uint();

                        let key = (t.op.clone(), vec![a, const_shift_amount.to_i32().unwrap()]);
                        if self.cache.contains_key(&key) {
                            let s = self.cache.get(&key).unwrap().clone();
                            self.term_to_shares.insert(t, s);
                        } else {
                            let s = self.get_shares(&t);
                            self.cache.insert(key, s.clone());
                            let line =
                                format!("2 1 {} {} {} {}\n", a, const_shift_amount, s[0], op);
                            self.bytecode_output.push(line);
                        };
                    }
                    _ => panic!("Binop not supported: {}", o),
                };
            }
            Op::Field(i) => {
                assert!(t.cs.len() == 1);
                let shares = self.get_shares(&t.cs[0]);
                assert!(*i < shares.len());
                self.term_to_shares.insert(t.clone(), vec![shares[*i]]);
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
                }
            }
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }
    }

    fn embed_vector(&mut self, t: Term) {
        match &t.op {
            Op::Const(Value::Array(arr)) => {
                let mut shares: Vec<i32> = Vec::new();

                for i in 0..arr.size {
                    // TODO: sort of index might not be a 32-bit bitvector
                    let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                    let v = match arr.map.get(&idx) {
                        Some(c) => c,
                        None => &*arr.default,
                    };

                    // TODO: sort of value might not be a 32-bit bitvector
                    let v_term = leaf_term(Op::Const(v.clone()));
                    if self.term_to_shares.contains_key(&v_term) {
                        // existing const
                        let s = self.get_share(&v_term);
                        shares.push(s);
                    } else {
                        // new const
                        let s = self.get_new_share(&v_term, &t);
                        match v {
                            Value::BitVector(b) => {
                                if !self.written_const_set.contains(&s){
                                    self.written_const_set.insert(s);
                                    let op = "CONS_bv";
                                    let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                                    if b.as_sint() == 99{
                                        println!("GOtcha2: {}", t);
                                    }
                                    self.const_output.push(line);
                                }
                                // self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                            }
                            _ => todo!(),
                        }
                        shares.push(s);
                    }
                }

                assert!(shares.len() == arr.size);
                self.term_to_shares.insert(t.clone(), shares);
            }
            Op::Const(Value::Tuple(tup)) => {
                let shares = self.get_shares(&t);
                assert!(shares.len() == tup.len());
                for (val, s) in tup.iter().zip(shares.iter()) {
                    match val {
                        Value::BitVector(b) => {
                            if !self.written_const_set.contains(s){
                                self.written_const_set.insert(*s);
                                let op = "CONS_bv";
                                let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                                if b.as_sint() == 99{
                                    println!("GOtcha3: {}", t);
                                }
                                self.const_output.push(line);
                            }
                        }
                        _ => todo!(),
                    }
                }
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
            }
            Op::Tuple => {
                let mut shares: Vec<i32> = Vec::new();
                for c in t.cs.iter() {
                    shares.append(&mut self.get_shares(c));
                }
                self.term_to_shares.insert(t.clone(), shares);
            }
            Op::Call(name, _arg_names, arg_sorts, ret_sorts) => {
                let shares = self.get_shares(&t);
                let op = format!("CALL({})", name);
                let num_args: usize = arg_sorts.iter().map(|ret| self.get_sort_len(ret)).sum();
                let num_rets: usize = ret_sorts.iter().map(|ret| self.get_sort_len(ret)).sum();
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
            }
            _ => {
                panic!("Non-field in embed_vector: {}", t.op)
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

        for c in PostOrderIter_v2::new(t) {
            if self.term_to_shares.contains_key(&c) {
                continue;
            }

            match check(&c) {
                Sort::Bool => {
                    self.embed_bool(c);
                }
                Sort::BitVector(_) => {
                    self.embed_bv(c);
                }
                Sort::Array(..) | Sort::Tuple(_) => {
                    self.embed_vector(c);
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }
            self.write_bytecode_output(false);
            self.write_const_output(false);
            self.write_share_output(false);
        }
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self) {
        let computations = self.fs.computations.clone();

        // for (name, c) in computations.iter() {
        //     println!("name: {}", name);
        //     for t in c.terms_postorder() {
        //         println!("t: {}", t);
        //     }
        // }

        // create output files
        get_path(self.path, &self.lang, "const", true);
        get_path(self.path, &self.lang, "share_map", true);

        for (name, comp) in computations.iter() {
            let mut outputs: Vec<String> = Vec::new();

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
        }

        // write remaining const variables
        self.write_const_output(true);

        // write remaining shares
        self.write_share_output(true);
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
        #[cfg(feature = "lp")]
        "gglp" => {
            let (fs, s_map) = inline_all_and_assign_glp(&ir, cm);
            let mut converter = ToABY::new(fs, s_map, path, lang);
            converter.lower();
        }
        #[cfg(feature = "lp")]
        "lp+mut" => {
            let (fs, s_map) = partition_with_mut(&ir, cm, path, lang, np, *hyper==1, ml, mss, imbalance);
            let mut converter = ToABY::new(fs, s_map, path, lang);
            converter.lower();
        }
        #[cfg(feature = "lp")]
        "smart_glp" => {
            let (fs, s_map) = inline_all_and_assign_smart_glp(&ir, cm);
            let mut converter = ToABY::new(fs, s_map, path, lang);
            converter.lower();
        }
        // #[cfg(feature = "lp")]
        // "mlp+mut" => {
        //     let (fs, s_map) = mlp_with_mut(&ir, cm, path, lang, np, *hyper==1, ml, mss, imbalance);
        //     let mut converter = ToABY::new(fs, s_map, path, lang);
        //     converter.lower();
        // }
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
            converter.lower();
        }
    };

}

fn get_sort_len(s: &Sort) -> usize {
    let mut len = 0;
    len += match s {
        Sort::Bool => 1,
        Sort::BitVector(_) => 1,
        Sort::Array(_, _, n) => *n,
        Sort::Tuple(sorts) => {
            let mut inner_len = 0;
            for inner_s in sorts.iter() {
                inner_len += get_sort_len(inner_s);
            }
            inner_len
        }
        _ => panic!("Sort is not supported: {:#?}", s),
    };
    len
}

pub fn construct_def_uses(c: &Computation) -> (TermSet, FxHashSet<(Term, Term)>){
    let mut term_to_terms: TermMap<Vec<Term>> = TermMap::new();
    let mut def_uses: FxHashSet<(Term, Term)> = FxHashSet::default();
    let mut const_terms: TermSet = TermSet::new();
    let mut good_terms: TermSet = TermSet::new();
    for out in c.outputs.iter() {
        for t in PostOrderIter_v2::new(out.clone()) {
            match &t.op{
                Op::Const(Value::Tuple(tup)) => {
                    let mut terms: Vec<Term> = Vec::new();
                    for val in tup.iter() {
                        terms.push(leaf_term(Op::Const(val.clone())));
                        const_terms.insert(leaf_term(Op::Const(val.clone())));
                        good_terms.insert(leaf_term(Op::Const(val.clone())));
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Tuple => {
                    let mut terms: Vec<Term> = Vec::new();
                    for c in t.cs.iter() {
                        terms.extend(term_to_terms.get(&c).unwrap().clone());
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Field(i) => {
                    let terms = term_to_terms.get(&t.cs[0]).unwrap().clone();
                    term_to_terms.insert(t.clone(), vec![terms[*i].clone()]);
                }
                Op::Update(i) => {
                    let mut tuple_terms = term_to_terms.get(&t.cs[0]).unwrap().clone();
                    let value_terms = term_to_terms.get(&t.cs[1]).unwrap().clone();
                    tuple_terms[*i] = value_terms[0].clone();
                    term_to_terms.insert(t.clone(), tuple_terms);
                }
                Op::Const(Value::Array(arr)) => {
                    let mut terms: Vec<Term> = Vec::new();
                    let sort = check(&t);
                    if let Sort::Array(_, _, n) = sort{
                        let n = n as i32;
                        for i in 0..n{
                            let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                            let v = match arr.map.get(&idx) {
                                Some(c) => c,
                                None => &*arr.default,
                            };
                            terms.push(leaf_term(Op::Const(v.clone())));
                            const_terms.insert(leaf_term(Op::Const(v.clone())));
                            good_terms.insert(leaf_term(Op::Const(v.clone())));
                        }
                    } else{
                        todo!("Const array sort not array????")
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Store => {
                    let mut array_terms = term_to_terms.get(&t.cs[0]).unwrap().clone();
                    let value_terms = term_to_terms.get(&t.cs[2]).unwrap().clone();
                    if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        array_terms[idx] = value_terms[0].clone();
                        term_to_terms.insert(t.clone(), array_terms);
                    }
                    // secret indexing?
                }
                Op::Select => {
                    let array_terms = term_to_terms.get(&t.cs[0]).unwrap().clone();
                    if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        term_to_terms.insert(t.clone(), vec![array_terms[idx].clone()]);
                    }
                }
                // noy sure if we should include call in def uses...
                // Op::Call(..) => {
                //     term_to_terms.insert(t.clone(), vec![t.clone()]);
                // }
                // _ =>{
                //     for c in t.cs.iter(){
                //         if let Op::Call(..) = t.op{
                //             continue;
                //         } else{
                //             let terms = term_to_terms.get(c).unwrap();
                //             assert_eq!(terms.len(), 1);
                //             def_uses.insert((t.clone(), terms[0].clone()));
                //         }
                //     }
                //     term_to_terms.insert(t.clone(), vec![t.clone()]);
                // }
                Op::Call(_, _, _, ret_sorts) => {
                    // Use call term itself as the placeholder
                    // Call term will be ignore by the ilp solver later
                    let mut ret_terms: Vec<Term> = Vec::new();
                    let num_rets: usize = ret_sorts.iter().map(|ret| get_sort_len(ret)).sum();
                    for _ in 0..num_rets{
                        ret_terms.push(t.clone());
                    }
                    term_to_terms.insert(t.clone(), ret_terms);
                }
                _ =>{
                    for c in t.cs.iter(){
                        if let Op::Call(..) = t.op{
                            continue;
                        } else{
                            let terms = term_to_terms.get(c).unwrap();
                            assert_eq!(terms.len(), 1);
                            def_uses.insert((t.clone(), terms[0].clone()));
                        }
                    }
                    term_to_terms.insert(t.clone(), vec![t.clone()]);
                    good_terms.insert(t.clone());
                }
            }
        }
    }
    (good_terms, def_uses)
}