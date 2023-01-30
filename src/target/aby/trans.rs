//! Lowering IR to ABY bytecode
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
use std::fs;
use std::io;
use std::path::Path;

use super::assignment::assign_all_boolean;
use super::assignment::assign_all_yao;
use super::assignment::assign_arithmetic_and_boolean;
use super::assignment::assign_arithmetic_and_yao;
use super::assignment::assign_greedy;
use super::assignment::ShareType;

const PUBLIC: u8 = 2;
const WRITE_SIZE: usize = 65536;

struct ToABY<'a> {
    cs: Computations,
    s_map: HashMap<String, SharingMap>,
    path: &'a Path,
    lang: String,
    curr_comp: String,
    // Input mapping
    inputs: Vec<Term>,
    // Term to share id
    term_to_shares: TermMap<i32>,
    share_cnt: i32,
    // Cache
    cache: HashMap<(Op, Vec<i32>), i32>,
    // Const Cache
    const_cache: HashMap<Term, HashMap<ShareType, i32>>,
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
        self.term_to_shares.clear();
        // self.s_map.clear();
        // clean up
        garbage_collect();
    }
}

impl<'a> ToABY<'a> {
    fn new(
        cs: Computations,
        s_map: HashMap<String, SharingMap>,
        path: &'a Path,
        lang: &str,
    ) -> Self {
        Self {
            cs,
            s_map,
            path,
            lang: lang.to_string(),
            curr_comp: "".to_string(),
            inputs: Vec::new(),
            term_to_shares: TermMap::default(),
            share_cnt: 0,
            cache: HashMap::new(),
            const_cache: HashMap::new(),
            bytecode_input: Vec::new(),
            bytecode_output: Vec::new(),
            const_output: Vec::new(),
            share_output: Vec::new(),
        }
    }

    fn write_const_output(&mut self, flush: bool) {
        if flush || self.const_output.len() >= WRITE_SIZE {
            let const_output_path = get_path(self.path, &self.lang, "const", false);
            let mut lines = self
                .const_output
                .clone()
                .into_iter()
                .collect::<Vec<String>>();
            lines.dedup();
            write_lines(&const_output_path, &lines);
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
            let mut lines = self
                .share_output
                .clone()
                .into_iter()
                .collect::<Vec<String>>();
            lines.dedup();
            write_lines(&share_output_path, &lines);
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

    fn get_md(&self) -> &ComputationMetadata {
        &self.cs.comps.get(&self.curr_comp).unwrap().metadata
    }

    fn get_term_share_type(&self, t: &Term) -> ShareType {
        let s_map = self.s_map.get(&self.curr_comp).unwrap();
        *s_map.get(t).unwrap()
    }

    fn insert_const(&mut self, t: &Term) {
        if !self.const_cache.contains_key(t) {
            let mut const_map: HashMap<ShareType, i32> = HashMap::new();

            // a type
            let s_a = self.share_cnt;
            const_map.insert(ShareType::Arithmetic, s_a);
            self.share_cnt += 1;

            // b type
            let s_b = self.share_cnt;
            const_map.insert(ShareType::Boolean, s_b);
            self.share_cnt += 1;

            // y type
            let s_y = self.share_cnt;
            const_map.insert(ShareType::Yao, s_y);
            self.share_cnt += 1;

            self.const_cache.insert(t.clone(), const_map);
        }
    }

    fn output_const_share(&mut self, t: &Term, to_share_type: ShareType) -> i32 {
        if self.const_cache.contains_key(t) {
            let output_share = *self
                .const_cache
                .get(t)
                .unwrap()
                .get(&to_share_type)
                .unwrap();
            let op = "CONS";

            match &t.op() {
                Op::Const(Value::BitVector(b)) => {
                    let value = b.as_sint();
                    let bitlen = 32;
                    let line = format!("2 1 {value} {bitlen} {output_share} {op}\n");
                    self.const_output.push(line);
                }
                Op::Const(Value::Bool(b)) => {
                    let value = *b as i32;
                    let bitlen = 1;
                    let line = format!("2 1 {value} {bitlen} {output_share} {op}\n");
                    self.const_output.push(line);
                }
                _ => todo!(),
            };

            // Add to share map
            let line = format!("{} {}\n", output_share, to_share_type.char());
            self.share_output.push(line);

            output_share
        } else {
            panic!("const cache does not contain term: {}", t);
        }
    }

    fn write_share(&mut self, t: &Term, s: i32) {
        let share_type = self.get_term_share_type(t).char();
        let line = format!("{s} {share_type}\n");
        self.share_output.push(line);
    }

    // TODO: Rust ENTRY api on maps
    fn get_share(&mut self, t: &Term, to_share_type: ShareType) -> i32 {
        if t.is_const() && check(t).is_scalar() {
            self.output_const_share(t, to_share_type)
        } else {
            match self.term_to_shares.get(t) {
                Some(v) => *v,
                None => {
                    let s = self.share_cnt;
                    self.term_to_shares.insert(t.clone(), s);
                    self.share_cnt += 1;

                    // Write share
                    self.write_share(t, s);

                    s
                }
            }
        }
    }

    // clippy doesn't like that self is only used in recursion
    // allowing so this can remain an associated function
    #[allow(clippy::only_used_in_recursion)]
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
        let to_share_type = self.get_term_share_type(t);
        let a = self.get_share(&t.cs()[0], to_share_type);
        let b = self.get_share(&t.cs()[1], to_share_type);
        let key = (t.op().clone(), vec![a, b]);
        let s = self.get_share(t, to_share_type);
        if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone()) {
            e.insert(s);
            let line = format!("2 1 {a} {b} {s} {op}\n");
            self.bytecode_output.push(line);
        } else {
            let s = *self.cache.get(&key).unwrap();
            self.term_to_shares.insert(t.clone(), s);
        };
    }

    fn embed_bool(&mut self, t: Term) {
        let to_share_type = self.get_term_share_type(&t);
        match &t.op() {
            Op::Var(name, Sort::Bool) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.is_input(name) {
                    let vis = self.unwrap_vis(name);
                    let s = self.get_share(&t, to_share_type);
                    let op = "IN";

                    if vis == PUBLIC {
                        let bitlen = 1;
                        let line = format!("3 1 {name} {vis} {bitlen} {s} {op}\n");
                        self.bytecode_input.push(line);
                    } else {
                        let line = format!("2 1 {name} {vis} {s} {op}\n");
                        self.bytecode_input.push(line);
                    }
                    self.inputs.push(t.clone());
                }
            }
            Op::Const(_) => {
                self.insert_const(&t);
            }
            Op::Eq => {
                self.embed_eq(&t);
            }
            Op::Ite => {
                let op = "MUX";
                let to_share_type = self.get_term_share_type(&t);
                let sel = self.get_share(&t.cs()[0], to_share_type);
                let a = self.get_share(&t.cs()[1], to_share_type);
                let b = self.get_share(&t.cs()[2], to_share_type);

                let key = (t.op().clone(), vec![a, b]);
                let s = self.get_share(&t, to_share_type);
                if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone())
                {
                    e.insert(s);
                    let line = format!("3 1 {sel} {a} {b} {s} {op}\n");
                    self.bytecode_output.push(line);
                } else {
                    let s = *self.cache.get(&key).unwrap();
                    self.term_to_shares.insert(t.clone(), s);
                };
            }
            Op::Not => {
                let op = "NOT";
                let a = self.get_share(&t.cs()[0], to_share_type);

                let key = (t.op().clone(), vec![a]);
                let s = self.get_share(&t, to_share_type);
                if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone())
                {
                    e.insert(s);
                    let line = format!("1 1 {a} {s} {op}\n");
                    self.bytecode_output.push(line);
                } else {
                    let s = *self.cache.get(&key).unwrap();
                    self.term_to_shares.insert(t.clone(), s);
                };
            }
            Op::BoolNaryOp(o) => {
                if t.cs().len() == 1 {
                    // HACK: Conditionals might not contain two variables
                    // If t.cs() len is 1, just output that term
                    // This is to bypass adding an AND gate with a single conditional term
                    // Refer to pub fn condition() in src/circify/mod.rs
                    let a = self.get_share(&t.cs()[0], to_share_type);
                    match o {
                        BoolNaryOp::And => self.term_to_shares.insert(t.clone(), a),
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

                    let a = self.get_share(&t.cs()[0], to_share_type);
                    let b = self.get_share(&t.cs()[1], to_share_type);

                    let key = (t.op().clone(), vec![a, b]);
                    let s = self.get_share(&t, to_share_type);
                    if let std::collections::hash_map::Entry::Vacant(e) =
                        self.cache.entry(key.clone())
                    {
                        e.insert(s);
                        let line = format!("2 1 {a} {b} {s} {op}\n");
                        self.bytecode_output.push(line);
                    } else {
                        let s = *self.cache.get(&key).unwrap();
                        self.term_to_shares.insert(t.clone(), s);
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

                let a = self.get_share(&t.cs()[0], to_share_type);
                let b = self.get_share(&t.cs()[1], to_share_type);

                let key = (t.op().clone(), vec![a, b]);
                let s = self.get_share(&t, to_share_type);
                if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone())
                {
                    e.insert(s);
                    let line = format!("2 1 {a} {b} {s} {op}\n");
                    self.bytecode_output.push(line);
                } else {
                    let s = *self.cache.get(&key).unwrap();
                    self.term_to_shares.insert(t.clone(), s);
                };
            }
            _ => panic!("Non-field in embed_bool: {}", t),
        }
    }

    fn embed_bv(&mut self, t: Term) {
        let to_share_type = self.get_term_share_type(&t);
        match &t.op() {
            Op::Var(name, Sort::BitVector(_)) => {
                let md = self.get_md();
                if !self.inputs.contains(&t) && md.is_input(name) {
                    let vis = self.unwrap_vis(name);
                    let s = self.get_share(&t, to_share_type);
                    let op = "IN";

                    if vis == PUBLIC {
                        let bitlen = 32;
                        let line = format!("3 1 {name} {vis} {bitlen} {s} {op}\n");
                        self.bytecode_input.push(line);
                    } else {
                        let line = format!("2 1 {name} {vis} {s} {op}\n");
                        self.bytecode_input.push(line);
                    }
                    self.inputs.push(t.clone());
                }
            }
            Op::Const(Value::BitVector(_)) => {
                // create all three shares
                self.insert_const(&t);
            }
            Op::Ite => {
                let op = "MUX";
                let sel = self.get_share(&t.cs()[0], to_share_type);
                let a = self.get_share(&t.cs()[1], to_share_type);
                let b = self.get_share(&t.cs()[2], to_share_type);

                let key = (t.op().clone(), vec![sel, a, b]);
                let s = self.get_share(&t, to_share_type);
                if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone())
                {
                    e.insert(s);
                    let line = format!("3 1 {sel} {a} {b} {s} {op}\n");
                    self.bytecode_output.push(line);
                } else {
                    let s = *self.cache.get(&key).unwrap();
                    self.term_to_shares.insert(t.clone(), s);
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
                let a = self.get_share(&t.cs()[0], to_share_type);
                let b = self.get_share(&t.cs()[1], to_share_type);

                let key = (t.op().clone(), vec![a, b]);
                let s = self.get_share(&t, to_share_type);
                if let std::collections::hash_map::Entry::Vacant(e) = self.cache.entry(key.clone())
                {
                    e.insert(s);
                    let line = format!("2 1 {a} {b} {s} {op}\n");
                    self.bytecode_output.push(line);
                } else {
                    let s = *self.cache.get(&key).unwrap();
                    self.term_to_shares.insert(t.clone(), s);
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
                        let a = self.get_share(&t.cs()[0], to_share_type);
                        let b = self.get_share(&t.cs()[1], to_share_type);

                        let key = (t.op().clone(), vec![a, b]);
                        let s = self.get_share(&t, to_share_type);
                        if let std::collections::hash_map::Entry::Vacant(e) =
                            self.cache.entry(key.clone())
                        {
                            e.insert(s);
                            let line = format!("2 1 {a} {b} {s} {op}\n");
                            self.bytecode_output.push(line);
                        } else {
                            let s = *self.cache.get(&key).unwrap();
                            self.term_to_shares.insert(t, s);
                        };
                    }
                    BvBinOp::Shl | BvBinOp::Lshr => {
                        let a = self.get_share(&t.cs()[0], to_share_type);
                        let const_shift_amount_term = fold(&t.cs()[1], &[]);
                        let const_shift_amount =
                            const_shift_amount_term.as_bv_opt().unwrap().uint();

                        let key = (
                            t.op().clone(),
                            vec![a, const_shift_amount.to_i32().unwrap()],
                        );
                        let s = self.get_share(&t, to_share_type);
                        if let std::collections::hash_map::Entry::Vacant(e) =
                            self.cache.entry(key.clone())
                        {
                            e.insert(s);
                            let line = format!("2 1 {a} {const_shift_amount} {s} {op}\n");
                            self.bytecode_output.push(line);
                        } else {
                            let s = *self.cache.get(&key).unwrap();
                            self.term_to_shares.insert(t, s);
                        };
                    }
                    _ => panic!("Binop not supported: {}", o),
                };
            }
            Op::Field(i) => {
                assert!(t.cs().len() == 1);
                let tuple_share = self.get_share(&t.cs()[0], to_share_type);
                let field_share = self.get_share(&t, to_share_type);
                let op = "FIELD";
                let line = format!("2 1 {tuple_share} {i} {field_share} {op}\n");
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), field_share);
            }
            Op::Select => {
                assert!(t.cs().len() == 2);
                let select_share = self.get_share(&t, to_share_type);
                let array_share = self.get_share(&t.cs()[0], to_share_type);

                let line = if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                    let op = "SELECT_CONS";
                    let idx = bv.uint().to_usize().unwrap();
                    let len = self.get_sort_len(&check(&t.cs()[0]));
                    assert!(idx < len, "{}", "idx: {idx}, len: {len}");
                    format!("2 1 {array_share} {idx} {select_share} {op}\n")
                } else {
                    let op = "SELECT";
                    let idx_share = self.get_share(&t.cs()[1], to_share_type);
                    format!("2 1 {array_share} {idx_share} {select_share} {op}\n",)
                };
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), select_share);
            }
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }
    }

    fn embed_vector(&mut self, t: Term) {
        let to_share_type = self.get_term_share_type(&t);
        match &t.op() {
            Op::Const(Value::Array(arr)) => {
                let array_share = self.get_share(&t, to_share_type);
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
                    if self.const_cache.contains_key(&v_term) {
                        // existing const
                        let s = self.get_share(&v_term, to_share_type);
                        shares.push(s);
                    } else {
                        // new const
                        self.insert_const(&v_term);
                        let s = self.get_share(&v_term, to_share_type);
                        shares.push(s);
                    }
                }
                assert!(shares.len() == arr.size);

                let op = "CONS_ARRAY";
                let line = format!(
                    "{} 1 {} {} {}\n",
                    arr.size,
                    self.shares_to_string(shares),
                    array_share,
                    op
                );
                self.const_output.push(line);
                self.term_to_shares.insert(t.clone(), array_share);
            }
            Op::Const(Value::Tuple(tup)) => {
                let tuple_share = self.get_share(&t, to_share_type);
                let mut shares: Vec<i32> = Vec::new();
                for val in tup.iter() {
                    match val {
                        Value::BitVector(b) => {
                            let v_term: Term = bv_lit(b.as_sint(), 32);
                            if self.const_cache.contains_key(&v_term) {
                                // existing const
                                let s = self.get_share(&v_term, to_share_type);
                                shares.push(s);
                            } else {
                                // new const
                                self.insert_const(&v_term);
                                let s = self.get_share(&v_term, to_share_type);
                                shares.push(s);
                            }
                        }
                        _ => todo!(),
                    }
                }
                assert!(shares.len() == tup.len());

                let op = "CONS_TUPLE";
                let line = format!(
                    "{} 1 {} {} {}\n",
                    tup.len(),
                    self.shares_to_string(shares.clone()),
                    tuple_share,
                    op
                );
                self.const_output.push(line);
                self.term_to_shares.insert(t.clone(), tuple_share);
            }
            Op::Ite => {
                let op = "MUX";
                let mux_share = self.get_share(&t, to_share_type);
                let sel = self.get_share(&t.cs()[0], to_share_type);
                let a = self.get_share(&t.cs()[1], to_share_type);
                let b = self.get_share(&t.cs()[2], to_share_type);

                let line = format!("3 1 {sel} {a} {b} {mux_share} {op}\n");
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), mux_share);
            }
            Op::Store => {
                assert!(t.cs().len() == 3);

                let array_share = self.get_share(&t.cs()[0], to_share_type);
                // let mut array_shares = self.get_shares(&t.cs()[0], to_share_type).clone();
                let value_share = self.get_share(&t.cs()[2], to_share_type);
                let store_share = self.get_share(&t, to_share_type);

                let line = if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                    let op = "STORE_CONS";
                    let idx = bv.uint().to_usize().unwrap();
                    let len = self.get_sort_len(&check(&t.cs()[0]));
                    assert!(idx < len, "{}", "idx: {idx}, len: {len}");
                    format!("3 1 {array_share} {idx} {value_share} {store_share} {op}\n",)
                } else {
                    let op = "STORE";
                    let index_share = self.get_share(&t.cs()[1], to_share_type);
                    format!("3 1 {array_share} {index_share} {value_share} {store_share} {op}\n",)
                };
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), store_share);
            }
            Op::Field(i) => {
                assert!(t.cs().len() == 1);

                // let shares = self.get_shares(&t.cs()[0], to_share_type);
                let tuple_share = self.get_share(&t.cs()[0], to_share_type);
                let field_share = self.get_share(&t, to_share_type);

                let op = "FIELD_VEC";

                let tuple_sort = check(&t.cs()[0]);
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

                let line = format!("3 1 {tuple_share} {offset} {len} {field_share} {op}\n");
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), field_share);
            }
            Op::Update(i) => {
                assert!(t.cs().len() == 2);

                let tuple_share = self.get_share(&t.cs()[0], to_share_type);
                let value_share = self.get_share(&t.cs()[1], to_share_type);
                let update_share = self.get_share(&t, to_share_type);

                let op = "UPDATE";
                let line = format!("3 1 {tuple_share} {i} {value_share} {update_share} {op}\n",);
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), update_share);
            }
            Op::Tuple => {
                let tuple_share = self.get_share(&t, to_share_type);

                let mut shares: Vec<i32> = Vec::new();
                for c in t.cs().iter() {
                    shares.push(self.get_share(c, to_share_type));
                }

                let op = "TUPLE";
                let line = format!(
                    "{} 1 {} {} {}\n",
                    t.cs().len(),
                    self.shares_to_string(shares.clone()),
                    tuple_share,
                    op
                );
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), tuple_share);
            }
            Op::Call(name, ..) => {
                let call_share = self.get_share(&t, to_share_type);
                let op = format!("CALL({name})");

                let mut arg_shares: Vec<i32> = Vec::new();
                for c in t.cs().iter() {
                    arg_shares.push(self.get_share(c, to_share_type));
                }

                let line = format!(
                    "{} 1 {} {} {}\n",
                    arg_shares.len(),
                    self.shares_to_string(arg_shares),
                    call_share,
                    op
                );
                self.bytecode_output.push(line);
                self.term_to_shares.insert(t.clone(), call_share);
            }
            _ => {
                panic!("Non-field in embed_vector: {}", t.op())
            }
        }
    }

    fn embed(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
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
        let computations = self.cs.comps.clone();

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
                &format!("{name}_bytecode_output"),
                true,
            );

            for t in comp.outputs.iter() {
                self.embed(t.clone());

                let op = "OUT";
                let to_share_type = self.get_term_share_type(t);
                let share = self.get_share(t, to_share_type);
                let line = format!("1 0 {share} {op}\n");
                outputs.push(line);
            }
            self.bytecode_output.append(&mut outputs);

            // reorder inputs
            let mut bytecode_input_map: HashMap<String, String> = HashMap::new();
            for line in &self.bytecode_input {
                let key = line.split(' ').collect::<Vec<&str>>()[2];
                bytecode_input_map.insert(key.to_string(), line.to_string());
            }

            let inputs: Vec<String> = comp
                .metadata
                .ordered_input_names()
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
            let bytecode_path = get_path(self.path, &self.lang, &format!("{name}_bytecode"), true);
            write_lines(&bytecode_path, &self.bytecode_input);

            // write output bytecode
            let bytecode_output_path = get_path(
                self.path,
                &self.lang,
                &format!("{name}_bytecode_output"),
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
            fs::remove_file(&bytecode_output_path).unwrap_or_else(|_| {
                panic!(
                    "Failed to remove bytecode output: {}",
                    &bytecode_output_path
                )
            });

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
pub fn to_aby(cs: Computations, path: &Path, lang: &str, cm: &str, ss: &str) {
    // Protocol Assignments
    let mut s_map: HashMap<String, SharingMap> = HashMap::new();

    // TODO: change ILP to take in Functions instead of individual computations
    for (name, comp) in cs.comps.iter() {
        let assignments = match ss {
            "b" => assign_all_boolean(comp, cm),
            "y" => assign_all_yao(comp, cm),
            "a+b" => assign_arithmetic_and_boolean(comp, cm),
            "a+y" => assign_arithmetic_and_yao(comp, cm),
            "greedy" => assign_greedy(comp, cm),
            #[cfg(feature = "lp")]
            "lp" => assign(comp, cm),
            #[cfg(feature = "lp")]
            "glp" => assign(comp, cm),
            _ => {
                panic!("Unsupported sharing scheme: {}", ss);
            }
        };
        #[cfg(feature = "bench")]
        println!("LOG: Assignment {}: {:?}", name, now.elapsed());
        s_map.insert(name.to_string(), assignments);
    }

    let mut converter = ToABY::new(cs, s_map, path, lang);
    converter.lower();
}
