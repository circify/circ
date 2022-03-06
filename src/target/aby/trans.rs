//! Lowering IR to ABY DSL
//! [EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/ABY_example/common/ezpc.h)

//! Inv gates need to typecast circuit object to boolean circuit
//! [Link to comment in EzPC Compiler](https://github.com/mpc-msri/EzPC/blob/da94a982709123c8186d27c9c93e27f243d85f0e/EzPC/EzPC/codegen.ml)

use crate::ir::term::*;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::SharingMap;
use crate::target::aby::utils::*;
use std::fmt;
use std::path::Path;

#[cfg(not(feature = "lp"))]
use super::assignment::some_arith_sharing;

// const BOOLEAN_BITLEN: i32 = 1;

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
    cache: TermMap<EmbeddedTerm>,
    term_to_share_cnt: TermMap<i32>,
    s_map: SharingMap,
    share_cnt: i32,
    bytecode_path: String,
    share_map_path: String,
    param_map_path: String,
}

impl ToABY {
    fn new(s_map: SharingMap, path: &Path, lang: &str) -> Self {
        Self {
            cache: TermMap::new(),
            term_to_share_cnt: TermMap::new(),
            s_map,
            share_cnt: 0,
            bytecode_path: get_path(path, lang, "bytecode"),
            share_map_path: get_path(path, lang, "share_map"),
            param_map_path: get_path(path, lang, "param_map"),
        }
    }

    fn map_terms_to_shares(&mut self, term_: Term) {
        for t in PostOrderIter::new(term_) {
            self.term_to_share_cnt.insert(t, self.share_cnt);
            self.share_cnt += 1;
        }
    }

    fn write_mapping_file(&self, term_: Term) {
        for t in PostOrderIter::new(term_) {
            let share_type = self.s_map.get(&t).unwrap();
            let share_str = share_type.char();
            let share_cnt = self.term_to_share_cnt.get(&t).unwrap();
            write_line_to_file(
                &self.share_map_path,
                &format!("{} {}\n", *share_cnt, share_str),
            );
        }
    }

    fn get_var_name(t: &Term) -> String {
        match &t.op {
            Op::Var(name, _) => {
                let new_name = name.to_string().replace('.', "_");
                let n = new_name.split('_').collect::<Vec<&str>>();

                match n.len() {
                    5 => n[3].to_string(),
                    6.. => {
                        let l = n.len() - 1;
                        format!("{}_{}", n[l - 2], n[l])
                    }
                    _ => {
                        panic!("Invalid variable name: {}", name);
                    }
                }
            }
            _ => panic!("Term {} is not of type Var", t),
        }
    }

    fn get_share_name(&mut self, t: &Term) -> String {
        let share_cnt = self.term_to_share_cnt.get(t).unwrap();
        format!("s_{}", share_cnt)
    }

    /// Return constant gate evaluating to 1
    // fn one(s_type: &str) -> String {
    //     format!("{}->PutCONSGate((uint64_t)1, (uint32_t)1)", s_type)
    // }

    fn embed_eq(&mut self, t: Term, a_term: Term, b_term: Term) {
        let share = self.get_share_name(&t);
        let s = self.term_to_share_cnt.get(&t).unwrap();
        let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
        let b = self.term_to_share_cnt.get(&t.cs[1]).unwrap();
        let op = "EQ";
        let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
        write_line_to_file(&self.bytecode_path, &line);
        match check(&a_term) {
            Sort::Bool => {
                self.check_bool(&a_term);
                self.check_bool(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool(share));
            }
            Sort::BitVector(_) => {
                self.check_bv(&a_term);
                self.check_bv(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool(share));
            }
            e => panic!("Unimplemented sort for Eq: {:?}", e),
        }
    }

    /// Given term `t`, type-check `t` is of type Bool
    fn check_bool(&self, t: &Term) {
        self.cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t));
    }

    fn embed_bool(&mut self, t: Term) {
        let share = self.get_share_name(&t);
        let s = self.term_to_share_cnt.get(&t).unwrap();
        match &t.op {
            Op::Var(_, Sort::Bool) => {
                if !self.cache.contains_key(&t) {
                    self.cache.insert(
                        t.clone(),
                        EmbeddedTerm::Bool(format!("s_{}", ToABY::get_var_name(&t))),
                    );
                    let line = format!(
                        "{} {}\n",
                        ToABY::get_var_name(&t),
                        self.term_to_share_cnt.get(&t).unwrap()
                    );
                    write_line_to_file(&self.param_map_path, &line);
                }
            }
            Op::Const(Value::Bool(b)) => {
                let op = "CONS_bool";
                let line = format!("1 1 {} {} {}\n", *b as i32, s, op);
                write_line_to_file(&self.bytecode_path, &line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::Eq => {
                self.embed_eq(t.clone(), t.cs[0].clone(), t.cs[1].clone());
            }
            Op::Ite => {
                let op = "MUX";

                self.check_bool(&t.cs[0]);
                self.check_bv(&t.cs[1]);
                self.check_bv(&t.cs[2]);

                let sel = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let a = self.term_to_share_cnt.get(&t.cs[1]).unwrap();
                let b = self.term_to_share_cnt.get(&t.cs[2]).unwrap();

                let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::Not => {
                let op = "NOT";

                self.check_bool(&t.cs[0]);

                let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let line = format!("1 1 {} {} {}\n", a, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            Op::BoolNaryOp(o) => {
                if t.cs.len() == 1 {
                    // HACK: Conditionals might not contain two variables
                    // If t.cs len is 1, just output that term
                    // This is to bypass adding an AND gate with a single conditional term
                    // Refer to pub fn condition() in src/circify/mod.rs
                    self.check_bool(&t.cs[0]);
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
                } else {
                    self.check_bool(&t.cs[0]);
                    self.check_bool(&t.cs[1]);

                    let op = match o {
                        BoolNaryOp::Or => "OR",
                        BoolNaryOp::And => "AND",
                        BoolNaryOp::Xor => "XOR",
                    };

                    let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                    let b = self.term_to_share_cnt.get(&t.cs[1]).unwrap();
                    let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                    write_line_to_file(&self.bytecode_path, &line);

                    self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
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

                let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let b = self.term_to_share_cnt.get(&t.cs[1]).unwrap();
                let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool(share));
            }
            _ => panic!("Non-field in embed_bool: {}", t),
        }
    }

    /// Given term `t`, type-check `t` is of type Bv
    fn check_bv(&self, t: &Term) {
        self.cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing wire for {:?}", t));
    }

    fn embed_bv(&mut self, t: Term) {
        let share = self.get_share_name(&t);
        let s = self.term_to_share_cnt.get(&t).unwrap();
        match &t.op {
            Op::Var(_, Sort::BitVector(_)) => {
                if !self.cache.contains_key(&t) {
                    self.cache.insert(
                        t.clone(),
                        EmbeddedTerm::Bv(format!("s_{}", ToABY::get_var_name(&t))),
                    );
                    let line = format!(
                        "{} {}\n",
                        ToABY::get_var_name(&t),
                        self.term_to_share_cnt.get(&t).unwrap()
                    );
                    write_line_to_file(&self.param_map_path, &line);
                }
            }
            Op::Const(Value::BitVector(b)) => {
                let op = "CONS_bv";
                let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                write_line_to_file(&self.bytecode_path, &line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::Ite => {
                let op = "MUX";

                self.check_bool(&t.cs[0]);
                self.check_bv(&t.cs[1]);
                self.check_bv(&t.cs[2]);

                let sel = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let a = self.term_to_share_cnt.get(&t.cs[1]).unwrap();
                let b = self.term_to_share_cnt.get(&t.cs[2]).unwrap();

                let line = format!("3 1 {} {} {} {} {}\n", sel, a, b, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::BvNaryOp(o) => {
                let op = match o {
                    BvNaryOp::Xor => "XOR",
                    BvNaryOp::Or => "OR",
                    BvNaryOp::And => "AND",
                    BvNaryOp::Add => "ADD",
                    BvNaryOp::Mul => "MUL",
                };

                self.check_bv(&t.cs[0]);
                self.check_bv(&t.cs[1]);

                let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let b = self.term_to_share_cnt.get(&t.cs[1]).unwrap();

                let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            Op::BvBinOp(o) => {
                let op = match o {
                    BvBinOp::Sub => "SUB",
                    BvBinOp::Udiv => "DIV",
                    BvBinOp::Urem => "REM",
                    BvBinOp::Shl => "SHL",
                    BvBinOp::Lshr => "LSHR",
                    BvBinOp::Ashr => "ASHR",
                };

                self.check_bv(&t.cs[0]);
                self.check_bv(&t.cs[1]);

                let a = self.term_to_share_cnt.get(&t.cs[0]).unwrap();
                let b = self.term_to_share_cnt.get(&t.cs[1]).unwrap();

                let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
                write_line_to_file(&self.bytecode_path, &line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bv(share));
            }
            // TODO
            Op::BvExtract(_start, _end) => {}
            _ => panic!("Non-field in embed_bv: {:?}", t),
        }
    }

    fn embed(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
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
    }

    /// Given a term `t`, lower `t` to ABY Circuits
    fn lower(&mut self, t: Term) {
        self.embed(t.clone());

        let op = "OUT";
        let s = self.term_to_share_cnt.get(&t).unwrap();
        let line = format!("1 0 {} {}\n", s, op);
        write_line_to_file(&self.bytecode_path, &line);
    }
}

/// Convert this (IR) `ir` to ABY.
pub fn to_aby(ir: Computation, path: &Path, lang: &str, cm: &str) {
    let Computation { outputs: terms, .. } = ir.clone();

    #[cfg(feature = "lp")]
    let s_map: SharingMap = assign(&ir, cm);
    #[cfg(not(feature = "lp"))]
    let s_map: SharingMap = some_arith_sharing(&ir, cm);

    let mut converter = ToABY::new(s_map, path, lang);

    for t in terms {
        // println!("terms: {}", t);
        converter.map_terms_to_shares(t.clone());
        converter.write_mapping_file(t.clone());
        converter.lower(t.clone());
    }
}
