//! Lowering IR to FHE

//use crate::front::datalog::Inputs;
use crate::ir::term::*;
use crate::target::fhe::utils::*;
use std::path::Path;

#[derive(Clone)]
enum EmbeddedTerm {
    Bool,
    Bv,
    Arr,
}

struct ToFHE {
    md: ComputationMetadata,
    inputs: TermSet,
    cache: TermMap<EmbeddedTerm>,
    term_to_stext_cnt: TermMap<i32>,
    stext_cnt: i32,
    bytecode_path: String,
    bytecode_output: Vec<String>,
}

impl ToFHE {
    fn new(md: ComputationMetadata, path: &Path, lang: &str) -> Self {
        Self {
            md,
            inputs: TermSet::new(),
            cache: TermMap::new(),
            term_to_stext_cnt: TermMap::new(),
            stext_cnt: 0,
            bytecode_path: get_path(path, lang, "bytecode"),
            bytecode_output: Vec::new(),
        }
    }

    fn map_terms_to_shares(&mut self, term_: Term) {
        for t in PostOrderIter::new(term_) {
            self.term_to_stext_cnt.insert(t, self.stext_cnt);
            self.stext_cnt += 1;
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

    fn unwrap_vis(&self, name: &str) -> u8 {
        match self.md.input_vis.get(name).unwrap() {
            Some(_) => 1,
            None => 0,
        }
    }

    fn embed_eq(&mut self, t: Term, a_term: Term, b_term: Term) {
        let s = self.term_to_stext_cnt.get(&t).unwrap();
        let a = self.term_to_stext_cnt.get(&t.cs[0]).unwrap();
        let b = self.term_to_stext_cnt.get(&t.cs[1]).unwrap();
        let op;
        match check(&a_term) {
            Sort::Bool => {
                self.check_bool(&a_term);
                self.check_bool(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool);
                op = "B_EQ";
            }
            Sort::BitVector(_) => {
                self.check_bv(&a_term);
                self.check_bv(&b_term);
                self.cache.insert(t, EmbeddedTerm::Bool);
                op = "V_EQ";
            }
            e => panic!("Unimplemented sort for Eq: {:?}", e),
        }
        let line = format!("2 1 {} {} {} {}\n", a, b, s, op);
        self.bytecode_output.push(line);
    }

    /// Given term `t`, type-check `t` is of type Bool
    fn check_bool(&self, t: &Term) {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing expression for {:?}", t))
        {
            EmbeddedTerm::Bool => (),
            _ => panic!("Check_bool failed"),
        };
    }

    fn embed_bool(&mut self, t: Term) {
        let s = self.term_to_stext_cnt.get(&t).unwrap();
        match &t.op {
            Op::Var(name, Sort::Bool) => {
                // write to bytecode file
                if !self.inputs.contains(&t) && self.md.input_vis.contains_key(name) {
                    let term_name = ToFHE::get_var_name(&t);
                    let enc = self.unwrap_vis(name);
                    let op = "IN";

                    let line = format!("2 1 {} {} {} {}\n", term_name, enc, s, op);
                    self.bytecode_output.insert(0, line);
                    self.inputs.insert(t.clone());
                }
                if !self.cache.contains_key(&t) {
                    self.cache.insert(t.clone(), EmbeddedTerm::Bool);
                }
            }
            Op::Const(Value::Bool(b)) => {
                let op = "CONS";
                let line = format!("1 1 {} {} {}\n", *b as i32, s, op);
                self.bytecode_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            Op::Eq => {
                self.embed_eq(t.clone(), t.cs[0].clone(), t.cs[1].clone());
            }
            Op::Ite => {
                unimplemented!("Bool Ite unimplemented");
            }
            Op::Not => {
                let op = "NOT";

                self.check_bool(&t.cs[0]);

                let a = self.term_to_stext_cnt.get(&t.cs[0]).unwrap();
                let line = format!("1 1 {} {} {}\n", a, s, op);
                self.bytecode_output.push(line);

                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            Op::BoolNaryOp(o) => {
                self.bytecode_output.push(format!("{} 1", t.cs.len()));

                for cterm in &t.cs {
                    self.check_bool(cterm);
                    self.bytecode_output
                        .push(format!(" {}", self.term_to_stext_cnt.get(cterm).unwrap()));
                }

                let op = match o {
                    BoolNaryOp::Or => "B_OR",
                    BoolNaryOp::And => "B_AND",
                    BoolNaryOp::Xor => "B_XOR",
                };

                self.bytecode_output.push(format!(" {} {}\n", s, op));

                self.cache.insert(t.clone(), EmbeddedTerm::Bool);
            }
            _ => panic!("Non-field in embed_bool: {:?}", t),
        }
    }

    /// Given term `t`, type-check `t` is of type Bv
    fn check_bv(&self, t: &Term) {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing expression for {:?}", t))
        {
            EmbeddedTerm::Bv => (),
            _ => panic!("Check_bv failed"),
        };
    }

    fn embed_bv(&mut self, t: Term) {
        let s = self.term_to_stext_cnt.get(&t).unwrap();
        match &t.op {
            Op::Var(name, Sort::BitVector(_)) => {
                // write to bytecode file
                if !self.inputs.contains(&t) && self.md.input_vis.contains_key(name) {
                    let term_name = ToFHE::get_var_name(&t);
                    let enc = self.unwrap_vis(name);
                    let op = "IN";

                    let line = format!("2 1 {} {} {} {}\n", term_name, enc, s, op);
                    self.bytecode_output.insert(0, line);
                    self.inputs.insert(t.clone());
                }
                if !self.cache.contains_key(&t) {
                    self.cache.insert(t.clone(), EmbeddedTerm::Bv);
                }
            }
            Op::Const(Value::BitVector(b)) => {
                let op = "CONS";
                let line = format!("1 1 {} {} {}\n", b.as_sint(), s, op);
                self.bytecode_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            Op::BvNaryOp(o) => {
                self.bytecode_output.push(format!("{} 1", t.cs.len()));

                for cterm in &t.cs {
                    self.check_bv(cterm);
                    self.bytecode_output
                        .push(format!(" {}", self.term_to_stext_cnt.get(cterm).unwrap()));
                }

                let op = match o {
                    BvNaryOp::Xor => "V_XOR",
                    BvNaryOp::Or => "V_OR",
                    BvNaryOp::And => "V_AND",
                    BvNaryOp::Add => "ADD",
                    BvNaryOp::Mul => "MUL",
                };

                self.bytecode_output.push(format!(" {} {}\n", s, op));

                self.cache.insert(t.clone(), EmbeddedTerm::Bv);
            }
            _ => {
                panic!("Non-field in embed_bv: {:?}", t);
            }
        }
    }

    // Given term `t`, type-check `t` is of type arr
    fn check_arr(&self, t: &Term) {
        match self
            .cache
            .get(t)
            .unwrap_or_else(|| panic!("Missing expression for {:?}", t))
        {
            EmbeddedTerm::Arr => (),
            _ => panic!("Check_arr failed"),
        };
    }

    fn embed_arr(&mut self, t: Term) {
        let s = self.term_to_stext_cnt.get(&t).unwrap();
        match &t.op {
            Op::Var(name, Sort::Array(_, _, len)) => {
                // write to bytecode file
                if !self.inputs.contains(&t) && self.md.input_vis.contains_key(name) {
                    let term_name = ToFHE::get_var_name(&t);
                    let enc = self.unwrap_vis(name);
                    let op = "ARR_IN";

                    let line = format!("3 1 {} {} {} {} {}\n", term_name, enc, len, s, op);
                    self.bytecode_output.insert(0, line);
                }
                if !self.cache.contains_key(&t) {
                    self.cache.insert(t.clone(), EmbeddedTerm::Arr);
                }
            }
            Op::Const(Value::Array(arr)) => {
                self.bytecode_output.push(format!("{} 1", arr.size));

                for ival in arr.key_sort.elems_iter_values().take(arr.size) {
                    let val = arr.select(&ival);
                    if let Value::Array(_) = val.clone() {
                        panic!("Const arr does not support multi-dim arrays")
                    }
                    self.bytecode_output.push(format!(" {}", val));
                }

                let op = "ARR_CONS";
                let line = format!("{} {}\n", s, op);
                self.bytecode_output.push(line);
                self.cache.insert(t.clone(), EmbeddedTerm::Arr);
            }
            Op::Map(op) => {
                self.bytecode_output.push(format!("{} 1", t.cs.len()));
                for cterm in &t.cs {
                    self.check_arr(cterm);
                    self.bytecode_output
                        .push(format!(" {}", self.term_to_stext_cnt.get(cterm).unwrap()));
                }
                let opstr = match **op {
                    Op::BoolNaryOp(BoolNaryOp::Or) => "B_OR",
                    Op::BoolNaryOp(BoolNaryOp::And) => "B_AND",
                    Op::BoolNaryOp(BoolNaryOp::Xor) => "B_XOR",
                    Op::BvNaryOp(BvNaryOp::Add) => "ADD",
                    Op::BvNaryOp(BvNaryOp::Mul) => "MUL",
                    _ => panic!("Map does not support operation {}", op),
                };
                self.bytecode_output.push(format!(" {} {}\n", s, opstr));
                self.cache.insert(t.clone(), EmbeddedTerm::Arr);
            }
            _ => {
                unimplemented!("Array operation not implemented");
            }
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
                Sort::Array(..) => {
                    self.embed_arr(c);
                }
                e => panic!("Unsupported sort in embed: {:?}", e),
            }
        }
    }

    /// Given a term `t`, lower `t` to FHE program
    fn lower(&mut self, t: Term) {
        self.embed(t.clone());

        match check(&t) {
            Sort::Array(_, _, len) => {
                let op = "ARR_OUT";
                let s = self.term_to_stext_cnt.get(&t).unwrap();
                let line = format!("2 0 {} {} {}\n", s, len, op);
                self.bytecode_output.push(line);
            }
            _ => {
                let op = "OUT";
                let s = self.term_to_stext_cnt.get(&t).unwrap();
                let line = format!("1 0 {} {}\n", s, op);
                self.bytecode_output.push(line);
            }
        }

        // write lines to file
        write_lines_to_file(&self.bytecode_path, &self.bytecode_output);
    }
}

/// Convert this (IR) `ir` to FHE.
pub fn to_fhe(ir: Computation, path: &Path, lang: &str) {
    let Computation {
        outputs: terms,
        metadata: md,
        ..
    } = ir;

    let mut converter = ToFHE::new(md, path, lang);

    for t in terms {
        // println!("Terms: {}", t);
        converter.map_terms_to_shares(t.clone());
        converter.lower(t.clone());
    }
}
