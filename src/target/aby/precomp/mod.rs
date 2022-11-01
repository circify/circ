//! Machinery for Precomputation of Plaintext/Single-Party-Dependent Components
use std::collections::HashMap;
use std::fs;

use fxhash::FxHashMap;

use crate::{ir::{term::{*, text::parse_term}}, target::aby::utils::write_lines_to_file};

// #[derive(Debug, StructOpt)]
// #[structopt(name = "precomp", about = "Binary for precomputing IRs")]
// struct Options {
//     /// Input file
//     #[structopt(parse(from_os_str), name = "INPUT_PATH")]
//     input_path: PathBuf,
//     /// IR file
//     #[structopt(parse(from_os_str), name = "IR_PATH")]
//     ir_path: PathBuf,
// }

/// Precomputes an IR based on inputs
pub struct PreComputer {
    terms: TermMap<String>,
    var_set: HashMap<String, Term>,
    hmap: FxHashMap<String, Value>,
}

impl PreComputer {
    /// Intantiates a new PreComputer
    pub fn new() -> Self {
        Self {
            terms: TermMap::new(),
            var_set: HashMap::new(),
            hmap: FxHashMap::default(),
        }
    }

    //From ToABY
    fn get_var_name(&self, t: &Term) -> String {
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

    fn parse_ir(&mut self, src: String) {
        for pair in src.split(",") {
            let p = pair.split(":").collect::<Vec<&str>>();
            if p[0].len() == 0 {
                break; //Dealing with final trailing comma
            }
            let term = parse_term(p[1].as_bytes());
            for c in PostOrderIter::new(term.clone()) {
                match &c.op {
                    Op::Var(..) => {
                        self.var_set.insert(self.get_var_name(&c),c);
                    }
                    _ => {}
                }
            }
            self.terms.insert(term, p[0].to_string());
        }
    }

    fn fill_hmap(&mut self, inputs: String) {
        for line in inputs.split("\n") {
            let split:Vec<&str> = line.split(" ").collect();
            let var_name = split[0].to_string();
            match self.var_set.get(&var_name) {
                None => {
                    //Do nothing, as this is an input unused in this precomp
                }
                Some(var_term) => {
                    match &var_term.op {
                        Op::Var(name, var_sort) => {
                            let full_name = name.to_string();
                            match var_sort {
                                Sort::BitVector(..) => {
                                    let input = split[1].parse().expect("Wanted an bitvector input");
                                    self.hmap.insert(full_name, Value::BitVector(BitVector::new(input, 32)));
                                }
                                Sort::F32 => {
                                    let input = split[1].parse().expect("Wanted an f32 input");
                                    self.hmap.insert(full_name, Value::F32(input));
                                }
                                Sort::F64 => {
                                    let input = split[1].parse().expect("Wanted an f64 input");
                                    self.hmap.insert(full_name, Value::F64(input));
                                }
                                Sort::Int => {
                                    let input = split[1].parse().expect("Wanted an Int input");
                                    self.hmap.insert(full_name, Value::Int(input));
                                }
                                Sort::Bool => {
                                    let input = split[1].parse().expect("Wanted an Bool input");
                                    self.hmap.insert(full_name, Value::Bool(input));
                                }
                                _ => {
                                    panic!("Unimplemented");
                                }
                            }
                        }
                        _ => {
                            panic!("Expected Variable Term")
                        }
                    }
                    
                }
            }
        }
    }


    /// Carries out precomputation, saves result in output_path
    pub fn precompute(&mut self, ir_path: &str, inputs_path: &str, output_path: &str) {
        let ir_string = fs::read_to_string(ir_path)
            .expect("unable to read from file");
        let inputs_string = fs::read_to_string(inputs_path)
            .expect("unable to read from file");

        self.parse_ir(ir_string);
        self.fill_hmap(inputs_string);
        
        println!("\nIn precomp: terms list.");
        for (key, value) in self.terms.iter() {
            println!("{} / {}", key, value);
        }
        println!("\nIn precomp: var set");
        for (key, value) in self.var_set.iter() {
            println!("{} / {}", key, value);
        }
        println!("\nIn precomp: hmap");
        for (key, value) in self.hmap.iter() {
            println!("{} / {}", key, value);
        }

        
        println!("Soon outputing to: {}", output_path);
        let mut lines = Vec::new();

        for (term, bridge_name) in self.terms.iter() {
            lines.push(format!("{} {}\n", bridge_name, eval(term, &self.hmap)));
        }
        write_lines_to_file(output_path, &lines);
    }

}



// fn main() {
//     //Will need this fn when we convert to excecutable
//     //Get filepaths from command line

//     //Initialize precomputer
//     //run precompute
// }