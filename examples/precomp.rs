//! Machinery for Precomputation of Plaintext/Single-Party-Dependent Components
use std::collections::HashMap;
use std::fs;
use std::io::Write;
use circ::ir::term::*;
use circ::ir::term::text::parse_term;

use fxhash::FxHashMap;
use std::path::PathBuf;
use std::path::Path;
use structopt::StructOpt;

#[derive(Debug, StructOpt)]
#[structopt(name = "precomp", about = "Binary for precomputing IRs")]
struct Options {
    /// IR file path
    #[structopt(parse(from_os_str), name = "IR_PATH")]
    ir_path: PathBuf,
    /// Input file path
    #[structopt(parse(from_os_str), name = "INPUT_PATH")]
    inputs_path: PathBuf,
    /// Output file path
    #[structopt(parse(from_os_str), name = "OUTPUT_PATH")]
    outputs_path: PathBuf,
    /// True if we should truncate the output file. False if we should append to the end of it
    #[structopt(short = "f")]
    first_write: bool,
}

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

    fn serialize_value(&self, v: &Value) -> String {
        match v {
            Value::Bool(b) => format!("{}", b),
            Value::BitVector(b) => format!("{}", b.uint()),
            _ => panic!("Unsupported"),
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

    fn write_lines_to_file(&self, path: &str, lines: &[String], first_write: bool) {
        if !Path::new(&path).exists() {
            fs::File::create(&path).expect(&*format!("Failed to create: {}", path));
        }
    
        let data = lines.join("\n");
        let mut file = fs::OpenOptions::new()
            .write(true)
            .truncate(first_write)
            .append(!first_write)
            .open(path)
            .expect("Failed to open circuit_tmp file");
    
        if !first_write {
            file.write("\n".as_bytes())
                .expect("Failed to write to precomp results file");
        }

        file.write_all(data.as_bytes())
            .expect("Failed to write to precomp results file");
    }

    /// Carries out precomputation, saves result in outputs_path
    pub fn precompute(&mut self, ir_path: &Path, inputs_path: &Path, 
                        outputs_path: &Path, first_write: bool) {
        println!("\nInputs: {} - {} - {}",
            ir_path.to_str().expect("ASD"),
            inputs_path.to_str().expect("ASD"),
            outputs_path.to_str().expect("ASD"));
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

        println!("Soon outputing to: {}", outputs_path.to_str().expect("NO"));
        let mut lines = Vec::new();

        for (term, bridge_name) in self.terms.iter() {
            let eval_res = self.serialize_value(&eval(term, &self.hmap));
            println!("{} {}", bridge_name, eval_res);
            lines.push(format!("{} {}", bridge_name, eval_res));
        }
        self.write_lines_to_file(outputs_path.to_str()
            .expect("Unable to parse output path to str"), &lines, first_write);
    }

}



fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
        let options = Options::from_args();

        let mut precomputer = PreComputer::new();
        precomputer.precompute(
            options.ir_path.as_path(), 
            options.inputs_path.as_path(),
            options.outputs_path.as_path(),
            options.first_write
        );
    println!("Precompute binary finished!");
}
//ir_path: "scripts/aby_tests/tests/playground_c_plaintext_ir.txt"
//inputs_path: "scripts/aby_tests/test_inputs/playground.txt"
//outputs_path: "scripts/aby_tests/tests/plaintext_precompute_result.txt"


// ./target/release/examples/precomp scripts/aby_tests/tests/playground_c_plaintext_ir.txt scripts/aby_tests/test_inputs/playground.txt scripts/aby_tests/tests/playground_precompute_result.txt

// ./target/release/examples/precomp scripts/aby_tests/tests/playground_c_party_a_ir.txt scripts/aby_tests/test_inputs/playground.txt scripts/aby_tests/tests/playground_precompute_result.txt

// ./target/release/examples/precomp scripts/aby_tests/tests/playground_c_party_b_ir.txt scripts/aby_tests/test_inputs/playground.txt scripts/aby_tests/tests/playground_precompute_result.txt