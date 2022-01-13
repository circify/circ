//! Translation from IR to Chaco file input format
//! This input format can be found in [Jostle User Guide](https://chriswalshaw.co.uk/jostle/jostle-exe.pdf)
//!
//!

use crate::ir::term::*;
use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::io::{self, BufRead};
use std::path::Path;
use std::path::PathBuf;
use std::process::{Command, Stdio};

#[derive(Clone, Hash, Eq)]
struct Node {
    idx: usize,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
    }
}

#[derive(Clone)]
struct Edges<T> {
    vec: Vec<T>,
}

impl<T: PartialEq> Edges<T> {
    fn add(&mut self, item: T) -> bool {
        if !self.vec.contains(&item) {
            self.vec.push(item);
            return true;
        }
        false
    }
}

struct ToChaco {
    num_nodes: usize,
    num_edges: usize,
    next_idx: usize,
    max_parts: usize,
    term_to_node: HashMap<Term, Node>,
    node_to_term: HashMap<Node, Term>,
    term_to_part: HashMap<Term, usize>,
    edges: HashMap<Node, Edges<Node>>,
}

impl ToChaco {
    fn new() -> Self {
        Self {
            num_nodes: 0,
            num_edges: 0,
            next_idx: 0,
            max_parts: 0,
            term_to_node: HashMap::new(),
            node_to_term: HashMap::new(),
            term_to_part: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    fn insert_node(&mut self, t: &Term) {
        if !self.term_to_node.contains_key(t) {
            self.next_idx += 1;
            let new_node = Node { idx: self.next_idx };
            self.term_to_node.insert(t.clone(), new_node.clone());
            self.node_to_term.insert(new_node, t.clone());
            self.num_nodes += 1;
        }
    }

    fn insert_edge(&mut self, from: &Term, to: &Term) {
        self.insert_node(&from);
        self.insert_node(&to);

        let from_node = self.term_to_node.get(&from).unwrap().clone();
        let to_node = self.term_to_node.get(&to).unwrap().clone();

        if !self.edges.contains_key(&from_node) {
            self.edges
                .insert(from_node.clone(), Edges { vec: Vec::new() });
        }
        let added = self.edges.get_mut(&from_node).unwrap().add(to_node);
        if added {
            self.num_edges += 1;
        }
    }

    fn convert(&mut self, t: &Term) {
        for c in PostOrderIter::new(t.clone()) {
            match &c.op {
                Op::Var(_, _) | Op::Const(_) => {
                    self.insert_node(&c);
                }
                Op::Ite | Op::Eq | Op::BvBinOp(_) | Op::BvNaryOp(_) | Op::BvBinPred(_) => {
                    for cs in c.cs.iter() {
                        self.insert_edge(&cs, &c);
                    }
                    for cs in c.cs.iter().rev() {
                        self.insert_edge(&c, &cs);
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", c, c.op),
            }
        }
    }

    fn get_graph_path(&self, path_buf: &PathBuf, lang: &String) -> String {
        let filename = Path::new(&path_buf.iter().last().unwrap().to_os_string())
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        let name = format!("{}_{}", filename, lang);
        let path = format!("third_party/ABY/src/examples/{}.graph", name);
        if Path::new(&path).exists() {
            fs::remove_file(&path).expect("Failed to remove old graph file");
        }
        path
    }

    fn get_part_path(&self, path_buf: &PathBuf, lang: &String) -> String {
        let filename = Path::new(&path_buf.iter().last().unwrap().to_os_string())
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        let name = format!("{}_{}", filename, lang);
        let path = format!("third_party/ABY/src/examples/{}.part", name);
        if Path::new(&path).exists() {
            fs::remove_file(&path).expect("Failed to remove old partition file");
        }
        path
    }

    fn write_graph(&self, path: &String) {
        if !Path::new(&path).exists() {
            fs::File::create(&path).expect("Failed to create graph file");
        }
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(path)
            .expect("Failed to open graph file");

        // write number of nodes and edges
        file.write_all(format!("{} {}\n", self.num_nodes, self.num_edges / 2).as_bytes())
            .expect("Failed to write to graph file");

        // for Nodes 1..N, write their neighbors
        for i in 0..(self.num_nodes) {
            let node = Node { idx: i + 1 };

            match self.edges.get(&node) {
                Some(edges) => {
                    let line = edges
                        .vec
                        .clone()
                        .into_iter()
                        .map(|node| node.idx.to_string())
                        .collect::<Vec<String>>()
                        .join(" ");
                    file.write_all(line.as_bytes())
                        .expect("Failed to write to graph file");
                }
                None => {
                    let line = "";
                    file.write_all(line.as_bytes())
                        .expect("Failed to write to graph file");
                }
            }
            file.write_all("\n".as_bytes())
                .expect("Failed to write to graph file");
        }
    }

    fn check_graph(&self, graph_path: &String) {
        //TODO: fix path
        let output = Command::new("../KaHIP/deploy/graphchecker")
            .arg(graph_path)
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("The graph format seems correct."));
    }

    fn partition_graph(&self, graph_path: &String, part_path: &String) {
        //TODO: fix path
        let output = Command::new("../KaHIP/deploy/kaffpa")
            .arg(graph_path)
            .arg("--k")
            .arg("4") //TODO: make this a function on the number of terms
            .arg("--preconfiguration=strong")
            .arg(format!("--output_filename={}", part_path))
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains(&format!("writing partition to {}", part_path)));
    }

    fn read_lines<P>(&self, filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
    where
        P: AsRef<Path>,
    {
        let file = File::open(filename)?;
        Ok(io::BufReader::new(file).lines())
    }

    /// Partitioning functions
    fn make_ir_paritition_map(&mut self, path: &String) {
        if let Ok(lines) = self.read_lines(path) {
            // Consumes the iterator, returns an (Optional) String
            for line in lines.into_iter().enumerate() {
                if let (i, Ok(part)) = line {
                    let node = Node { idx: i + 1 };
                    let term = self.node_to_term.get(&node);
                    let part_num = part.parse::<usize>().unwrap();
                    if part_num > self.max_parts {
                        self.max_parts = part_num;
                    }
                    if let Some(t) = term {
                        self.term_to_part.insert(t.clone(), part_num);
                    } else {
                        panic!("Node: {} - was not mapped in node_to_term map", i + 1);
                    }
                }
            }
        }
    }

    fn partition_ir(&self, t: &Term) {
        // return a vector of computations
        for c in PostOrderIter::new(t.clone()) {
            // println!("Term: {}", self.term_to_part.get(&c).unwrap());

            // match &c.op {
            //     Op::Var(_, _) | Op::Const(_) => {
            //         self.insert_node(&c);
            //     }
            //     Op::Ite | Op::Eq | Op::BvBinOp(_) | Op::BvNaryOp(_) | Op::BvBinPred(_) => {
            //         for cs in c.cs.iter() {
            //             self.insert_edge(&cs, &c);
            //         }
            //         for cs in c.cs.iter().rev() {
            //             self.insert_edge(&c, &cs);
            //         }
            //     }
            //     _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", c, c.op),
            // }
        }
    }
}

/// Convert this (IR) constraint system `cs` to the Chaco file
/// input format.
/// Write the result to the input file path.
pub fn partition(cs: &Computation, path: &PathBuf, lang: &String) {
    println!("Writing IR to Chaco format");
    let Computation { outputs, .. } = cs.clone();
    let mut converter = ToChaco::new();
    for t in &outputs {
        converter.convert(t);
    }
    let graph_path = converter.get_graph_path(path, lang);
    converter.write_graph(&graph_path);

    let part_path = converter.get_part_path(path, lang);

    // call partitioner
    converter.check_graph(&graph_path);
    converter.partition_graph(&graph_path, &part_path);

    // read partition
    converter.make_ir_paritition_map(&part_path);

    for t in &outputs {
        converter.partition_ir(t);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sample_test() {
        // Millionaire's example
        let ts = Computation {
            outputs: vec![term![ITE]],
            metadata: ComputationMetadata::default(),
            values: None,
        };
        let cs = Computation {
            outputs: vec![term![ITE;
                term![BV_ULT;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("b".to_owned(), Sort::BitVector(32)))],
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("b".to_owned(), Sort::BitVector(32)))]],
            metadata: ComputationMetadata::default(),
            values: None,
        };
        let Computation { outputs, .. } = cs.clone();
        let mut converter = ToChaco::new();
        for t in &outputs {
            converter.convert(t);
        }
        assert_eq!(converter.num_nodes, 4);
        assert_eq!(converter.num_edges, 5);
    }
}
