//! Translation from IR to Chaco file input format
//! This input format can be found in [Jostle User Guide](https://chriswalshaw.co.uk/jostle/jostle-exe.pdf)
//!
//!

use crate::ir::term::*;
use std::collections::HashMap;
use std::fs;
use std::io::prelude::*;
use std::path::Path;
use std::path::PathBuf;

#[derive(Clone, Hash, Eq)]
struct Node {
    idx: usize,
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.idx == other.idx
    }
}

struct ToChaco {
    num_nodes: usize,
    num_edges: usize,
    next_idx: usize,
    term_to_node: HashMap<Term, Node>,
    edges: HashMap<Node, Vec<Node>>,
}

impl ToChaco {
    fn new() -> Self {
        Self {
            num_nodes: 0,
            num_edges: 0,
            next_idx: 1,
            term_to_node: HashMap::new(),
            edges: HashMap::new(),
        }
    }

    fn insert_node(&mut self, t: &Term) {
        if !self.term_to_node.contains_key(t) {
            let new_node = Node { idx: self.next_idx };
            self.term_to_node.insert(t.clone(), new_node);
            self.next_idx += 1;
            self.num_nodes += 1;
        }
    }

    fn insert_edge(&mut self, from: &Term, to: &Term) {
        self.insert_node(&from);
        self.insert_node(&to);

        let from_node = self.term_to_node.get(&from).unwrap().clone();
        let to_node = self.term_to_node.get(&to).unwrap().clone();

        if !self.edges.contains_key(&from_node) {
            self.edges.insert(from_node.clone(), Vec::new());
        }
        self.edges.get_mut(&from_node).unwrap().push(to_node);
        self.num_edges += 1;
    }

    fn embed(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
            match &c.op {
                Op::Var(_, _) | Op::Const(_) => {
                    self.insert_node(&c);
                }
                Op::Ite | Op::BvBinPred(_) => {
                    for cs in c.cs.iter() {
                        self.insert_edge(&cs, &c);
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", c, c.op),
            }
        }
    }

    fn convert(&mut self, t: Term) {
        self.embed(t.clone());
    }

    fn get_output_path(&self, path_buf: &PathBuf, lang: &String) -> String {
        let filename = Path::new(&path_buf.iter().last().unwrap().to_os_string())
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        let name = format!("{}_{}", filename, lang);
        let path = format!("third_party/ABY/src/examples/{}_graph.txt", name);
        if Path::new(&path).exists() {
            fs::remove_file(&path).expect("Failed to remove old graph file");
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
        file.write_all(format!("{} {}\n", self.num_nodes, self.num_edges).as_bytes())
            .expect("Failed to write to graph file");

        // for Nodes 1..N, write their neighbors
        for i in 0..(self.num_nodes) {
            let node = Node {
                idx: i+1
            };
            
            match self.edges.get(&node) {
                Some(edges) => {
                    let line = edges.into_iter().map(|node| node.idx.to_string()).collect::<Vec<String>>().join(" ");
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
}

/// Convert this (IR) constraint system `cs` to the Chaco file
/// input format.
/// Write the result to the input file path.
pub fn to_chaco(cs: &Computation, output_path: &PathBuf, lang: &String) {
    println!("Writing IR to Chaco format");
    let Computation { outputs, .. } = cs.clone();
    let mut converter = ToChaco::new();
    for t in outputs {
        converter.convert(t);
    }
    let path = converter.get_output_path(output_path, lang);
    converter.write_graph(&path);
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn sample_test() {
        // Millionaire's example
        let cs = Computation {
            outputs: vec![
                term![ITE;
                term![BV_ULT;
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("b".to_owned(), Sort::BitVector(32)))],
                leaf_term(Op::Var("a".to_owned(), Sort::BitVector(32))),
                leaf_term(Op::Var("b".to_owned(), Sort::BitVector(32)))],
            ],
            metadata: ComputationMetadata::default(),
            values: None,
        };
        let Computation { outputs, .. } = cs.clone();
        let mut converter = ToChaco::new();
        for t in outputs {
            converter.convert(t);
        }
        assert_eq!(converter.num_nodes, 4);
        assert_eq!(converter.num_edges, 5);
    }
}

