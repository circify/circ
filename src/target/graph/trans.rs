//! Translation from IR to Chaco file input format
//! This input format can be found in [Jostle User Guide](https://chriswalshaw.co.uk/jostle/jostle-exe.pdf)
//!
//!

use crate::ir::term::*;
use crate::target::aby::assignment::ilp::assign;
use crate::target::aby::assignment::SharingMap;
use crate::target::aby::utils::get_aby_source;
use std::collections::HashMap;
use std::fs;
use std::fs::File;
use std::io::prelude::*;
use std::io::{self, BufRead};
use std::path::Path;
use std::path::PathBuf;
use std::process::{Command, Stdio};

#[derive(Clone, PartialEq, Eq, Hash)]
struct Node {
    idx: usize,
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

struct ParitionGraph {
    num_nodes: usize,
    num_edges: usize,
    next_idx: usize,
    partition_size: usize,
    num_parts: usize,
    term_to_node: HashMap<Term, Node>,
    node_to_term: HashMap<Node, Term>,
    term_to_part: HashMap<Term, usize>,
    edges: HashMap<Node, Edges<Node>>,
    cs: Computation,
    cm: String,
    path: PathBuf,
    lang: String,
    graph_path: String,
    part_path: String,
}

impl ParitionGraph {
    fn new(partition_size: usize, cs: &Computation, cm: &str, path: &Path, lang: &str) -> Self {
        let mut graph = Self {
            num_nodes: 0,
            num_edges: 0,
            next_idx: 0,
            partition_size,
            num_parts: 0,
            term_to_node: HashMap::new(),
            node_to_term: HashMap::new(),
            term_to_part: HashMap::new(),
            edges: HashMap::new(),
            cs: cs.clone(),
            cm: cm.to_string(),
            path: PathBuf::from(path),
            lang: lang.to_string(),
            graph_path: "".to_string(),
            part_path: "".to_string(),
        };
        graph.init_paths();
        graph
    }

    // Get file path to write Chaco graph to
    fn get_graph_path(&self) -> String {
        let filename = Path::new(&self.path.iter().last().unwrap().to_os_string())
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        let name = format!("{}_{}", filename, self.lang);
        let path = format!("{}/src/examples/{}.graph", get_aby_source(), name);
        if Path::new(&path).exists() {
            fs::remove_file(&path).expect("Failed to remove old graph file");
        }
        path
    }

    // Get file path to write graph partitioning output to
    fn get_part_path(&self) -> String {
        let filename = Path::new(&self.path.iter().last().unwrap().to_os_string())
            .file_stem()
            .unwrap()
            .to_os_string()
            .into_string()
            .unwrap();
        let name = format!("{}_{}", filename, &self.lang);
        let path = format!("{}/src/examples/{}.part", get_aby_source(), name);
        if Path::new(&path).exists() {
            fs::remove_file(&path).expect("Failed to remove old partition file");
        }
        path
    }

    // Initialize paths to write Chaco graph and partition files
    fn init_paths(&mut self) {
        self.graph_path = self.get_graph_path();
        self.part_path = self.get_part_path();
    }

    // Insert node into PartitionGraph
    fn insert_node(&mut self, t: &Term) {
        if !self.term_to_node.contains_key(t) {
            self.next_idx += 1;
            let new_node = Node { idx: self.next_idx };
            self.term_to_node.insert(t.clone(), new_node.clone());
            self.node_to_term.insert(new_node, t.clone());
            self.num_nodes += 1;
        }
    }

    // Insert edge into PartitionGraph
    fn insert_edge(&mut self, from: &Term, to: &Term) {
        self.insert_node(from);
        self.insert_node(to);

        let from_node = self.term_to_node.get(from).unwrap().clone();
        let to_node = self.term_to_node.get(to).unwrap().clone();

        if !self.edges.contains_key(&from_node) {
            self.edges
                .insert(from_node.clone(), Edges { vec: Vec::new() });
        }
        let added = self.edges.get_mut(&from_node).unwrap().add(to_node);
        if added {
            self.num_edges += 1;
        }
    }

    // Write Chaco graph to file
    fn write_graph(&mut self) {
        if !Path::new(&self.graph_path).exists() {
            fs::File::create(&self.graph_path).expect("Failed to create graph file");
        }
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(&self.graph_path)
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

    // Convert each node to Chaco graph representation
    fn chaco_(&mut self, t: &Term) {
        for c in PostOrderIter::new(t.clone()) {
            match &c.op {
                Op::Var(_, _) | Op::Const(_) => {
                    self.insert_node(&c);
                }
                Op::Ite
                | Op::Not
                | Op::Eq
                | Op::BvBinOp(_)
                | Op::BvNaryOp(_)
                | Op::BvBinPred(_)
                | Op::BoolNaryOp(_) => {
                    for cs in c.cs.iter() {
                        self.insert_edge(cs, &c);
                    }
                    for cs in c.cs.iter().rev() {
                        self.insert_edge(&c, cs);
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", c, c.op),
            }
        }
    }

    // Convert IR to Chaco graph format
    fn chaco(&mut self) {
        println!("Writing IR to Chaco format");
        let Computation { outputs, .. } = self.cs.clone();
        for t in &outputs {
            self.chaco_(t);
        }
        self.write_graph();
        self.get_num_partitions();
    }

    // Determine number of partitions based on the number of terms in the Computation
    fn get_num_partitions(&mut self) {
        self.num_parts = self.num_nodes / self.partition_size + 1;
    }

    // Check if input graph is formatted correctly
    fn check_graph(&self) {
        //TODO: fix path
        let output = Command::new("../KaHIP/deploy/graphchecker")
            .arg(&self.graph_path)
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("The graph format seems correct."));
    }

    // Call graph partitioning algorithm on input graph
    fn call_graph_partitioner(&self) {
        //TODO: fix path
        let output = Command::new("../KaHIP/deploy/kaffpa")
            .arg(&self.graph_path)
            .arg("--k")
            .arg(self.num_parts.to_string()) //TODO: make this a function on the number of terms
            .arg("--preconfiguration=fast")
            .arg(format!("--output_filename={}", &self.part_path))
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        println!("stdout: {}", stdout);
        assert!(stdout.contains(&format!("writing partition to {}", &self.part_path)));
    }

    // Read a file line by line
    fn read_lines<P>(&self, filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
    where
        P: AsRef<Path>,
    {
        let file = File::open(filename)?;
        Ok(io::BufReader::new(file).lines())
    }

    // Partition IR graph into HashMap<usize (part), ComputationSubgraph>
    fn partition_ir(&mut self) -> HashMap<usize, ComputationSubgraph> {
        let mut partitions: HashMap<usize, ComputationSubgraph> = HashMap::new();

        // Initialize partitions
        for part in 0..self.num_parts {
            partitions.insert(part, ComputationSubgraph::new());
        }

        if let Ok(lines) = self.read_lines(&self.part_path) {
            for line in lines.into_iter().enumerate() {
                if let (i, Ok(part)) = line {
                    let node = Node { idx: i + 1 };
                    let term = self.node_to_term.get(&node);
                    let part_num = part.parse::<usize>().unwrap();
                    if let Some(t) = term {
                        if let Some(subgraph) = partitions.get_mut(&part_num) {
                            subgraph.insert_node(t);
                            self.term_to_part.insert(t.clone(), part_num);
                        } else {
                            panic!("Subgraph not found for index: {}", part_num);
                        }
                    } else {
                        panic!("Node: {} - was not mapped in node_to_term map", i + 1);
                    }
                }
            }
        }

        // Find edges for each subgraph
        let mut new_partitions: HashMap<usize, ComputationSubgraph> = HashMap::new();
        for (i, mut subgraph) in partitions.into_iter() {
            subgraph.insert_edges();
            new_partitions.insert(i, subgraph.clone());
        }
        new_partitions
    }

    // Partition IR and get mapping
    fn get_partitions(&mut self) {
        self.check_graph();
        self.call_graph_partitioner();
    }

    // Get Local Assignments for a ComputationSubgraph
    fn get_local_assignments(
        &self,
        cs: &HashMap<usize, ComputationSubgraph>,
    ) -> HashMap<usize, SharingMap> {
        let mut local_smaps: HashMap<usize, SharingMap> = HashMap::new();
        for (i, c) in cs.iter() {
            local_smaps.insert(*i, assign(c, &self.cm));
        }
        local_smaps
    }

    fn get_global_assignments(&self, local_smaps: &HashMap<usize, SharingMap>) -> SharingMap {
        let mut global_smap: SharingMap = SharingMap::new();

        let Computation { outputs, .. } = self.cs.clone();
        for term_ in &outputs {
            for t in PostOrderIter::new(term_.clone()) {
                // get term partition assignment
                let part = self.term_to_part.get(&t).unwrap();

                // get local assignment
                let local_share = local_smaps.get(part).unwrap().get(&t).unwrap();

                // TODO: mutate local assignments

                // assign to global share
                global_smap.insert(t.clone(), *local_share);
            }
        }
        global_smap
    }
}

/// Convert this (IR) constraint system `cs` to the Chaco file
/// input format.
/// Write the result to the input file path.
pub fn get_share_map(cs: &Computation, cm: &str, path: &Path, lang: &str) -> SharingMap {
    //TODO: pass in partition size
    let partition_size: usize = 10000;
    let mut pg = ParitionGraph::new(partition_size, cs, cm, path, lang);

    // Convert IR to Chaco  format
    pg.chaco();

    // Call graph partitioner on Chaco
    pg.get_partitions();

    // Partition IR
    let partitions = pg.partition_ir();

    // get local assignments
    let local_smaps = pg.get_local_assignments(&partitions);

    // TODO: mutate local assignments

    // get global assignments
    pg.get_global_assignments(&local_smaps)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_to_chaco() {
        // Millionaire's example
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
        let mut pg = ParitionGraph::new(2, &cs, "opa", &Path::new("test"), "c");
        pg.chaco();
        assert_eq!(pg.num_nodes, 4);
        assert_eq!(pg.num_edges / 2, 5);
    }
}
