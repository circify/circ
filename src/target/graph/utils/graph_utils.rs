//! Translation from IR to Chaco file input format
//! This input format can be found in [Jostle User Guide](https://chriswalshaw.co.uk/jostle/jostle-exe.pdf)
//!
//!
//! 
//! 

use crate::ir::term::*;
use crate::target::aby::assignment::def_uses::*;

use std::collections::HashMap;
use std::fs;
use std::io::prelude::*;
use std::path::Path;

#[derive(Clone, PartialEq, Eq, Hash)]
struct Node {
    idx: usize,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct HyperEdge {
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

fn coarse_map_get(cm: &HashMap<Term, Vec<usize>>, t: &Term ,level: usize) -> usize{
    let v = cm.get(t).unwrap();
    *(v.get(level).unwrap_or_else(|| v.last().unwrap()))
}

pub struct GraphWriter{
    num_nodes: usize,
    num_edges: usize,
    num_hyper_edges: usize,
    term_to_id: HashMap<Term, usize>,
    edges: HashMap<usize, Edges<usize>>,
    hyper_edges: HashMap<HyperEdge, Edges<usize>>,
    node_to_hyper_edge: HashMap<usize, HyperEdge>,
    id_to_part: HashMap<usize, usize>,
    hyper_mode: bool,
}

impl GraphWriter {
    pub fn new(hyper_mode: bool) -> Self{
        let gw = Self {
            num_nodes: 0,
            num_edges: 0,
            num_hyper_edges: 0,
            term_to_id: HashMap::new(),
            edges: HashMap::new(),
            hyper_edges: HashMap::new(),
            id_to_part: HashMap::new(),
            node_to_hyper_edge: HashMap::new(),
            hyper_mode: hyper_mode,
        };
        gw
    }

    pub fn build(&mut self, cs: &Computation, coarsen_map: &HashMap<Term, Vec<usize>>, level: usize, num_nodes: usize){
        self.num_nodes = num_nodes;
        for t in cs.terms_postorder() {
            match &t.op {
                Op::Ite
                | Op::Not
                | Op::Eq
                | Op::Store
                | Op::Select
                | Op::Tuple
                | Op::Field(_)
                | Op::BvBinOp(_)
                | Op::BvNaryOp(_)
                | Op::BvBinPred(_)
                | Op::BoolNaryOp(_) => {
                    let t_id = coarse_map_get(coarsen_map, &t, level);
                    for cs in t.cs.iter() {
                        let cs_id = coarse_map_get(coarsen_map, &cs, level);
                        if cs_id != t_id{
                            if self.hyper_mode{
                                self.insert_hyper_edge(&cs_id, &t_id);
                            } else {
                                self.insert_edge(&cs_id, &t_id);
                                self.insert_edge(&t_id, &cs_id);
                            }
                        }
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", t, t.op),
            }
        }
    }

    pub fn build_from_tm(&mut self, cs: &Computation, tm: &TermMap<usize>, num_nodes: usize){
        self.num_nodes = num_nodes;
        for t in cs.terms_postorder() {
            match &t.op {
                Op::Ite
                | Op::Not
                | Op::Eq
                | Op::Store
                | Op::Select
                | Op::Tuple
                | Op::Field(_)
                | Op::BvBinOp(_)
                | Op::BvNaryOp(_)
                | Op::BvBinPred(_)
                | Op::BoolNaryOp(_) => {
                    let t_id = tm.get(&t).unwrap();
                    for cs in t.cs.iter() {
                        let cs_id = tm.get(&cs).unwrap();
                        if cs_id != t_id{
                            if self.hyper_mode{
                                self.insert_hyper_edge(&cs_id, &t_id);
                            } else {
                                self.insert_edge(&cs_id, &t_id);
                                self.insert_edge(&t_id, &cs_id);
                            }
                        }
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}, {:#?}", t, t.op),
            }
        }
    }

    fn get_tid_or_assign(&mut self, t: &Term) -> usize{
        if self.term_to_id.contains_key(t){
            return *(self.term_to_id.get(t).unwrap());
        } else{
            self.num_nodes += 1;
            self.term_to_id.insert(t.clone(), self.num_nodes);
            return self.num_nodes;
        }
    }

    pub fn build_from_cs(&mut self, cs: &Computation) -> HashMap<Term, usize>{
        for t in cs.terms_postorder() {
            match &t.op {
                Op::Var(_, _) | Op::Const(_) => {
                    self.get_tid_or_assign(&t);
                }
                Op::Ite
                | Op::Not
                | Op::Eq
                | Op::Store
                | Op::Select
                | Op::Tuple
                | Op::Field(_)
                | Op::BvBinOp(_)
                | Op::BvNaryOp(_)
                | Op::BvBinPred(_)
                | Op::BoolNaryOp(_) => {
                    let t_id = self.get_tid_or_assign(&t);
                    for cs in t.cs.iter() {
                        let cs_id = self.get_tid_or_assign(&cs);
                        if cs_id != t_id{
                            if self.hyper_mode{
                                self.insert_hyper_edge(&cs_id, &t_id);
                            } else {
                                self.insert_edge(&cs_id, &t_id);
                                self.insert_edge(&t_id, &cs_id);
                            }
                        }
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}", t.op),
            }
        }
        self.term_to_id.clone()
    }

    pub fn build_from_dug(&mut self, dug: &DefUsesGraph) -> HashMap<Term, usize>{
        for t in dug.good_terms.iter() {
            match &t.op {
                Op::Var(_, _) | Op::Const(_) => {
                    self.get_tid_or_assign(&t);
                }
                Op::Ite
                | Op::Not
                | Op::Eq
                | Op::Store
                | Op::Select
                | Op::Tuple
                | Op::Field(_)
                | Op::BvBinOp(_)
                | Op::BvNaryOp(_)
                | Op::BvBinPred(_)
                | Op::BoolNaryOp(_) => {
                    let t_id = self.get_tid_or_assign(&t);
                    for def in dug.use_defs.get(t).unwrap().iter() {
                        let def_id = self.get_tid_or_assign(&def);
                        if def_id != t_id{
                            if self.hyper_mode{
                                self.insert_hyper_edge(&def_id, &t_id);
                            } else {
                                self.insert_edge(&def_id, &t_id);
                                self.insert_edge(&t_id, &def_id);
                            }
                        }
                    }
                }
                _ => unimplemented!("Haven't  implemented conversion of {:#?}", t.op),
            }
        }
        self.term_to_id.clone()
    }

    pub fn write(&mut self, path: &String){
        if self.hyper_mode{
            self.write_hyper_graph(path);
        } else{
            self.write_graph(path);
        }
    }

    // Insert edge into PartitionGraph
    fn insert_edge(&mut self, from: &usize, to: &usize) {

        if !self.edges.contains_key(&from) {
            self.edges
                .insert(from.clone(), Edges { vec: Vec::new() });
        }
        let added = self.edges.get_mut(&from).unwrap().add(*to);
        if added {
            self.num_edges += 1;
        }
    }

    // Insert hyper edge into PartitionGraph
    fn insert_hyper_edge(&mut self, from: &usize, to: &usize) {

        // Assume each node will only have one output 
        // TODO: fix this?
        if !self.node_to_hyper_edge.contains_key(from) {
            self.num_hyper_edges += 1;

            let new_hyper_edge = HyperEdge {idx: self.num_hyper_edges};
            self.node_to_hyper_edge
                .insert(from.clone(), new_hyper_edge.clone());

            self.hyper_edges
                .insert(new_hyper_edge.clone(), Edges { vec: Vec::new() });
            // Add from node itself
            self.hyper_edges.get_mut(&new_hyper_edge).unwrap().add(*from);
            self.hyper_edges.get_mut(&new_hyper_edge).unwrap().add(*to);
        } else{
            let hyper_edge = self.node_to_hyper_edge.get(&from).unwrap();
            self.hyper_edges.get_mut(&hyper_edge).unwrap().add(*to);
        }
    }

    // Write Chaco graph to file
    fn write_graph(&mut self, path: &String) {
        if !Path::new(path).exists() {
            println!("graph_path: {}", path);
            fs::File::create(path).expect("Failed to create graph file");
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
            let id = i+1;

            match self.edges.get(&id) {
                Some(edges) => {
                    let line = edges
                        .vec
                        .clone()
                        .into_iter()
                        .map(|nid| nid.to_string())
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

    // Write Chaco graph to file
    fn write_hyper_graph(&mut self, path: &String) {
        if !Path::new(path).exists() {
            println!("hyper_graph_path: {}", path);
            fs::File::create(path).expect("Failed to create hyper graph file");
        }
        let mut file = fs::OpenOptions::new()
            .write(true)
            .append(true)
            .open(path)
            .expect("Failed to open hyper graph file");

        // write number of nodes and edges
        file.write_all(format!("{} {}\n", self.num_hyper_edges, self.num_nodes).as_bytes())
            .expect("Failed to write to hyper graph file");

        // for Nodes 1..N, write their neighbors
        for i in 0..(self.num_hyper_edges) {
            let hyper_edge = HyperEdge { idx: i + 1 };

            match self.hyper_edges.get(&hyper_edge) {
                Some(nodes) => {
                    let line = nodes
                        .vec
                        .clone()
                        .into_iter()
                        .map(|nid| nid.to_string())
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
}


pub fn write_partition(path: &String, partition: &HashMap<usize, usize>){
    if !Path::new(path).exists() {
        println!("partition_path: {}", path);
        fs::File::create(path).expect("Failed to create hyper graph file");
    }
    let mut file = fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open(path)
        .expect("Failed to open hyper graph file");

    // for Nodes 1..N, write their neighbors
    for i in 0..partition.keys().len() {

        let line = format!("{}\n", partition.get(&i).unwrap());
        file.write_all(line.as_bytes())
            .expect("Failed to write to graph file");
    }
}