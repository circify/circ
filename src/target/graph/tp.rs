//! Multi-level Partitioning Implementation
//!
//!

use crate::ir::opt::link::link_one;
use crate::ir::term::*;

use crate::target::aby::assignment::def_uses::*;
use crate::target::graph::utils::graph_utils::*;
use crate::target::graph::utils::part::*;

use std::collections::HashMap;

pub struct TrivialPartition {
    partitioner: Partitioner,
    gwriter: GraphWriter,
    fs: Functions,
    comp_history: HashMap<String, Computation>,
}

impl TrivialPartition {
    pub fn new(fs: &Functions, time_limit: usize, imbalance: usize, hyper_mode: bool) -> Self {
        let mut tp = Self {
            partitioner: Partitioner::new(time_limit, imbalance, hyper_mode),
            gwriter: GraphWriter::new(hyper_mode),
            fs: fs.clone(),
            comp_history: HashMap::new(),
        };
        for fname in fs.computations.keys() {
            tp.traverse(fname);
        }
        tp
    }

    /// traverse the comp and combine
    fn traverse(&mut self, fname: &String) {
        if !self.comp_history.contains_key(fname) {
            let mut c = self.fs.get_comp(fname).unwrap().clone();
            let mut cnt = 0;
            for t in c.terms_postorder() {
                if let Op::Call(callee, ..) = &t.op {
                    self.traverse(callee);
                }
            }
            self.merge(&mut c);
            self.comp_history.insert(fname.into(), c);
        }
    }

    fn merge(&mut self, computation: &mut Computation) {
        let mut cache = TermMap::<Term>::new();
        let mut children_added = TermSet::new();
        let mut stack = Vec::new();
        stack.extend(computation.outputs.iter().cloned());
        while let Some(top) = stack.pop() {
            if !cache.contains_key(&top) {
                // was it missing?
                if children_added.insert(top.clone()) {
                    stack.push(top.clone());
                    stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
                } else {
                    let get_children = || -> Vec<Term> {
                        top.cs
                            .iter()
                            .map(|c| cache.get(c).unwrap())
                            .cloned()
                            .collect()
                    };
                    let new_t_opt = self.visit(computation, &top, get_children);
                    let new_t = new_t_opt.unwrap_or_else(|| term(top.op.clone(), get_children()));
                    cache.insert(top.clone(), new_t);
                }
            }
        }
        computation.outputs = computation
            .outputs
            .iter()
            .map(|o| cache.get(o).unwrap().clone())
            .collect();
    }

    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if let Op::Call(fn_name, arg_names, _, _) = &orig.op {
            // println!("Rewritten children: {:?}", rewritten_children());
            let callee = self
                .comp_history
                .get(fn_name)
                .expect("missing inlined callee");
            let term = link_one(arg_names, rewritten_children(), callee);
            Some(term)
        } else {
            None
        }
    }

    pub fn inline_all(&mut self, fname: &String) -> (Computation, DefUsesGraph) {
        let c = self.comp_history.get(fname).unwrap().clone();
        let dug = DefUsesGraph::new(&c);
        (c, dug)
    }

    pub fn run(
        &mut self,
        fname: &String,
        path: &String,
        ps: usize,
    ) -> (Computation, DefUsesGraph, TermMap<usize>, usize) {
        let mut part_map = TermMap::new();
        self.traverse(fname);
        let c = self.comp_history.get(fname).unwrap();
        let dug = DefUsesGraph::new(&c);
        let num_parts = dug.good_terms.len() / ps + 1;
        println!("LOG: Number of Partitions: {}", num_parts);
        if num_parts > 1 {
            let t_map = self.gwriter.build_from_dug(&dug);
            self.gwriter.write(path);
            let partition = self.partitioner.do_partition(path, &num_parts);
            for (t, tid) in t_map.iter() {
                part_map.insert(t.clone(), *partition.get(tid).unwrap());
            }
        }
        (
            self.comp_history.get(fname).unwrap().clone(),
            dug,
            part_map,
            num_parts,
        )
    }

    pub fn run_from_dug(
        &mut self,
        fname: &String,
        dug: &DefUsesGraph,
        path: &String,
        ps: usize,
    ) -> (TermMap<usize>, usize) {
        let mut part_map = TermMap::new();
        let c = self.fs.get_comp(fname);
        let num_parts = dug.good_terms.len() / ps + 1;
        println!("LOG: Number of Partitions: {}", num_parts);
        if num_parts > 1 {
            let t_map = self.gwriter.build_from_dug(&dug);
            self.gwriter.write(path);
            let partition = self.partitioner.do_partition(path, &num_parts);
            for (t, tid) in t_map.iter() {
                part_map.insert(t.clone(), *partition.get(tid).unwrap());
            }
        }
        (part_map, num_parts)
    }
}
