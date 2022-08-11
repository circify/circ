//! Multi-level Partitioning Implementation
//!
//!

use crate::ir::term::*;

use crate::target::graph::utils::graph_utils::*;
use crate::target::graph::utils::part::*;

use std::collections::HashMap;

pub struct CoarsenMap {
    num_nodes: usize,
    num_edges: usize,
    num_hyper_edges: usize,
    next_idx: usize,
    hyper_mode: bool,
    coarsen_level: usize,
    coarsen_map: HashMap<Term, Vec<usize>>,
    num_nodes_per_level: Vec<usize>,
}

impl CoarsenMap {
    fn new() -> Self {
        let mut g = Self {
            num_nodes: 0,
            num_edges: 0,
            num_hyper_edges: 0,
            coarsen_map: HashMap::new(),
            next_idx: 0,
            hyper_mode: false,
            coarsen_level: 0,
            num_nodes_per_level: Vec::new(),
        };
        g.num_nodes_per_level.push(0);
        g
    }

    /// add a node to current coarsen map
    /// Nodes added by this function are not coarsened
    fn add_node_to_coarsen_map(&mut self, t: &Term) {
        self.num_nodes_per_level[0] += 1;
        self.num_nodes += 1;
        let node_id = self.num_nodes_per_level[0];
        let v = vec![node_id];
        self.coarsen_map.insert(t.clone(), v);
    }

    /// merge callee's coarsen map to caller's
    fn merge_coarsen_map(&mut self, g: &CoarsenMap, sub_map: &TermMap<Term>) {
        // extend the coarsen level if needed
        if g.coarsen_level > self.coarsen_level {
            for _ in self.coarsen_level..g.coarsen_level {
                self.num_nodes_per_level.push(self.num_nodes);
            }
            self.coarsen_level = g.coarsen_level;
        }

        // merge the map into
        for (t, v) in g.coarsen_map.iter() {
            let new_t = sub_map.get(t).unwrap();
            let new_v: Vec<usize> = (0..v.len())
                .map(|i| v[i] + self.num_nodes_per_level[i])
                .collect();
            self.coarsen_map.insert(new_t.clone(), new_v);
            self.num_nodes += 1;
        }

        // update the number of nodes of each level
        for i in 0..g.coarsen_level {
            self.num_nodes_per_level[i] += g.num_nodes_per_level[i];
        }
    }
}

pub struct MultiLevelPartition {
    partitioner: Partitioner,
    gwriter: GraphWriter,
    fs: Functions,
    comp_history: HashMap<String, Computation>,
    graph_history: HashMap<String, CoarsenMap>,
    func_comp_size: HashMap<String, usize>,
    coarsen_threshold: usize,
    num_coarsen_node: usize,
    path: String,
    hyper_mode: bool,
}

impl MultiLevelPartition {
    pub fn new(
        fs: &Functions,
        coarsen_threshold: usize,
        num_coarsen_node: usize,
        path: &String,
        time_limit: usize,
        imbalance: usize,
        hyper_mode: bool,
    ) -> Self {
        let mlp = Self {
            partitioner: Partitioner::new(time_limit, imbalance, hyper_mode),
            gwriter: GraphWriter::new(hyper_mode),
            fs: fs.clone(),
            comp_history: HashMap::new(),
            graph_history: HashMap::new(),
            func_comp_size: HashMap::new(),
            coarsen_threshold: coarsen_threshold,
            num_coarsen_node: num_coarsen_node,
            path: path.clone(),
            hyper_mode: hyper_mode,
        };
        mlp
    }

    /// muti-level coarsening
    fn multilevel_coarsen(&mut self, fname: &String) -> bool {
        let mut coarsened = false;
        if !self.comp_history.contains_key(fname) {
            let c = self.fs.get_comp(fname).unwrap().clone();
            let mut cnt = 0;
            for t in c.terms_postorder() {
                if let Op::Call(callee, ..) = &t.op {
                    coarsened |= self.multilevel_coarsen(callee);
                    cnt += self.func_comp_size.get(callee).unwrap();
                } else {
                    cnt += 1;
                }
            }

            let (new_c, new_g) = self.merge_and_graph(fname);
            self.comp_history.insert(fname.into(), new_c);
            self.graph_history.insert(fname.into(), new_g);

            if cnt > self.coarsen_threshold {
                // perform coarsened
                coarsened = true;
                self.coarsening_by_partition(fname);
            }
        }
        coarsened
    }

    fn coarsening_by_partition(&mut self, fname: &String) {
        let mut t_map: TermMap<usize> = TermMap::new();
        let cm = self.graph_history.get_mut(fname).unwrap();
        let cs = self.comp_history.get(fname).unwrap();
        let num_nodes = cm.num_nodes_per_level.get(0).unwrap().clone();

        for (t, v) in cm.coarsen_map.iter() {
            t_map.insert(t.clone(), v.get(0).unwrap().clone());
        }

        let mut gw: GraphWriter = GraphWriter::new(self.hyper_mode);
        gw.build_from_tm(cs, &t_map, num_nodes);
        let coarsen_graph_path =
            format!("{}.{}.coarsen{}.graph", self.path, fname, cm.coarsen_level);
        gw.write(&coarsen_graph_path);
        let num_parts = num_nodes / self.num_coarsen_node;
        let partition = self
            .partitioner
            .do_partition(&coarsen_graph_path, &num_parts);
        cm.num_nodes_per_level.insert(0, num_parts);

        let tmp = cm.coarsen_map.clone();
        for t in tmp.keys() {
            let mut v = cm.coarsen_map.get_mut(t).unwrap();
            let tid = t_map.get(t).unwrap();
            v.insert(0, partition.get(tid).unwrap().clone());
        }
    }

    /// Merge the function call inside this function and generate graph
    fn merge_and_graph(&mut self, fname: &str) -> (Computation, CoarsenMap) {
        let mut cache = TermMap::<Term>::new();
        let mut children_added = TermSet::new();
        let mut is_arg = TermSet::new();
        let mut stack = Vec::new();
        let mut caller = self.fs.get_comp(fname).unwrap().clone();
        let mut g = CoarsenMap::new();
        stack.extend(caller.outputs.iter().cloned());
        // let coarsened = self.graph_history.contains_key(fname);
        while let Some(top) = stack.pop() {
            if !cache.contains_key(&top) {
                // was it missing?
                if children_added.insert(top.clone()) {
                    stack.push(top.clone());
                    stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
                    if let Op::Call(..) = &top.op {
                        is_arg.extend(top.cs.iter().cloned());
                    }
                } else {
                    let get_children = || -> Vec<Term> {
                        top.cs
                            .iter()
                            .map(|c| cache.get(c).unwrap())
                            .cloned()
                            .collect()
                    };
                    if let Op::Call(fn_name, arg_names, _, _) = &top.op {
                        let callee = self
                            .comp_history
                            .get(fn_name)
                            .expect("missing inlined callee");
                        let coarsened = self.graph_history.contains_key(fn_name);

                        let (new_t, sub_map) = link_one_sub(arg_names, get_children(), callee);

                        if coarsened {
                            // coarsened function, take care of mapping
                            let callee_g = self.graph_history.get(fn_name).unwrap();
                            cache.insert(top.clone(), new_t.clone());
                            g.merge_coarsen_map(&callee_g, &sub_map);
                            g.add_node_to_coarsen_map(&new_t);
                        } else {
                            cache.insert(top.clone(), new_t.clone());
                            stack.push(new_t.clone());
                        }
                    } else {
                        let new_t = term(top.op.clone(), get_children());
                        // arg nodes will be handle later by call node
                        if !is_arg.contains(&top) {
                            g.add_node_to_coarsen_map(&new_t);
                        }
                        cache.insert(top.clone(), new_t);
                    }
                }
            }
        }
        caller.outputs = caller
            .outputs
            .iter()
            .map(|o| cache.get(o).unwrap().clone())
            .collect();
        (caller, g)
    }

    fn multilevel_uncoarsen(
        &mut self,
        fname: &String,
        partition: &HashMap<usize, usize>,
        num_parts: usize,
    ) -> TermMap<usize> {
        let cm = self.graph_history.get(fname).unwrap();
        let cs = self.comp_history.get(fname).unwrap();
        let mut cur_part = partition.clone();
        for l in 1..cm.coarsen_level {
            let mut gw: GraphWriter = GraphWriter::new(self.hyper_mode);
            gw.build(
                cs,
                &cm.coarsen_map,
                l,
                cm.num_nodes_per_level.get(l).unwrap().clone(),
            );
            let part_graph_path = format!("{}.{}.part.graph", self.path, fname);
            let prev_part_path = format!("{}.{}.refine_{}.part", self.path, fname, l);
            gw.write(&part_graph_path);

            // coarsen the partition
            let mut tmp: HashMap<usize, usize> = HashMap::new();
            for (t, v) in cm.coarsen_map.iter() {
                // fix this
                let prev_id = *(v.get(l - 1).unwrap_or_else(|| v.last().unwrap()));
                let cur_id = *(v.get(l).unwrap_or_else(|| v.last().unwrap()));
                tmp.insert(cur_id, cur_part.get(&prev_id).unwrap().clone());
            }
            cur_part = tmp;
            write_partition(&prev_part_path, &cur_part);
            let placeholder = format!("Path_404");
            cur_part = self.partitioner.do_refinement(
                &part_graph_path,
                &prev_part_path,
                &placeholder,
                &num_parts,
            );
        }

        let mut part_result: TermMap<usize> = TermMap::new();
        let finest_l = cm.coarsen_level;
        for (t, v) in cm.coarsen_map.iter() {
            let cur_id = v.get(finest_l).unwrap_or_else(|| v.last().unwrap());
            part_result.insert(t.clone(), cur_part.get(cur_id).unwrap().clone());
        }

        part_result
    }

    pub fn run(
        &mut self,
        fname: &String,
        path: &String,
        num_parts: usize,
    ) -> (Computation, TermMap<usize>) {
        // Coarsening
        self.multilevel_coarsen(fname);

        //  Partition
        let mut t_map: TermMap<usize> = TermMap::new();
        let cm = self.graph_history.get(fname).unwrap();
        let cs = self.comp_history.get(fname).unwrap();
        let num_nodes = cm.num_nodes_per_level.get(0).unwrap().clone();

        for (t, v) in cm.coarsen_map.iter() {
            t_map.insert(t.clone(), v.get(0).unwrap().clone());
        }

        let mut gw: GraphWriter = GraphWriter::new(self.hyper_mode);
        gw.build_from_tm(cs, &t_map, num_nodes);
        let part_graph_path = format!("{}.{}.part.graph", self.path, fname);
        gw.write(&part_graph_path);
        let partition = self.partitioner.do_partition(&part_graph_path, &num_parts);

        // Uncoarsening
        (
            self.comp_history.get(fname).unwrap().clone(),
            self.multilevel_uncoarsen(fname, &partition, num_parts),
        )
    }
}

/// Copy of link_one function with sub_map for coarsen node mapping
fn link_one_sub(
    arg_names: &Vec<String>,
    arg_values: Vec<Term>,
    callee: &Computation,
) -> (Term, TermMap<Term>) {
    let mut sub_map: TermMap<Term> = arg_names
        .into_iter()
        .zip(arg_values)
        .map(|(n, v)| {
            let s = callee.metadata.input_sort(n).clone();
            (leaf_term(Op::Var(n.clone(), s)), v)
        })
        .collect();

    let t = term(
        Op::Tuple,
        callee
            .outputs()
            .iter()
            .map(|o| extras::substitute_cache(o, &mut sub_map))
            .collect(),
    );
    (t, sub_map)
}
