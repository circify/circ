//! Translation from IR to Chaco file input format
//! This input format can be found in [Jostle User Guide](https://chriswalshaw.co.uk/jostle/jostle-exe.pdf)
//!
//!

use crate::ir::term::*;

use crate::target::aby::assignment::ilp::assign_mut;
use crate::target::aby::assignment::ilp::assign_mut_smart;
use crate::target::aby::assignment::ilp::comb_selection;
use crate::target::aby::assignment::ilp::comb_selection_smart;

use crate::target::aby::assignment::SharingMap;
use std::collections::HashMap;

use crate::target::aby::assignment::def_uses::*;

use std::thread;

fn get_outer_n(cs: &ComputationSubgraph, n: usize) -> ComputationSubgraph {
    let mut last_cs = cs.clone();
    for _ in 0..n {
        let mut mut_cs: ComputationSubgraph = ComputationSubgraph::new();
        for node in last_cs.nodes.clone() {
            mut_cs.insert_node(&node);
        }
        for node in last_cs.ins.clone() {
            for outer_node in node.cs.iter() {
                mut_cs.insert_node(&outer_node)
            }
        }
        mut_cs.insert_edges();
        last_cs = mut_cs;
    }
    last_cs
}

/// Mutations with multi threading
fn mutate_partitions_mp_step(
    cs: &HashMap<usize, ComputationSubgraph>,
    cm: &str,
    outer_level: usize,
    step: usize,
) -> HashMap<usize, HashMap<usize, SharingMap>> {
    // TODO: merge and stop
    let mut mut_smaps: HashMap<usize, HashMap<usize, SharingMap>> = HashMap::new();

    let mut mut_sets: HashMap<(usize, usize), (ComputationSubgraph, ComputationSubgraph)> =
        HashMap::new();

    for (i, c) in cs.iter() {
        mut_smaps.insert(*i, HashMap::new());
        for j in 0..outer_level {
            let outer_tmp = get_outer_n(c, j * step);
            mut_sets.insert((*i, j), (outer_tmp.clone(), c.clone()));
        }
    }

    let mut children = vec![];
    let _cm = cm.to_string();

    for ((i, j), (c, c_ref)) in mut_sets.iter() {
        let costm = _cm.clone();
        let i = i.clone();
        let j = j.clone();
        let c = c.clone();
        let c_ref = c_ref.clone();
        children.push(thread::spawn(move || {
            (i, j, assign_mut(&c, &costm, &c_ref))
        }));
    }

    for child in children {
        let (i, j, smap) = child.join().unwrap();
        mut_smaps.get_mut(&i).unwrap().insert(j, smap);
    }
    mut_smaps
}

/// Mutations with multi threading
fn mutate_partitions_mp_step_smart(
    dug: &DefUsesGraph,
    dusg: &HashMap<usize, DefUsesSubGraph>,
    cm: &str,
    outer_level: usize,
    step: usize,
) -> HashMap<usize, HashMap<usize, SharingMap>> {
    // TODO: merge and stop
    let mut mut_smaps: HashMap<usize, HashMap<usize, SharingMap>> = HashMap::new();

    let mut mut_sets: HashMap<(usize, usize), (DefUsesSubGraph, TermSet)> = HashMap::new();

    for (i, du) in dusg.iter() {
        mut_smaps.insert(*i, HashMap::new());
        mut_sets.insert((*i, 0), (du.clone(), du.nodes.clone()));
        let mut old_du = du.clone();
        for j in 0..outer_level {
            old_du = extend_dusg(&old_du, dug);
            println!("Mutation {} for partition {}: {}", i, j, old_du.nodes.len());
            mut_sets.insert((*i, j), (old_du.clone(), du.nodes.clone()));
        }
    }

    let mut children = vec![];
    let _cm = cm.to_string();
    let k_map = dug.get_k();


    for ((i, j), (du, du_ref)) in mut_sets.iter() {
        let costm = _cm.clone();
        let i = i.clone();
        let j = j.clone();
        let du = du.clone();
        let du_ref = du_ref.clone();
        let k_map = k_map.clone();
        children.push(thread::spawn(move || {
            (i, j, assign_mut_smart(&du, &costm, &du_ref, &k_map))
        }));
    }

    for child in children {
        let (i, j, smap) = child.join().unwrap();
        mut_smaps.get_mut(&i).unwrap().insert(j, smap);
    }
    mut_smaps
}

fn get_global_assignments(
    cs: &Computation,
    term_to_part: &TermMap<usize>,
    local_smaps: &HashMap<usize, SharingMap>,
) -> SharingMap {
    let mut global_smap: SharingMap = SharingMap::new();

    let Computation { outputs, .. } = cs.clone();
    for term_ in &outputs {
        for t in PostOrderIter::new(term_.clone()) {
            // get term partition assignment
            let part = term_to_part.get(&t).unwrap();

            // get local assignment
            let local_share = local_smaps.get(part).unwrap().get(&t).unwrap();

            // TODO: mutate local assignments ilp

            // assign to global share
            global_smap.insert(t.clone(), *local_share);
        }
    }
    global_smap
}

fn get_global_assignments_smart(
    dug: &DefUsesGraph,
    term_to_part: &TermMap<usize>,
    local_smaps: &HashMap<usize, SharingMap>,
) -> SharingMap {
    let mut global_smap: SharingMap = SharingMap::new();
    for t in dug.good_terms.iter() {
        // get term partition assignment
        let part = term_to_part.get(&t).unwrap();

        // get local assignment
        let local_share = local_smaps.get(part).unwrap().get(&t).unwrap();

        // assign to global share
        global_smap.insert(t.clone(), *local_share);
    }
    global_smap
}

pub fn get_share_map_with_mutation(
    cs: &Computation,
    cm: &str,
    partitions: &HashMap<usize, ComputationSubgraph>,
    term_to_part: &TermMap<usize>,
    mut_level: &usize,
    mut_step_size: &usize,
) -> SharingMap {
    let mutation_smaps =
        mutate_partitions_mp_step(partitions, cm, mut_level.clone(), mut_step_size.clone());
    let selected_mut_maps = comb_selection(&mutation_smaps, &partitions, cm);
    get_global_assignments(cs, term_to_part, &selected_mut_maps)
}

pub fn get_share_map_with_mutation_smart(
    dug: &DefUsesGraph,
    cm: &str,
    partitions: &HashMap<usize, DefUsesSubGraph>,
    term_to_part: &TermMap<usize>,
    mut_level: &usize,
    mut_step_size: &usize,
) -> SharingMap {
    let mutation_smaps = mutate_partitions_mp_step_smart(
        dug,
        partitions,
        cm,
        mut_level.clone(),
        mut_step_size.clone(),
    );
    let selected_mut_maps = comb_selection_smart(dug, &mutation_smaps, &partitions, cm);
    get_global_assignments_smart(dug, term_to_part, &selected_mut_maps)
}
