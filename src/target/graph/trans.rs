use crate::ir::term::*;

use crate::target::aby::assignment::get_cost_model;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::assign;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::smart_global_assign;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp::calculate_cost_smart_dug;
#[cfg(feature = "lp")]
use crate::target::aby::assignment::ilp_opa::opa_smart_global_assign;
use crate::target::graph::mlp::*;
use crate::target::graph::tp::*;
#[cfg(feature = "lp")]
use crate::target::graph::utils::mutation::*;

use crate::target::aby::assignment::ShareType;
use crate::target::aby::assignment::SharingMap;

use crate::target::aby::assignment::def_uses::*;

use std::collections::HashMap;
use std::path::Path;
use std::time::Instant;
use std::time::Duration;

use std::fs;

// Get file path to write Chaco graph to
fn get_graph_path(path: &Path, lang: &str, hyper_mode: bool) -> String {
    let filename = Path::new(&path.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap();
    let name = format!("{}_{}", filename, lang);
    let mut path = format!("scripts/aby_tests/tests/{}.graph", name);
    if hyper_mode {
        path = format!("scripts/aby_tests/tests/{}_hyper.graph", name);
    }
    if Path::new(&path).exists() {
        fs::remove_file(&path).expect("Failed to remove old graph file");
    }
    path
}

// #[cfg(feature = "lp")]
// /// inline all function into main
// pub fn partition_with_mut(
//     fs: &Functions,
//     cm: &str,
//     path: &Path,
//     lang: &str,
//     num_parts: &usize,
//     hyper_mode: bool,
//     ml: &usize,
//     mss: &usize,
//     imbalance: &usize,
// ) -> (Functions, HashMap<String, SharingMap>){
//     let mut mlp = MultiLevelPartition::new(
//         fs,
//         20000000,
//         10,
//         path,
//         0,
//         imbalance.clone(),
//         false
//     );
//     let main = "main";
//     let graph_path = get_graph_path(path, lang, hyper_mode);
//     let (c, partition) = mlp.run(&main.to_string(), &graph_path, *num_parts);

//     // Construct ComputationSubgraphs
//     let mut tmp_css: HashMap<usize, ComputationSubgraph> = HashMap::new();
//     let mut css: HashMap<usize, ComputationSubgraph> = HashMap::new();

//     for part_id in 0..*num_parts{
//         tmp_css.insert(part_id, ComputationSubgraph::new());
//     }

//     for (t, part_id) in partition.iter(){
//         if let Some(subgraph) = tmp_css.get_mut(&part_id) {
//             subgraph.insert_node(t);
//         } else {
//             panic!("Subgraph not found for index: {}", num_parts);
//         }
//     }

//     for (part_id, mut cs) in tmp_css.into_iter(){
//         cs.insert_edges();
//         css.insert(part_id, cs.clone());
//     }

//     let assignment = get_share_map_with_mutation(&c, cm, &css, &partition, ml, mss);
//     let mut s_map: HashMap<String, SharingMap> = HashMap::new();
//     s_map.insert(main.to_string(), assignment);
//     let mut fs = Functions::new();
//     fs.insert(main.to_string(), c);
//     (fs, s_map)
// }

#[cfg(feature = "lp")]
/// inline all function into main
pub fn partition_with_mut(
    fs: &Functions,
    cm: &str,
    path: &Path,
    lang: &str,
    ps: &usize,
    hyper_mode: bool,
    ml: &usize,
    mss: &usize,
    imbalance: &usize,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, imbalance.clone(), hyper_mode);
    let main = "main";
    let graph_path = get_graph_path(path, lang, hyper_mode);
    let (c, d, partition, num_parts) = tp.run(&main.to_string(), &graph_path, *ps);

    println!("Time: Partition: {:?}", now.elapsed());
    now = Instant::now();

    // Construct ComputationSubgraphs
    let mut tmp_css: HashMap<usize, ComputationSubgraph> = HashMap::new();
    let mut css: HashMap<usize, ComputationSubgraph> = HashMap::new();

    for part_id in 0..num_parts {
        tmp_css.insert(part_id, ComputationSubgraph::new());
    }

    for (t, part_id) in partition.iter() {
        if let Some(subgraph) = tmp_css.get_mut(&part_id) {
            subgraph.insert_node(t);
        } else {
            panic!("Subgraph not found for index: {}", num_parts);
        }
    }

    for (part_id, mut cs) in tmp_css.into_iter() {
        cs.insert_edges();
        css.insert(part_id, cs.clone());
    }
    println!("Time: To Subgraph: {:?}", now.elapsed());

    now = Instant::now();
    let assignment = get_share_map_with_mutation(&c, cm, &css, &partition, ml, mss);
    println!("Time: ILP : {:?}", now.elapsed());
    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn css_partition_with_mut_smart(
    fs: &Functions,
    dugs: &HashMap<String, DefUsesGraph>,
    cm: &str,
    path: &Path,
    lang: &str,
    ps: &usize,
    hyper_mode: bool,
    ml: &usize,
    mss: &usize,
    imbalance: &usize,
) -> HashMap<String, SharingMap> {
    let mut s_map: HashMap<String, SharingMap> = HashMap::new();

    let mut part_duration: Duration =Duration::ZERO;
    let mut ilp_duration: Duration =Duration::ZERO;

    for (fname, comp) in fs.computations.iter() {
        let mut now = Instant::now();
        println!("Partitioning: {}", fname);
        let mut tp = TrivialPartition::new(fs, 0, imbalance.clone(), hyper_mode);
        let graph_path = get_graph_path(path, lang, hyper_mode);
        let d = dugs.get(fname).unwrap();
        let (partition, num_parts) = tp.run_from_dug(fname, d, &graph_path, *ps);

        part_duration += now.elapsed();

        let mut assignment: SharingMap;
        if num_parts == 1 {
            // No need to partition
            now = Instant::now();
            assignment = smart_global_assign(&d.good_terms, &d.def_use, &d.get_k(), cm);
            ilp_duration += now.elapsed();
        } else {
            // Construct DefUsesSubGraph
            now = Instant::now();
            let mut tmp_dusg: HashMap<usize, DefUsesSubGraph> = HashMap::new();
            let mut dusg: HashMap<usize, DefUsesSubGraph> = HashMap::new();

            for part_id in 0..num_parts {
                tmp_dusg.insert(part_id, DefUsesSubGraph::new());
            }

            for t in d.good_terms.iter() {
                let part_id = partition.get(t).unwrap();
                if let Some(du) = tmp_dusg.get_mut(&part_id) {
                    du.insert_node(t);
                } else {
                    panic!("Subgraph not found for index: {}", num_parts);
                }
            }

            for (part_id, mut du) in tmp_dusg.into_iter() {
                du.insert_edges(&d);
                dusg.insert(part_id, du.clone());
            }
            assignment = get_share_map_with_mutation_smart(&d, cm, &dusg, &partition, ml, mss);

            ilp_duration += now.elapsed();
        }
        s_map.insert(fname.clone(), assignment);
    }

    println!("LOG: Partition time: {:?}", part_duration);
    println!("LOG: ILP time: {:?}", ilp_duration);

    s_map
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn partition_with_mut_smart(
    fs: &Functions,
    cm: &str,
    path: &Path,
    lang: &str,
    ps: &usize,
    hyper_mode: bool,
    ml: &usize,
    mss: &usize,
    imbalance: &usize,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, imbalance.clone(), hyper_mode);
    let main = "main";
    let graph_path = get_graph_path(path, lang, hyper_mode);
    let (c, d, partition, num_parts) = tp.run(&main.to_string(), &graph_path, *ps);

    println!("LOG: Partition time: {:?}", now.elapsed());

    let assignment: SharingMap;
    if num_parts == 1 {
        // No need to partition
        now = Instant::now();
        assignment = smart_global_assign(&d.good_terms, &d.def_use, &d.get_k() , cm);
        println!("LOG: ILP time: {:?}", now.elapsed());
    } else {
        // Construct DefUsesSubGraph
        now = Instant::now();
        let mut tmp_dusg: HashMap<usize, DefUsesSubGraph> = HashMap::new();
        let mut dusg: HashMap<usize, DefUsesSubGraph> = HashMap::new();

        for part_id in 0..num_parts {
            tmp_dusg.insert(part_id, DefUsesSubGraph::new());
        }

        for t in d.good_terms.iter() {
            // println!("op: {}", t.op);
            let part_id = partition.get(t).unwrap();
            if let Some(du) = tmp_dusg.get_mut(&part_id) {
                du.insert_node(t);
            } else {
                panic!("Subgraph not found for index: {}", num_parts);
            }
        }

        println!("Finish inserting terms");

        for (part_id, mut du) in tmp_dusg.into_iter() {
            du.insert_edges(&d);
            dusg.insert(part_id, du.clone());
        }

        println!("Finish inserting edges");
        
        assignment = get_share_map_with_mutation_smart(&d, cm, &dusg, &partition, ml, mss);
        println!("LOG: ILP time: {:?}", now.elapsed());
    }

    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &d));

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_glp(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    // println!("Terms after inline all.");
    // for t in c.terms_postorder() {
    //     println!("t: {}", t);
    // }

    let cs = c.to_cs();
    let assignment = assign(&cs, cm);
    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_smart_glp(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    let k_map = dug.get_k();

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let assignment = smart_global_assign(&dug.good_terms, &dug.def_use, &k_map, cm);
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_y(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let assignment: SharingMap = dug.good_terms
        .iter()
        .map(|term| (term.clone(), ShareType::Yao))
        .collect();
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_b(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let assignment: SharingMap = dug.good_terms
        .iter()
        .map(|term| (term.clone(), ShareType::Boolean))
        .collect();
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_a_y(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let cost_model = get_cost_model(cm);
    let assignment: SharingMap = dug.good_terms
        .iter()
        .map(|term| {
            (
                term.clone(),
                if let Some(costs) = cost_model.get(&term.op) {
                    match &term.op {
                        Op::Select | Op::Store => ShareType::Yao,
                        _ => {
                            let mut min_ty: ShareType = ShareType::Yao;
                            let mut min_cost: f64 = costs[&min_ty];
                            for ty in &[ShareType::Arithmetic] {
                                if let Some(c) = costs.get(ty) {
                                    if *c < min_cost {
                                        min_ty = *ty;
                                        min_cost = *c;
                                    }
                                }
                            }
                            min_ty
                        }
                    }
                } else {
                    ShareType::Yao
                },
            )
        })
        .collect();
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}

#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_a_b(
    fs: &Functions,
    cm: &str,
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let cost_model = get_cost_model(cm);
    let assignment: SharingMap = dug.good_terms
        .iter()
        .map(|term| {
            (
                term.clone(),
                if let Some(costs) = cost_model.get(&term.op){
                    let mut min_ty: ShareType = ShareType::Boolean;
                    let mut min_cost: f64 = costs[&min_ty];
                    for ty in &[ShareType::Arithmetic] {
                        if let Some(c) = costs.get(ty) {
                            if *c < min_cost {
                                min_ty = *ty;
                                min_cost = *c;
                            }
                        }
                    }
                    min_ty
                } else {
                    ShareType::Boolean
                },
            )
        })
        .collect();
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}


#[cfg(feature = "lp")]
/// inline all function into main
pub fn inline_all_and_assign_opa(
    fs: &Functions,
    cm: &str,
    share_types: &[ShareType; 2]
) -> (Functions, HashMap<String, SharingMap>) {
    let mut now = Instant::now();
    let mut tp = TrivialPartition::new(fs, 0, 0, false);
    let main = "main";
    let (c, dug) = tp.inline_all(&main.to_string());

    println!(
        "Time: Inline and construction def uses: {:?}",
        now.elapsed()
    );

    now = Instant::now();
    let assignment = opa_smart_global_assign(&dug.good_terms, &dug.def_use, cm, share_types);
    println!("Calculate cost: {}", calculate_cost_smart_dug(&assignment, cm, &dug));

    println!("LOG: ILP time: {:?}", now.elapsed());

    let mut s_map: HashMap<String, SharingMap> = HashMap::new();
    s_map.insert(main.to_string(), assignment);
    let mut fs = Functions::new();
    fs.insert(main.to_string(), c);
    (fs, s_map)
}
