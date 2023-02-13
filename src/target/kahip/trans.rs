use crate::ir::term::*;

use crate::target::aby::assignment::ShareType;
use crate::target::aby::assignment::SharingMap;

use std::collections::HashMap;
use std::path::Path;
use std::time::Duration;
use std::time::Instant;

use std::fs;

// Get file path to write Chaco graph to
fn get_graph_path(path: &Path, lang: &str) -> String {
    let filename = Path::new(&path.iter().last().unwrap().to_os_string())
        .file_stem()
        .unwrap()
        .to_os_string()
        .into_string()
        .unwrap();
    let name = format!("{}_{}", filename, lang);
    let mut path = format!("scripts/aby_tests/tests/{}.graph", name);
    if Path::new(&path).exists() {
        fs::remove_file(&path).expect("Failed to remove old graph file");
    }
    path
}

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
