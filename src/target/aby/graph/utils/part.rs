//!
use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::process::{Command, Stdio};

/// Partition using Kahip / kahypar
pub struct Partitioner {
    time_limit: usize,
    imbalance: usize,
    imbalance_f32: f32,
    hyper_mode: bool,
}

impl Partitioner {
    /// Initialize a partitioner
    pub fn new(time_limit: usize, imbalance: usize, hyper_mode: bool) -> Self {
        let graph = Self {
            time_limit: time_limit,
            imbalance: imbalance,
            imbalance_f32: imbalance as f32 / 100.0,
            hyper_mode: hyper_mode,
        };
        graph
    }

    /// Partition the graph given number of partitions
    pub fn do_partition(&self, graph_path: &String, num_parts: &usize) -> HashMap<usize, usize> {
        if self.hyper_mode {
            let part_path = format!(
                "{}.part{}.epsilon{}.seed-1.KaHyPar",
                graph_path,
                num_parts,
                self.imbalance_f32.to_string()
            );
            self.call_hyper_graph_partitioner(graph_path, num_parts);
            self.parse_partition(&part_path)
        } else {
            self.check_graph(graph_path);
            let part_path = format!("{}.part", graph_path);
            self.call_graph_partitioner(graph_path, &part_path, num_parts);
            self.parse_partition(&part_path)
        }
    }

    // Read a file line by line
    fn read_lines<P>(&self, filename: P) -> io::Result<io::Lines<io::BufReader<File>>>
    where
        P: AsRef<Path>,
    {
        let file = File::open(filename)?;
        Ok(io::BufReader::new(file).lines())
    }

    fn parse_partition(&self, part_path: &String) -> HashMap<usize, usize> {
        let mut part_map = HashMap::new();
        if let Ok(lines) = self.read_lines(part_path) {
            for line in lines.into_iter().enumerate() {
                if let (i, Ok(part)) = line {
                    let part_num = part.parse::<usize>().unwrap();
                    part_map.insert(i + 1, part_num);
                }
            }
        }
        part_map
    }

    // Call hyper graph partitioning algorithm on input hyper graph
    fn call_hyper_graph_partitioner(&self, graph_path: &String, num_parts: &usize) {
        //TODO: fix path
        let output = Command::new("../kahypar/build/kahypar/application/KaHyPar")
            .arg("-h")
            .arg(graph_path)
            .arg("-k")
            .arg(num_parts.to_string()) //TODO: make this a function on the number of terms
            .arg("-e")
            .arg(self.imbalance_f32.to_string())
            .arg("--objective=cut")
            .arg("--mode=direct")
            .arg("--preset=../kahypar/config/cut_kKaHyPar_sea20.ini")
            .arg("--write-partition=true")
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        println!("stdout: {}", stdout);
        // assert!(stdout.contains(&format!("writing partition to {}", &self.part_path)));
    }

    // Call graph partitioning algorithm on input graph
    fn call_graph_partitioner(&self, graph_path: &String, part_path: &String, num_parts: &usize) {
        //TODO: fix path
        let output = Command::new("../KaHIP/deploy/kaffpa")
            .arg(graph_path)
            .arg("--k")
            .arg(num_parts.to_string()) //TODO: make this a function on the number of terms
            .arg("--preconfiguration=fast")
            .arg("--imbalance")
            .arg(self.imbalance.to_string())
            .arg("--time_limit")
            .arg(self.time_limit.to_string())
            .arg(format!("--output_filename={}", part_path))
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        println!("stdout: {}", stdout);
        assert!(stdout.contains(&format!("writing partition to {}", part_path)));
    }
    
    // Check if input graph is formatted correctly
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
}
