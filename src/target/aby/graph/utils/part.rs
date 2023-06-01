use std::collections::HashMap;
use std::env;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;
use std::process::{Command, Stdio};
// use std::time::Instant;

pub struct Partitioner {
    time_limit: usize,
    imbalance: usize,
    imbalance_f32: f32,
    hyper_mode: bool,
    kahip_source: String,
    kahypar_source: String,
}

impl Partitioner {
    pub fn new(time_limit: usize, imbalance: usize, hyper_mode: bool) -> Self {
        // TODO: Allow only kahip or kahypar
        // Get KaHIP source directory
        let kahip_source = match env::var("KAHIP_SOURCE") {
            Ok(val) => val,
            Err(e) => panic!("Missing env variable: KAHIP_SOURCE, {}", e),
        };
        //  Get kahypar source directory
        let kahypar_source = match env::var("KAHYPAR_SOURCE") {
            Ok(val) => val,
            Err(e) => panic!("Missing env variable: KAHYPAR_SOURCE, {}", e),
        };
        let mut graph = Self {
            time_limit: time_limit,
            imbalance: imbalance,
            imbalance_f32: imbalance as f32 / 100.0,
            hyper_mode: hyper_mode,
            kahip_source,
            kahypar_source,
        };
        graph
    }

    pub fn do_refinement(
        &self,
        graph_path: &String,
        input_part_path: &String,
        output_part_path: &String,
        num_parts: &usize,
    ) -> HashMap<usize, usize> {
        if self.hyper_mode {
            let part_path = format!(
                "{}.part{}.epsilon{}.seed-1.KaHyPar",
                graph_path,
                num_parts,
                self.imbalance_f32.to_string()
            );
            self.call_hyper_graph_refiner(graph_path, input_part_path, num_parts);
            self.parse_partition(&part_path)
        } else {
            unimplemented!("Refinement using KaHIP not implemented. ");
        }
    }

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
        let output = Command::new(format!(
            "{}/build/kahypar/application/KaHyPar",
            self.kahypar_source
        ))
        .arg("-h")
        .arg(graph_path)
        .arg("-k")
        .arg(num_parts.to_string()) //TODO: make this a function on the number of terms
        .arg("-e")
        .arg(self.imbalance_f32.to_string())
        .arg("--objective=cut")
        .arg("--mode=direct")
        .arg(format!(
            "--preset={}/config/cut_kKaHyPar_sea20.ini",
            self.kahypar_source
        ))
        .arg("--write-partition=true")
        .stdout(Stdio::piped())
        .output()
        .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        // println!("stdout: {}", stdout);
    }

    // Call graph partitioning algorithm on input graph
    fn call_graph_partitioner(&self, graph_path: &String, part_path: &String, num_parts: &usize) {
        let output = Command::new(format!("{}/deploy/kaffpa", self.kahip_source))
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
        assert!(stdout.contains(&format!("writing partition to {}", part_path)));
    }

    // Call hyper graph partitioning algorithm on input hyper graph
    fn call_hyper_graph_refiner(
        &self,
        graph_path: &String,
        input_path: &String,
        num_parts: &usize,
    ) {
        let input_part_arg = format!("--part-file={}", input_path);
        let output = Command::new(format!(
            "{}/build/kahypar/application/KaHyPar",
            self.kahypar_source
        ))
        .arg("-h")
        .arg(graph_path)
        .arg("-k")
        .arg(num_parts.to_string()) //TODO: make this a function on the number of terms
        .arg("-e")
        .arg(self.imbalance_f32.to_string())
        .arg("--objective=cut")
        .arg("--mode=direct")
        .arg(format!(
            "--preset={}/config/cut_kKaHyPar_sea20.ini",
            self.kahypar_source
        ))
        .arg(input_part_arg)
        .arg("--vcycles=3")
        .arg("--write-partition=true")
        .stdout(Stdio::piped())
        .output()
        .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        // println!("stdout: {}", stdout);
    }

    // Check if input graph is formatted correctly
    fn check_graph(&self, graph_path: &String) {
        let output = Command::new(format!("{}/deploy/graphchecker", self.kahip_source))
            .arg(graph_path)
            .stdout(Stdio::piped())
            .output()
            .unwrap();
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("The graph format seems correct."));
    }
}
