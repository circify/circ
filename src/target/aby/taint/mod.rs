//! Machinery for Taint Analysis
use crate::{ir::term::*, target::aby::utils::{write_lines_to_file, get_path}};
use core::str;
use std::{fmt::{self, Display, Formatter}, path::Path};

const PARTY_A: u8 = 0;
const PARTY_B: u8 = 1;
const PUBLIC: u8 = 2;

/// The visibility of an operation
#[derive(PartialEq, Copy, Clone)]
pub enum VisType {
    /// Plaintext, only dependent on public values
    Plaintext,
    /// Only dependent on public values and/or Party A inputs
    PartyA,
    /// Only dependent on public values and/or Party A inputs
    PartyB,
    /// Dependent on both Party A and Party B inputs
    MultiParty,
}

impl Display for VisType {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            VisType::Plaintext => write!(f, "Public"),
            VisType::PartyA => write!(f, "Depends on Party A"),
            VisType::PartyB => write!(f, "Depends on Party B"),
            VisType::MultiParty => write!(f, "Depends on Both")
        }
    }
}

/// A map from terms (operations or inputs) to sharing schemes they use
pub type VisMap = TermMap<VisType>;

/// Taint analyzer for identify opportunities for pre-computation 
/// in MPC programs
pub struct TaintAnalyzer {
    ///Visibility Map
    vmap: VisMap,
    /// Metadata
    pub md: ComputationMetadata,
    ///Output terms of plaintext precomputation
    plaintext_ir: TermMap<String>,
    ///Output terms of party_a precomputation
    party_a_ir: TermMap<String>,
    ///Output terms of party_B precomputation
    party_b_ir: TermMap<String>,

    bridge_cnt: i32,
    ///Defines bridges between the partitioned IRs
    bridge_map: TermMap<Term>,
}

impl TaintAnalyzer {
    /// Intantiates new TaintAnalyzer
    pub fn new(md: ComputationMetadata) -> Self {
        Self {
            vmap: TermMap::new(),
            md: md,
            plaintext_ir: TermMap::new(),
            party_a_ir: TermMap::new(),
            party_b_ir: TermMap::new(),
            bridge_cnt: 0,
            bridge_map: TermMap::new(),
        }
    }
    ///Converts visibility integer to a VisType
    fn to_vistype(&self, vis_int: u8) -> VisType {
        match vis_int {
            PARTY_A => VisType::PartyA,
            PARTY_B => VisType::PartyB,
            PUBLIC => VisType::Plaintext,
            _ => panic!("Unsupported visiblity int label.")
        }
    }

    fn vmap_lookup(&self, t: Term) -> VisType {
        *self
            .vmap
            .get(&t) 
            .unwrap_or_else(|| panic!("Missing VisType for {:?}", t))
    }

    fn vmap_update(&mut self, t: Term, vis: VisType) {
        match self
            .vmap
            .get(&t) 
        {
            None | Some(VisType::Plaintext) => {
                self.vmap.insert(t.clone(), vis);
            }
            Some(VisType::PartyA) => {
                if vis == VisType::PartyB {
                    self.vmap.insert(t.clone(), VisType::MultiParty);
                }
            }
            Some(VisType::PartyB) => {
                if vis == VisType::PartyA {
                    self.vmap.insert(t.clone(), VisType::MultiParty);
                }
            }
            Some(VisType::MultiParty) => {
                //Do nothing
            }
        }
    }

    fn analyze_term(&mut self, t: Term) {
        match &t.op {
            Op::Var(name, _) => {
                if self.md.input_vis.contains_key(name) {
                    match self.md.input_vis.get(name).unwrap() {
                        Some(role) => {
                            let vis = self.to_vistype(*role);
                            self.vmap_update(t.clone(), vis);
                        }
                        None => {
                            self.vmap_update(t.clone(), VisType::Plaintext);
                        }
                    }
                }
            }
            Op::Const(_) => {
                self.vmap_update(t.clone(), VisType::Plaintext);
            }
            _ => {
                let mut vis = VisType::Plaintext;
                for cterm in &t.cs {
                    match self.vmap_lookup(cterm.clone()) {
                        VisType::PartyA => {
                            if vis == VisType::PartyB {
                                vis = VisType::MultiParty;
                                break;
                            }
                            vis = VisType::PartyA;
                        }
                        VisType::PartyB => {
                            if vis == VisType::PartyA {
                                vis = VisType::MultiParty;
                                break;
                            }
                            vis = VisType::PartyB;
                        }
                        VisType::MultiParty => {
                            vis = VisType::MultiParty;
                            break;
                        }
                        VisType::Plaintext => {},
                    }
                }
                self.vmap_update(t.clone(), vis);
            }
        }
    }

    fn iterate_term(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
            self.analyze_term(c);
        }
    }

    ///Populates the vmap based on the terms and metadata
    pub fn fill_vmap(&mut self, terms: Vec<Term>) {
        for t in terms {
            self.iterate_term(t.clone());
        }

        println!();
        println!("Printing VMAP\n");
        for (k, v) in self.vmap.iter() {
            println!("k={}, v={}", k ,v);
        }
        println!();
        println!();
    }
    
    fn new_bridge_name(&mut self) -> String {
        let name = format!("bridge_{}", self.bridge_cnt);
        self.bridge_cnt += 1;
        name
    }

    fn add_plaintext_output(&mut self, t: Term) {
        let name = self.new_bridge_name();
        self.plaintext_ir.insert(t.clone(), name.clone());
        let new_term = term(Op::Var(name.clone(), check(&t)), Vec::new());
        self.md.input_vis.insert(name, Some(PUBLIC));
        self.bridge_map.insert(t, new_term);
    }

    fn add_party_a_output(&mut self, t: Term) {
        let name = self.new_bridge_name();
        self.party_a_ir.insert(t.clone(), name.clone());
        let new_term = term(Op::Var(name.clone(), check(&t)), Vec::new());
        self.md.input_vis.insert(name, Some(PARTY_A));
        self.bridge_map.insert(t, new_term);
    }

    fn add_party_b_output(&mut self, t: Term) {
        let name = self.new_bridge_name();
        self.party_b_ir.insert(t.clone(), name.clone());
        let new_term = term(Op::Var(name.clone(), check(&t)), Vec::new());
        self.md.input_vis.insert(name, Some(PARTY_B));
        self.bridge_map.insert(t, new_term);
    }

    ///Partitions the IR based on data dependency
    pub fn partition_ir(&mut self, terms: Vec<Term>) {
        for output in terms {
            for t in PostOrderIter::new(output) {
                match self.vmap_lookup(t.clone()) {
                    VisType::MultiParty => {
                        for cterm in &t.cs {
                            match self.vmap_lookup(cterm.clone()) {
                                VisType::Plaintext => {
                                    self.add_plaintext_output(cterm.clone());
                                },
                                VisType::PartyA => {
                                    self.add_party_a_output(cterm.clone());
                                },
                                VisType::PartyB => {
                                    self.add_party_b_output(cterm.clone());
                                },
                                VisType::MultiParty => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        println!("\nPrinting Bridges:");
        for (key, value) in self.bridge_map.iter() {
            println!("{} / {}", key, value);
        }
    }

    fn serialize_precomputation(&self, terms: &TermMap<String>)-> Vec<String> {
        let mut lines = Vec::new();
        for (key, bridge_name) in terms.iter() {
            lines.push(format!("{}:{},", bridge_name, text::serialize_term(key)));
        }
        lines
    }

    ///Exports precomputations to as text files
    pub fn export_precomputations(&self, path: &Path, lang: &str) {
        println!("Printing Plaintext Outs:");
        for (key, value) in self.plaintext_ir.iter() {
            println!("{} / {}", key, value);
        }
        println!("Printing Party A Outs:");
        for (key, value) in self.party_a_ir.iter() {
            println!("{} / {}", key, value);
        }
        println!("Printing Party B Outs:");
        for (key, value) in self.party_b_ir.iter() {
            println!("{} / {}", key, value);
        }
        write_lines_to_file(
            &get_path(path, lang, "plaintext_ir"),
            &self.serialize_precomputation(&self.plaintext_ir));
        write_lines_to_file(
            &get_path(path, lang, "party_a_ir"),
            &self.serialize_precomputation(&self.party_a_ir));
        write_lines_to_file(
            &get_path(path, lang, "party_b_ir"),
            &self.serialize_precomputation(&self.party_b_ir));    
        println!("EXPORTED PRECOMPS");
    }

    ///Rewrites term in MPC computation to take advantage of precomputations (bridges)
    pub fn rewrite_term(&self, og_term: Term) -> Term {
        let mut rewritten =  TermMap::new();
        for t in PostOrderIter::new(og_term.clone()) {
            match self.bridge_map.get(&t) {
                Some(bridge_var) => {
                    rewritten.insert(t, bridge_var.clone());
                }
                None => {
                    let mut children = Vec::new();
                    for c in &t.cs {
                        match rewritten.get(c) {
                            None => {
                                children.push(c.clone());
                            }
                            Some(rewritten_c) => {
                                children.push(rewritten_c.clone());
                            }
                        }
                    }
                    rewritten.insert(t.clone(), term(t.op.clone(), children));
                }
            }
        }
        rewritten.get(&og_term).expect("Couldn't find rewritten term").clone()
    }
}
