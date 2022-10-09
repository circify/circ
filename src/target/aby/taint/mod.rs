//! Machinery for Taint Analysis
use crate::ir::term::*;
use std::fmt::{self, Display, Formatter};

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
    vmap: VisMap,
    md: ComputationMetadata,
    // plaintext_ir: Computation,
    // party_a_ir: Computation,
    // party_b_ir: Computation,
    // mpc_ir: Computation,
}


impl TaintAnalyzer {
    /// Intantiates new TaintAnalyzer
    pub fn new(md: ComputationMetadata) -> Self {
        Self {
            vmap: TermMap::new(),
            md: md,
            // plaintext_ir: Computation::new(false),
            // party_a_ir: Computation::new(false),
            // party_b_ir: Computation::new(false),
            // mpc_ir: Computation::new(false),
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
}