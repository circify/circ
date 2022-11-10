use std::collections::HashMap;
use std::collections::HashSet;

use std::vec::Vec;

use polynomial::Polynomial;

use crate::front::regex::deriv::{DFA, mk_dfa};
use crate::front::regex::parser::re::Regex;

/// DFA encoding using Lagrange polynomials
#[derive(Debug)]
pub struct PolyDFA {
    /// For each [char], a characteristic polynomial P(state_id) = state_id'
    /// Another encoding of the DFA's delta function
    poly: HashMap<char, Polynomial<i32>>,
    /// Initial state
    init: i32,
    /// Final state
    fin: HashSet<i32>
}

impl PolyDFA {
    pub fn new(init: i32, fin: &HashSet<i32>) -> Self {
       Self { poly: HashMap::new(), init, fin: fin.clone() }
    }

    pub fn add(&mut self, c: char, p: Polynomial<i32>) {
       self.poly.insert(c, p);
    }

    pub fn is_match(&self, doc: &String) -> bool {
       let mut s = self.init;
       // For "abb" compute [P_b(P_b(P_a(init)))]
       for c in doc.chars() {
          let ss = self.poly[&c].eval(s);
          println!("P(x) = {}", self.poly[&c].pretty("x"));
          println!("{} -> {}", s, ss);
          s = ss;
       }
       // If it is in the final states, then success
       self.fin.contains(&s)
    }
}

/// End-to-end: From Regex -> DFA -> PolyDFA
pub fn mk_poly(q0: &Regex, ab: &String) -> PolyDFA {
    let mut dfa = DFA::new();
    mk_dfa(q0, ab, &mut dfa);

    let fs = dfa.get_final_states();
    let mut pdfa = PolyDFA::new(dfa.get_state_num(q0), &fs);

    for c in ab.chars() {
        let (xs, ys)  =
            dfa.deltas()       // For all transitions....
                .into_iter()
                .filter_map(|(from, x, to)|
                  if x == c {  // ... with [c], save (from, to)
                      Some (
                        (dfa.get_state_num(&from),
                         dfa.get_state_num(&to)))
                  } else { None })
                .unzip::<i32, i32, Vec<i32>, Vec<i32>>();

        let lagrange = Polynomial::lagrange(&xs, &ys).unwrap();
        println!("Interpolate {:?}, {:?}: P(x) = {}", xs, ys, lagrange.pretty("x"));

        // Lagrange interpolation; P_c(x) intersects (xs, ys)
        pdfa.add(c, lagrange);
    }
    // println!("DFA: {:?}, PolyDFA: {:?}", dfa, pdfa);
    pdfa
}

