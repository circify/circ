use std::collections::HashMap;
use std::collections::HashSet;

use std::vec::Vec;

use polynomial::Polynomial;

use crate::front::regex::deriv::{DFA, mkDFA};
use crate::front::regex::parser::Re::Regex;

/// DFA encoding using Lagrange polynomials
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

    pub fn add(self, c: char, p: Polynomial<i32>) {
       self.poly.insert(c, p);
    }

    pub fn is_match(self, doc: String) -> bool {
       let mut s = self.init;
       // For "abb" compute [P_b(P_b(P_a(init)))]
       for c in doc.chars() {
          s = self.poly[&c].eval(s);
       }
       // If it is in the final states, then success
       self.fin.contains(&s)
    }
}

/// End-to-end: From Regex -> DFA -> PolyDFA
pub fn mkPoly(q0: &Regex, ab: String) -> PolyDFA {
    let dfa = DFA::new();
    mkDFA(q0, ab, &mut dfa);

    let Fs = dfa.get_final_states();
    let Pdfa = PolyDFA::new(dfa.get_state_num(q0), &Fs);

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

        // Lagrange interpolation; P_c(x) intersects (xs, ys)
        Pdfa.add(c, Polynomial::lagrange(&xs, &ys).unwrap());
    }
    Pdfa
}

