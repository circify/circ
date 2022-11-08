use std::collections::HashMap;
use std::collections::HashSet;

use std::vec::Vec;

use polynomial::Polynomial;

use crate::front::regex::deriv::{DFA, mkDFA};
use crate::front::regex::parser::Regex;

/// DFA encoding using Lagrange polynomials
pub struct PolyDFA {
    poly: HashMap<char, Polynomial<i32>>,
    init: i32,
    fin: HashSet<i32>
}

impl PolyDFA {
    pub fn new(init: i32, fin: HashSet<i32>) -> Self {
       Self { poly: HashMap::new(), init, fin }
    }

    pub fn add(self, c: char, p: Polynomial<i32>) {
       self.poly.insert(c, p);
    }

    pub fn is_match(self, doc: String) -> bool {
       let mut s = self.init;
       for c in doc.chars() {
          s = self.poly[&c].eval(s);
       }
       self.fin.contains(&s)
    }
}

pub fn mkPoly(q0: Regex, ab: String) -> PolyDFA {
    let dfa = DFA::new();
    mkDFA(q0, ab, &mut dfa);

    let Fs = dfa.get_final_states();
    let P = PolyDFA::new(dfa.get_state_num(&q0), Fs);

    for c in ab.chars() {
        let (xs, ys)  =
            dfa.deltas()
                .into_iter()
                .filter_map(|(from, x, to)|
                  if x == c {
                      Some ((dfa.get_state_num(&from),
                            dfa.get_state_num(&to)))
                  } else { None })
                .unzip::<i32, i32, Vec<i32>, Vec<i32>>();

        P.add(c, Polynomial::lagrange(&xs, &ys).unwrap());
    }
    P
}

