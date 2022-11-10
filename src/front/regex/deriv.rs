use std::collections::HashSet;
use std::collections::HashMap;

use crate::front::regex::parser::re::{self, Regex, RegexF};

// TODO: Find a good place for this
/* use hashconsing::{*, hash_coll::*};
fn memoize<T: Hash, R>(f: fn(HCons<T>, R)) -> fn(HCons<T>, R) {
    static MEMO: HConMap<HCons<T>, R> = HConMap::with_capacity(100);
    |a| MEMO.get(a).unwrap_or({
        let res = f(a);
        MEMO.insert(a, res);
        res
    })
}
*/

pub fn nullable(r: &Regex) -> bool {
    match &**r {
        RegexF::Nil | RegexF::Star(_) => true,
        RegexF::Empty | RegexF::Char(_) => false,
        RegexF::Not(ref r) => !nullable(r),
        RegexF::App(ref a, ref b) => nullable(a) && nullable(b),
        RegexF::Alt(ref a, ref b) => nullable(a) || nullable(b)
    }
}

pub fn deriv(c: char, r: &Regex) -> Regex {
    match &**r {
        RegexF::Nil => re::empty(),
        RegexF::Empty => re::empty(),
        RegexF::Char(x) if *x == c => re::nil(),
        RegexF::Char(_) => re::empty(),
        RegexF::Not(ref r) => re::not(deriv(c, r)),
        RegexF::App(ref a, ref b) if nullable(a) =>
           re::alt(re::app(deriv(c, a), b.clone()), deriv(c, b)),
        RegexF::App(ref a, ref b) => re::app(deriv(c, a), b.clone()),
        RegexF::Alt(ref a, ref b) => re::alt(deriv(c, a), deriv(c, b)),
        RegexF::Star(ref a) => re::app(deriv(c, a), re::star(a.clone()))
    }
}

#[derive(Debug)]
pub struct DFA {
    /// Number of states
    n: i32,
    /// Set of states (and their index)
    states: HashMap<Regex, i32>,
    /// Transition relation from [state -> state], given [char]
    trans: HashSet<(Regex, char, Regex)>
}

impl DFA {
    pub fn new() -> Self {
        Self { n: 0, states: HashMap::new(), trans: HashSet::new() }
    }
    pub fn add_transition(&mut self, from: &Regex, c: char, to: &Regex) {
        self.trans.insert((from.clone(), c, to.clone()));
    }

    pub fn add_state(&mut self, new_state: &Regex) {
        if self.states.insert(new_state.clone(), self.n).is_none() {
            self.n = self.n + 1;
        }
    }

    pub fn contains_state(&self, state: &Regex) -> bool {
        self.states.contains_key(state)
    }

    pub fn get_state_num(&self, state: &Regex) -> i32 {
        self.states[state]
    }

    pub fn get_final_states(&self) -> HashSet<i32> {
        self.states
          .clone()
          .into_iter()
          .filter_map(|(k,v)| if nullable(&k) { Some(v) } else { None })
          .collect()
    }

    pub fn deltas(&self) -> HashSet<(Regex, char, Regex)> { self.trans.clone() }
}

/// Top level, generate a DFA using derivatives [Owens et al. 06]
pub fn mk_dfa(q: &Regex, ab: &String, d: &mut DFA) {
    // Add to DFA if not already there
    d.add_state(q);

    // Explore derivatives
    for c in ab.chars() {
      let q_c = deriv(c, q);
      d.add_transition(q, c, &q_c);
      if d.contains_state(&q_c) {
          continue;
      } else {
          mk_dfa(&q_c, ab, d);
      }
    }
}
