use std::collections::HashSet;
use std::collections::HashMap;

use crate::front::regex::parser::Re::{self, Regex, RegexF};

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
    match **r {
        RegexF::Nil | RegexF::Star(_) => true,
        RegexF::Empty | RegexF::Char(_) => false,
        RegexF::Not(r) => !nullable(&r),
        RegexF::App(a,b) => nullable(&a) && nullable(&b),
        RegexF::Alt(a,b) => nullable(&a) || nullable(&b)
    }
}

pub fn deriv(c: char, r: &Regex) -> Regex {
    match **r {
        RegexF::Nil => Re::empty(),
        RegexF::Empty => Re::empty(),
        RegexF::Char(x) if x == c => Re::nil(),
        RegexF::Char(_) => Re::empty(),
        RegexF::Not(r) => Re::not(deriv(c, &r)),
        RegexF::App(a,b) if nullable(&a) =>
           Re::alt(Re::app(deriv(c, &a), b.clone()), deriv(c, &b)),
        RegexF::App(a,b) => Re::app(deriv(c, &a), b.clone()),
        RegexF::Alt(a,b) => Re::alt(deriv(c, &a), deriv(c, &b)),
        RegexF::Star(a) => Re::app(deriv(c, &a), Re::star(a.clone()))
    }
}

pub struct DFA {
    /// Number of states
    n: i32,
    /// Set of states (and their index)
    Q: HashMap<Regex, i32>,
    /// Transition relation from [state -> state], given [char]
    d: HashSet<(Regex, char, Regex)>
}

impl DFA {
    pub fn new() -> Self {
        Self { n: 0, Q: HashMap::new(), d: HashSet::new() }
    }
    pub fn add_transition(&mut self, from: Regex, c: char, to: Regex) {
        self.d.insert((from, c, to));
    }

    pub fn add_state(&mut self, new_state: Regex) {
        self.n= self.n + 1;
        self.Q.insert(new_state.clone(), self.n);
    }

    pub fn contains_state(&self, state: &Regex) -> bool {
        self.Q.contains_key(state)
    }

    pub fn get_state_num(&self, state: &Regex) -> i32 {
        self.Q[state]
    }

    pub fn get_final_states(&self) -> HashSet<i32> {
        self.Q.into_iter().filter_map(|(k,v)| if nullable(&k) { Some(v) } else { None }).collect()
    }

    pub fn deltas(&self) -> HashSet<(Regex, char, Regex)> { self.d }
}

pub fn mkDFA(q: &Regex, ab: String, d: &mut DFA) {
    for c in ab.chars() {
      let q_c = deriv(c, q);
      d.add_transition(q.clone(), c, q_c);

      if d.contains_state(&q_c) {
          continue;
      } else {
          d.add_state(q_c);
          mkDFA(&q_c, ab, d);
      }
    }
}
