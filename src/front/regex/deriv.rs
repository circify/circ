use std::collections::HashSet;
use std::collections::HashMap;

use crate::front::regex::parser::Regex;

pub fn nullable(r: &Regex) -> bool {
    match r {
        Regex::Nil | Regex::Star(_) => true,
        Regex::Empty | Regex::Char(_) => false,
        Regex::Not(r) => !nullable(&*r),
        Regex::App(a,b) => nullable(&*a) && nullable(&*b),
        Regex::Alt(a,b) => nullable(&*a) || nullable(&*b)
    }
}

/// Smart constructors for regex simplification
pub fn app(a: Box<Regex>, b: Box<Regex>) -> Regex {
    match (*a, *b) {
        (Regex::App(a, b), c) => app(a, Box::new(app(b, Box::new(c)))),
        (a, Regex::Nil) | (Regex::Nil, a) => a,
        (_, Regex::Empty) | (Regex::Empty, _) => Regex::Empty,
        (a, b) => Regex::App(Box::new(a), Box::new(b))
    }
}

pub fn alt(a: Box<Regex>, b: Box<Regex>) -> Regex {
    match (*a, *b) {
        (a, b) if a == b => a,
        (Regex::Alt(a, b), c) =>
            alt(a, Box::new(alt(b, Box::new(c)))),
        (Regex::Not(inner), _) if *inner == Regex::Empty =>
            Regex::Not(Box::new(Regex::Empty)),
        (Regex::Empty, a) | (a, Regex::Empty) => a,
        (a, b) if b < a => Regex::Alt(Box::new(b), Box::new(a)),
        (a, b) => Regex::Alt(Box::new(a), Box::new(b))
    }
}

pub fn star(a: Box<Regex>) -> Regex {
    match *a {
        Regex::Star(_) | Regex::Nil => *a,
        Regex::Empty => Regex::Nil,
        _ => Regex::Star(a)
    }
}

pub fn not(a: Box<Regex>) -> Regex {
    match *a {
        Regex::Not(a) => *a,
        _ => Regex::Not(a)
    }
}

fn deriv(c: char, r: &Regex) -> Regex {
    match r {
        Regex::Nil => Regex::Empty,
        Regex::Empty => Regex::Empty,
        Regex::Char(x) if x == &c => Regex::Nil,
        Regex::Char(_) => Regex::Empty,
        Regex::Not(r) => not(Box::new(deriv(c, &*r))),
        Regex::App(a,b) if nullable(&*a) =>
           alt(Box::new(app(Box::new(deriv(c, &*a)), b.clone())), Box::new(deriv(c, &*b))),
        Regex::App(a,b) => app(Box::new(deriv(c, &*a)), b.clone()),
        Regex::Alt(a,b) => alt(Box::new(deriv(c, &*a)), Box::new(deriv(c, &*b))),
        Regex::Star(a) => app(Box::new(deriv(c, &*a.clone())), Box::new(star(a.clone())))
    }
}

pub struct DFA {
    n: i32,
    Q: HashMap<Regex, i32>,
    d: HashSet<(Regex, char, Regex)>
}

impl DFA {
    pub fn new() -> Self {
        Self { n: 0, Q: HashMap::new(), d: HashSet::new() }
    }
    pub fn add_transition(&mut self, from: &Regex, c: char, to: &Regex) {
        self.d.insert((from.clone(), c, to.clone()));
    }

    pub fn add_state(&mut self, new_state: &Regex) {
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

    pub fn deltas(self) -> HashSet<(Regex, char, Regex)> { self.d }
}

pub fn mkDFA(q: Regex, ab: String, d: &mut DFA) {
    for c in ab.chars() {
      let q_c = deriv(c, &q);
      d.add_transition(&q, c, &q_c);

      if d.contains_state(&q_c) {
          continue;
      } else {
          d.add_state(&q_c);
          mkDFA(q_c, ab, d);
      }
    }
}
