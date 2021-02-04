use super::term::*;
use crate::target::r1cs::*;

use rug::Integer;

use std::collections::HashMap;
use std::fmt::Display;

struct ToR1cs {
    r1cs: R1cs<String>,
    bools: TermMap<Lc>,
    values: Option<HashMap<String, Value>>,
    next_idx: usize,
}

impl ToR1cs {
    fn new(modulus: Integer, values: Option<HashMap<String, Value>>) -> Self {
        Self {
            r1cs: R1cs::new(modulus, values.is_some()),
            bools: TermMap::new(),
            values,
            next_idx: 0,
        }
    }

    fn fresh_var<D: Display>(&mut self, ctx: &D) -> Lc {
        let n = format!("{}v{}", ctx, self.next_idx);
        self.next_idx += 1;
        self.r1cs.add_signal(n.clone());
        self.r1cs.signal_lc(&n)
    }

    fn embed(&mut self, t: Term) {
        for c in PostOrderIter::new(t) {
            match check(c.clone()).expect("type-check error in embed") {
                Sort::Bool => {
                    self.embed_bool(c);
                }
                s => panic!("Unsupported sort in embed: {:?}", s),
            }
        }
    }

    fn enforce_bit(&mut self, b: &Lc) {
        self.r1cs
            .constraint(b.clone(), b.clone() - 1, self.r1cs.zero());
    }

    fn embed_bool(&mut self, t: Term) -> &Lc {
        debug_assert!(check(t.clone()) == Ok(Sort::Bool));
        // TODO: skip if already embedded
        for c in PostOrderIter::new(t.clone()) {
            if !self.bools.contains_key(&c) {
                let lc = match &c.op {
                    Op::Var(name, Sort::Bool) => {
                        let v = self.fresh_var(name);
                        self.enforce_bit(&v);
                        v
                    }
                    _ => panic!("Non-boolean in embed_bool: {:?}", c),
                };
                self.bools.insert(c, lc);
            }
        }
        self.bools.get(&t).unwrap()
    }
}
