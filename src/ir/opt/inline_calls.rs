//! Inline function call terms

use std::collections::{BTreeMap, HashMap};

use crate::ir::term::*;

/// Inline cache.
#[derive(Default)]
pub struct Cache(TermMap<Term>);

impl Cache {
    /// Empty cache.
    pub fn new() -> Self {
        Cache(TermMap::new())
    }
}

// TODO: this can fail if the function name contains '_'
fn get_var_name(name: &String) -> String {
    let new_name = name.to_string().replace('.', "_");
    let n = new_name.split('_').collect::<Vec<&str>>();
    match n.len() {
        5 => n[3].to_string(),
        6.. => {
            let l = n.len() - 1;
            format!("{}_{}", n[l - 2], n[l])
        }
        _ => {
            panic!("Invalid variable name: {}", name);
        }
    }
}

fn match_arg(name: &String, params: &BTreeMap<String, Term>) -> Term {
    let new_name = get_var_name(name);
    params.get(&new_name).unwrap().clone()
}

fn inline(name: &str, params: BTreeMap<String, Term>, fs: &Functions) -> Vec<Term> {
    let mut res: Vec<Term> = Vec::new();
    let comp = fs.computations.get(name).unwrap();
    for o in comp.outputs.iter().rev() {
        let mut cache = TermMap::new();
        for t in PostOrderIter::new(o.clone()) {
            match &t.op {
                Op::Var(name, _sort) => {
                    let ret = match_arg(name, &params);
                    cache.insert(t.clone(), ret.clone());
                }
                _ => {
                    let mut children = Vec::new();
                    for c in &t.cs {
                        if let Some(rewritten_c) = cache.get(c) {
                            children.push(rewritten_c.clone());
                        } else {
                            children.push(c.clone());
                        }
                    }
                    cache.insert(t.clone(), term(t.op.clone(), children));
                }
            }
        }
        res.push(cache.get(o).unwrap().clone());
    }
    res
}

/// Traverse terms and inline function calls
pub fn inline_function_calls(
    term_: Term,
    Cache(ref mut rewritten): &mut Cache,
    fs: &Functions,
) -> Term {
    let mut call_cache: HashMap<Term, Vec<Term>> = HashMap::new();
    for t in PostOrderIter::new(term_.clone()) {
        println!("inlining term: {}", t);
        let mut children = Vec::new();
        for c in &t.cs {
            if let Some(rewritten_c) = rewritten.get(c) {
                if call_cache.contains_key(c) {
                    children.push(call_cache.get_mut(c).unwrap().pop().unwrap().clone());
                } else {
                    children.push(rewritten_c.clone());
                }
            } else {
                children.push(c.clone());
            }
        }
        let entry = match &t.op {
            Op::Call(name, args, _rets, _) => {
                println!("Inlining: {}", name);

                // Check number of args
                let num_args = args.values().fold(0, |sum, x| {
                    sum + match x {
                        Sort::Array(_, _, l) => *l,
                        _ => 1,
                    }
                });
                assert!(
                    num_args == t.cs.len(),
                    "Number of arguments mismatch. {}, {}",
                    num_args,
                    t.cs.len()
                );

                // Check arg types
                let arg_types = args
                    .values()
                    .map(|x| match &x {
                        Sort::Array(_, val_sort, l) => {
                            let mut res: Vec<Sort> = Vec::new();
                            for _ in 0..*l {
                                res.push(*val_sort.clone());
                            }
                            res
                        }
                        _ => vec![x.clone()],
                    })
                    .flatten()
                    .collect::<Vec<_>>();

                assert!(
                    arg_types == t.cs.iter().map(|c| check(c)).collect::<Vec<Sort>>(),
                    "Argument type mismatch"
                );

                let mut params: BTreeMap<String, Term> = BTreeMap::new();
                let arg_keys = args
                    .iter()
                    .map(|(n, x)| match &x {
                        Sort::Array(_, _, l) => {
                            let mut res: Vec<String> = Vec::new();
                            for i in 0..*l {
                                res.push(format!("{}_{}", n.clone(), i));
                            }
                            res
                        }
                        _ => vec![n.clone()],
                    })
                    .flatten();
                for (n, c) in arg_keys.zip(t.cs.clone()) {
                    params.insert(n.clone(), c.clone());
                }
                let res = inline(name, params, fs);
                call_cache.insert(t.clone(), res.clone());
                res[0].clone()
            }
            _ => term(t.op.clone(), children),
        };
        rewritten.insert(t.clone(), entry);
    }

    if let Some(t) = rewritten.get(&term_) {
        t.clone()
    } else {
        panic!("Couldn't find rewritten binarized term: {}", term_);
    }
}
