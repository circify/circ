//! Inline function call terms

use std::collections::BTreeMap;

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

fn inline(fd: &FuncDef, args: &Vec<Term>, fs: &Functions) -> Term {
    assert!(fd.params.len() == args.len());
    let mut params: BTreeMap<String, Term> = BTreeMap::new();
    for (p, t) in fd.params.keys().zip(args) {
        println!("param: {}", p);
        params.insert(p.clone(), t.clone());
    }

    let comp = cs.functions.get(fd).unwrap();
    assert!(comp.outputs.len() == 1);
    let o = &comp.outputs[0];
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
    cache.get(o).unwrap().clone()
}

/// Traverse terms and inline function calls
pub fn inline_function_calls(
    term_: Term,
    Cache(ref mut rewritten): &mut Cache,
    fs: &Functions,
) -> Term {
    let mut stack = vec![(term_.clone(), false)];

    // Maps terms to their rewritten versions.
    while let Some((t, children_pushed)) = stack.pop() {
        if rewritten.contains_key(&t) {
            continue;
        }
        if !children_pushed {
            stack.push((t.clone(), true));
            stack.extend(t.cs.iter().map(|c| (c.clone(), false)));
            continue;
        }
        let entry = match &t.op {
            Op::Call(name, args, rets) => inline(fd, &t.cs, fs),
            _ => t.clone(),
        };
        rewritten.insert(t, entry);
    }

    for t in PostOrderIter::new(term_.clone()) {
        let mut children = Vec::new();
        for c in &t.cs {
            if let Some(rewritten_c) = rewritten.get(c) {
                children.push(rewritten_c.clone());
            } else {
                children.push(c.clone());
            }
        }
        let entry = match &t.op {
            Op::Call(name, args, rets) => {
                println!("Inlining: {}", fd.name);
                inline(fd, &t.cs, cs)
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

// /// Traverse `term`, binarize n-ary operators.
// pub fn binarize_nary_ops(term_: Term) -> Term {
//     let mut c = Cache::new();
//     binarize_nary_ops_cached(term_, &mut c)
// }
// /// Traverse `term`, binarize n-ary operators.
// pub fn binarize_nary_ops_cached(term_: Term, Cache(ref mut rewritten): &mut Cache) -> Term {
//     let mut stack = vec![(term_.clone(), false)];

//     // Maps terms to their rewritten versions.
//     while let Some((t, children_pushed)) = stack.pop() {
//         if rewritten.contains_key(&t) {
//             continue;
//         }
//         if !children_pushed {
//             stack.push((t.clone(), true));
//             stack.extend(t.cs.iter().map(|c| (c.clone(), false)));
//             continue;
//         }
//         let entry = match &t.op {
//             Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => binarize(&t.op, &t.cs),
//             _ => t.clone(),
//
//    };
//         rewritten.insert(t, entry);
//     }

//     for t in PostOrderIter::new(term_.clone()) {
//         let mut children = Vec::new();
//         for c in &t.cs {
//             if let Some(rewritten_c) = rewritten.get(c) {
//                 children.push(rewritten_c.clone());
//             } else {
//                 children.push(c.clone());
//             }
//         }
//         let entry = match t.op {
//             Op::BoolNaryOp(_) | Op::BvNaryOp(_) | Op::PfNaryOp(_) => binarize(&t.op, &children),
//             _ => term(t.op.clone(), children),
//         };
//         rewritten.insert(t.clone(), entry);
//     }

//     if let Some(t) = rewritten.get(&term_) {
//         t.clone()
//     } else {
//         panic!("Couldn't find rewritten binarized term: {}", term_);
//     }
// }
