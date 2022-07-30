use rug::Integer;

use fxhash::FxHashSet;
use fxhash::FxHashMap;

use crate::ir::opt::cfold::fold;
use crate::ir::term::*;
use crate::target::aby::assignment::SharingMap;
use crate::target::aby::utils::*;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::io;
use std::path::Path;

pub struct PostOrderIter_v2 {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIter_v2 {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::new(),
        }
    }
}

impl std::iter::Iterator for PostOrderIter_v2 {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                if let Op::Select = t.op{
                    if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs[0].clone()));
                        continue;
                    }
                } else if let Op::Store = t.op{
                    if let Op::Const(Value::BitVector(_)) = &t.cs[1].op {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone(); 
                        self.stack.push((false, last.cs[0].clone()));
                        self.stack.push((false, last.cs[2].clone()));
                        continue;
                    }
                }
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs.iter().map(|c| (false, c.clone())));
            } else {
                break;
            }
        }
        self.stack.pop().map(|(_, t)| {
            self.visited.insert(t.clone());
            t
        })
    }
}

fn get_sort_len(s: &Sort) -> usize {
    let mut len = 0;
    len += match s {
        Sort::Bool => 1,
        Sort::BitVector(_) => 1,
        Sort::Array(_, _, n) => *n,
        Sort::Tuple(sorts) => {
            let mut inner_len = 0;
            for inner_s in sorts.iter() {
                inner_len += get_sort_len(inner_s);
            }
            inner_len
        }
        _ => panic!("Sort is not supported: {:#?}", s),
    };
    len
}

#[derive(Clone)]
pub struct DefUsesSubGraph{
    /// List of terms in subgraph
    pub nodes: TermSet,
    /// Adjacency list of edges in subgraph
    pub edges: TermMap<TermSet>,
    /// Output leaf nodes
    pub outs: TermSet,
    /// Input leaf nodes
    pub ins: TermSet,
    /// For ILP
    pub def_use: FxHashSet<(Term, Term)>,
    pub def_uses: FxHashMap<Term, Vec<Term>>,
}

impl DefUsesSubGraph{
    /// default constructor
    pub fn new() -> Self {
        Self {
            nodes: TermSet::new(),
            edges: TermMap::new(),
            outs: TermSet::new(),
            ins: TermSet::new(),
            def_use: FxHashSet::default(),
            def_uses: FxHashMap::default(),         
        }
    }

    /// Insert nodes into ComputationSubgraph
    pub fn insert_node(&mut self, node: &Term) {
        if !self.nodes.contains(node) {
            self.nodes.insert(node.clone());
            self.def_uses.insert(node.clone(), Vec::new());
        }
    }

    /// Insert edges based on nodes in the subgraph
    pub fn insert_edges(&mut self, dug: &DefUsesGraph) {
        let mut defs: FxHashSet<Term> = FxHashSet::default();
        for t in self.nodes.iter() {
            self.edges.insert(t.clone(), TermSet::new());
            let mut flag = true;
            for c in dug.use_defs.get(t).unwrap().iter() {
                if self.nodes.contains(c) {
                    self.edges.get_mut(t).unwrap().insert(c.clone());
                    self.def_use.insert((c.clone(), t.clone()));
                    defs.insert(c.clone());
                    flag = false;
                }
            }
            if flag {
                self.ins.insert(t.clone());
            }
        }

        for t in self.nodes.iter() {
            if !defs.contains(t) {
                self.outs.insert(t.clone());
            }
        }

        for (d, u) in self.def_use.iter() {
            self.def_uses.entry(d.clone()).or_insert_with(Vec::new).push(u.clone());
        }
        
    }
}

pub fn extend_dusg(dusg: &DefUsesSubGraph, dug: &DefUsesGraph, n: usize) -> DefUsesSubGraph{
    let mut old_g: DefUsesSubGraph = dusg.clone();
    let mut new_g: DefUsesSubGraph = DefUsesSubGraph::new();
    for _ in 0..n{
        for t in old_g.nodes.iter(){
            new_g.insert_node(t);
            for u in dug.def_uses.get(t).unwrap().iter(){
                new_g.insert_node(u);
            }
            for d in dug.use_defs.get(t).unwrap().iter(){
                new_g.insert_node(d);
            }
        }
        old_g = new_g;
        new_g = DefUsesSubGraph::new();
    }
    old_g
}

pub struct DefUsesGraph {
    pub term_to_terms: TermMap<Vec<Term>>,
    pub def_use: FxHashSet<(Term, Term)>,
    pub def_uses: FxHashMap<Term, FxHashSet<Term>>,
    pub use_defs: FxHashMap<Term, FxHashSet<Term>>,
    pub const_terms: TermSet,
    pub good_terms: TermSet,
}

impl DefUsesGraph {
    pub fn new(c: &Computation) -> Self{
        let mut dug = Self {
            term_to_terms: TermMap::new(),
            def_use: FxHashSet::default(),
            def_uses: FxHashMap::default(),
            use_defs: FxHashMap::default(),
            const_terms: TermSet::new(),
            good_terms: TermSet::new(),
        };
        dug.construct_def_use(c);
        dug.construct_def_uses();
        dug.construct_use_defs();
        dug
    }

    fn construct_def_use(&mut self, c: &Computation){
        for out in c.outputs.iter() {
            for t in PostOrderIter_v2::new(out.clone()) {
                match &t.op{
                    Op::Const(Value::Tuple(tup)) => {
                        let mut terms: Vec<Term> = Vec::new();
                        for val in tup.iter() {
                            terms.push(leaf_term(Op::Const(val.clone())));
                            self.const_terms.insert(leaf_term(Op::Const(val.clone())));
                            self.add_term(&leaf_term(Op::Const(val.clone())));
                        }
                        self.term_to_terms.insert(t.clone(), terms);
                    }
                    Op::Tuple => {
                        let mut terms: Vec<Term> = Vec::new();
                        for c in t.cs.iter() {
                            terms.extend(self.term_to_terms.get(&c).unwrap().clone());
                        }
                        self.term_to_terms.insert(t.clone(), terms);
                    }
                    Op::Field(i) => {
                        let tuple_terms = self.term_to_terms.get(&t.cs[0]).unwrap().clone();
    
                        let tuple_sort = check(&t.cs[0]);
                        let (offset, len) = match tuple_sort {
                            Sort::Tuple(t) => {
                                assert!(*i < t.len());
                                // find offset
                                let mut offset = 0;
                                for j in 0..*i {
                                    offset += get_sort_len(&t[j]);
                                }
                                // find len
                                let len = get_sort_len(&t[*i]);
    
                                (offset, len)
                            }
                            _ => panic!("Field op on non-tuple"),
                        };
                        // get ret slice
                        let field_terms = &tuple_terms[offset..offset + len];
                        self.term_to_terms.insert(t.clone(), field_terms.to_vec());
                    }
                    Op::Update(i) => {
                        let mut tuple_terms = self.term_to_terms.get(&t.cs[0]).unwrap().clone();
                        let value_terms = self.term_to_terms.get(&t.cs[1]).unwrap().clone();
                        tuple_terms[*i] = value_terms[0].clone();
                        self.term_to_terms.insert(t.clone(), tuple_terms);
                    }
                    Op::Const(Value::Array(arr)) => {
                        let mut terms: Vec<Term> = Vec::new();
                        let sort = check(&t);
                        if let Sort::Array(_, _, n) = sort{
                            println!("Create a {} size array.", n);
                            let n = n as i32;
                            for i in 0..n{
                                let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                                let v = match arr.map.get(&idx) {
                                    Some(c) => c,
                                    None => &*arr.default,
                                };
                                terms.push(leaf_term(Op::Const(v.clone())));
                                self.const_terms.insert(leaf_term(Op::Const(v.clone())));
                                self.add_term(&leaf_term(Op::Const(v.clone())));
                            }
                        } else{
                            todo!("Const array sort not array????")
                        }
                        self.term_to_terms.insert(t.clone(), terms);
                    }
                    Op::Store => {
                        let mut array_terms = self.term_to_terms.get(&t.cs[0]).unwrap().clone();
                        let value_terms = self.term_to_terms.get(&t.cs[2]).unwrap().clone();
                        if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                            // constant indexing
                            let idx = bv.uint().to_usize().unwrap().clone();
                            // println!("Store the {} value on a  {} size array.",idx , array_terms.len());
                            array_terms[idx] = value_terms[0].clone();
                            self.term_to_terms.insert(t.clone(), array_terms);
                        } else{
                            for idx in 0..array_terms.len(){
                                self.def_use.insert((array_terms[idx].clone(), t.clone()));
                                array_terms[idx] = t.clone();
                            }
                            self.def_use.insert((value_terms[0].clone(), t.clone()));
                            self.term_to_terms.insert(t.clone(), array_terms);
                            self.add_term(&t);
                        }
                    }
                    Op::Select => {
                        let array_terms = self.term_to_terms.get(&t.cs[0]).unwrap().clone();
                        if let Op::Const(Value::BitVector(bv)) = &t.cs[1].op {
                            // constant indexing
                            let idx = bv.uint().to_usize().unwrap().clone();
                            if array_terms.len() == 1 && idx == 1 {
                                println!("dad op: {:?}", t.cs[0].op);
                                println!("grandpa op: {:?}", t.cs[0].cs[0].op);
                            }
                            self.term_to_terms.insert(t.clone(), vec![array_terms[idx].clone()]);
                        } else{
                            for idx in 0..array_terms.len(){
                                self.def_use.insert((array_terms[idx].clone(), t.clone()));
                            }
                            self.term_to_terms.insert(t.clone(), vec![t.clone()]);
                            self.add_term(&t);
                        }
                    }
                    // noy sure if we should include call in def uses...
                    // Op::Call(..) => {
                    //     term_to_terms.insert(t.clone(), vec![t.clone()]);
                    // }
                    // _ =>{
                    //     for c in t.cs.iter(){
                    //         if let Op::Call(..) = t.op{
                    //             continue;
                    //         } else{
                    //             let terms = term_to_terms.get(c).unwrap();
                    //             assert_eq!(terms.len(), 1);
                    //             def_use.insert((t.clone(), terms[0].clone()));
                    //         }
                    //     }
                    //     term_to_terms.insert(t.clone(), vec![t.clone()]);
                    // }
                    Op::Call(_, _, _, ret_sorts) => {
                        // Use call term itself as the placeholder
                        // Call term will be ignore by the ilp solver later
                        let mut ret_terms: Vec<Term> = Vec::new();
                        let num_rets: usize = ret_sorts.iter().map(|ret| get_sort_len(ret)).sum();
                        for _ in 0..num_rets{
                            ret_terms.push(t.clone());
                        }
                        self.term_to_terms.insert(t.clone(), ret_terms);
                    }
                    Op::Ite =>{
                        // bool exp
                        
                        if let Op::Store = t.cs[1].op{
                            // assert_eq!(t.cs[2].op, Op::Store);
                            let cond_terms = self.term_to_terms.get(&t.cs[0]).unwrap().clone();
                            assert_eq!(cond_terms.len(), 1);
                            self.def_use.insert((cond_terms[0].clone(), t.clone()));
                            // true branch
                            let mut t_terms = self.term_to_terms.get(&t.cs[1]).unwrap().clone();
                            // false branch
                            let f_terms = self.term_to_terms.get(&t.cs[2]).unwrap().clone();
                            assert_eq!(t_terms.len(), f_terms.len());
                            for idx in 0..t_terms.len(){
                                self.def_use.insert((t_terms[idx].clone(), t.clone()));
                                self.def_use.insert((f_terms[idx].clone(), t.clone()));
                                t_terms[idx] = t.clone();
                            }
                            self.term_to_terms.insert(t.clone(), t_terms);
                        } else{
                            for c in t.cs.iter(){
                                if let Op::Call(..) = t.op{
                                    continue;
                                } else{
                                    // println!("op: {}", c.op);
                                    let terms = self.term_to_terms.get(c).unwrap();
                                    assert_eq!(terms.len(), 1);
                                    self.def_use.insert((terms[0].clone(), t.clone()));
                                }
                            }
                            self.term_to_terms.insert(t.clone(), vec![t.clone()]);
                        }
                        self.add_term(&t);
                    }
                    _ =>{
                        // println!("cur op: {}", t.op);
                        for c in t.cs.iter(){
                            if let Op::Call(..) = t.op{
                                continue;
                            } else{
                                // println!("op: {}", c.op);
                                let terms = self.term_to_terms.get(c).unwrap();
                                assert_eq!(terms.len(), 1);
                                self.def_use.insert((terms[0].clone(), t.clone()));
                            }
                        }
                        self.term_to_terms.insert(t.clone(), vec![t.clone()]);
                        self.add_term(&t);
                    }
                }
            }
        }
    }

    fn construct_def_uses(&mut self){
        for (def, _use) in self.def_use.iter(){
            if self.def_uses.contains_key(def){
                self.def_uses.get_mut(def).unwrap().insert(_use.clone());
            } else {
                let mut uses: FxHashSet<Term> = FxHashSet::default();
                uses.insert(_use.clone());
                self.def_uses.insert(def.clone(), uses);
            }
        }
    }

    fn construct_use_defs(&mut self){
        for (def, _use) in self.def_use.iter(){
            if self.use_defs.contains_key(_use){
                self.use_defs.get_mut(_use).unwrap().insert(def.clone());
            } else {
                let mut defs: FxHashSet<Term> = FxHashSet::default();
                defs.insert(def.clone());
                self.def_uses.insert(_use.clone(), defs);
            }
        }
    }

    fn add_term(&mut self, t: &Term){
        self.good_terms.insert(t.clone());
        let defs: FxHashSet<Term> = FxHashSet::default();
        let uses: FxHashSet<Term> = FxHashSet::default();
        self.def_uses.insert(t.clone(), uses);
        self.use_defs.insert(t.clone(), defs);
    }

}

pub fn is_good_term(t: &Term) -> bool{
    match t.op{
        Op::Const(Value::Tuple(_))
        | Op::Tuple
        | Op::Field(_)
        | Op::Update(_)
        | Op::Const(Value::Array(_))
        | Op::Store 
        | Op::Select
        | Op::Call(..) => false,
        _ => true
    }
}