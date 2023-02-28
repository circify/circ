use rug::Integer;

use fxhash::FxHashMap;
use fxhash::FxHashSet;

use crate::ir::term::*;

use std::cmp;
use std::collections::HashMap;
use std::time::Instant;

/// A post order iterater that skip the const index of select/store
pub struct PostOrderIterV3 {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIterV3 {
    /// Make an iterator over the descendents of `root`.
    pub fn new(roots: Vec<Term>) -> Self {
        Self {
            stack: roots.into_iter().map(|t| (false, t)).collect(),
            visited: TermSet::default(),
        }
    }
}

impl std::iter::Iterator for PostOrderIterV3 {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                if let Op::Select = t.op() {
                    if let Op::Const(Value::BitVector(_)) = &t.cs()[1].op() {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs()[0].clone()));
                        continue;
                    }
                } else if let Op::Store = t.op() {
                    if let Op::Const(Value::BitVector(_)) = &t.cs()[1].op() {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs()[0].clone()));
                        self.stack.push((false, last.cs()[2].clone()));
                        continue;
                    }
                }
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs().iter().map(|c| (false, c.clone())));
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

/// A post order iterater that skip the const index of select/store
pub struct PostOrderIterV2 {
    // (cs stacked, term)
    stack: Vec<(bool, Term)>,
    visited: TermSet,
}

impl PostOrderIterV2 {
    /// Make an iterator over the descendents of `root`.
    pub fn new(root: Term) -> Self {
        Self {
            stack: vec![(false, root)],
            visited: TermSet::default(),
        }
    }
}

impl std::iter::Iterator for PostOrderIterV2 {
    type Item = Term;
    fn next(&mut self) -> Option<Term> {
        while let Some((children_pushed, t)) = self.stack.last() {
            if self.visited.contains(t) {
                self.stack.pop();
            } else if !children_pushed {
                if let Op::Select = t.op() {
                    if let Op::Const(Value::BitVector(_)) = &t.cs()[1].op() {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs()[0].clone()));
                        continue;
                    }
                } else if let Op::Store = t.op() {
                    if let Op::Const(Value::BitVector(_)) = &t.cs()[1].op() {
                        self.stack.last_mut().unwrap().0 = true;
                        let last = self.stack.last().unwrap().1.clone();
                        self.stack.push((false, last.cs()[0].clone()));
                        self.stack.push((false, last.cs()[2].clone()));
                        continue;
                    }
                }
                self.stack.last_mut().unwrap().0 = true;
                let last = self.stack.last().unwrap().1.clone();
                self.stack
                    .extend(last.cs().iter().map(|c| (false, c.clone())));
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
/// A structure that maps the actual terms inside of array and tuple
pub struct DefUsesSubGraph {
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

impl DefUsesSubGraph {
    /// default constructor
    pub fn new() -> Self {
        Self {
            nodes: TermSet::default(),
            edges: TermMap::default(),
            outs: TermSet::default(),
            ins: TermSet::default(),
            def_use: FxHashSet::default(),
            def_uses: FxHashMap::default(),
        }
    }

    /// Insert nodes into DefUseSubGraph
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
            self.edges.insert(t.clone(), TermSet::default());
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
            self.def_uses
                .entry(d.clone())
                .or_insert_with(Vec::new)
                .push(u.clone());
        }
    }
}

/// Extend current dug to outer n level
pub fn extend_dusg(dusg: &DefUsesSubGraph, dug: &DefUsesGraph) -> DefUsesSubGraph {
    let mut new_g: DefUsesSubGraph = DefUsesSubGraph::new();
    new_g.nodes = dusg.nodes.clone();
    for t in dusg.ins.iter() {
        for d in dug.use_defs.get(t).unwrap().iter() {
            new_g.insert_node(d);
        }
    }
    for t in dusg.outs.iter() {
        for u in dug.def_uses.get(t).unwrap().iter() {
            new_g.insert_node(u);
        }
    }
    new_g.insert_edges(dug);
    new_g
}

#[derive(Clone)]
/// Def Use Graph for a computation
pub struct DefUsesGraph {
    // pub term_to_terms_idx: TermMap<Vec<(Term, usize)>>,
    // term_to_terms: TermMap<Vec<(Term, usize)>>,
    // term_to_id: TermMap<usize>,
    // id_to_term: HashMap<usize, Term>,
    pub def_use: FxHashSet<(Term, Term)>,
    pub def_uses: FxHashMap<Term, FxHashSet<Term>>,
    pub use_defs: FxHashMap<Term, FxHashSet<Term>>,
    pub const_terms: TermSet,
    pub good_terms: TermSet,
    pub call_args: TermMap<Vec<FxHashSet<usize>>>,
    pub call_rets: TermMap<Vec<FxHashSet<usize>>>,
    pub call_args_terms: TermMap<Vec<Vec<Term>>>,
    pub call_rets_terms: TermMap<Vec<Vec<Term>>>,
    pub ret_good_terms: Vec<Term>,
    pub self_ins: Vec<FxHashSet<Term>>,
    pub self_outs: Vec<Vec<Term>>,
    pub call_rets_to_term: HashMap<(Term, usize, usize, usize), Term>,
    n_ref: TermMap<usize>,
    cache_t: Term,
    cache_terms: Vec<(Term, usize)>,
    cache_flag: bool,
    is_main: bool,
    var_used: TermMap<TermSet>,
    pub depth_bool: usize,
    pub depth_arith: usize,
    pub num_bool: usize,
    pub num_mul: usize,
    num_calls: usize,
}

impl DefUsesGraph {
    pub fn new(c: &Computation) -> Self {
        let mut now = Instant::now();
        let mut dug = Self {
            // term_to_terms_idx: TermMap::default(),
            // term_to_terms: TermMap::default(),
            def_use: FxHashSet::default(),
            def_uses: FxHashMap::default(),
            use_defs: FxHashMap::default(),
            const_terms: TermSet::default(),
            good_terms: TermSet::default(),
            call_args: TermMap::default(),
            call_rets: TermMap::default(),
            call_args_terms: TermMap::default(),
            call_rets_terms: TermMap::default(),
            ret_good_terms: Vec::new(),
            self_ins: Vec::new(),
            self_outs: Vec::new(),
            call_rets_to_term: HashMap::new(),
            n_ref: TermMap::default(),
            cache_t: leaf_term(Op::Eq),
            cache_terms: Vec::new(),
            cache_flag: false,
            is_main: true,
            var_used: TermMap::default(),
            depth_bool: 0,
            depth_arith: 0,
            num_bool: 0,
            num_mul: 0,
            num_calls: 1,
        };
        println!("Entering Def Use Graph:");
        dug.construct_def_use(c);
        dug.construct_mapping();
        println!("Time: Def Use Graph: {:?}", now.elapsed());
        println!("DefUseGraph depth bool: {:?}", dug.depth_bool);
        println!("DefUseGraph depth mul: {:?}", dug.depth_arith);
        println!("DefUseGraph num_bool: {:?}", dug.num_bool);
        println!("DefUseGraph num_mul: {:?}", dug.num_mul);
        dug
    }

    pub fn for_call_site(
        c: &Computation,
        dugs: &HashMap<String, DefUsesGraph>,
        fname: &String,
    ) -> Self {
        let mut now = Instant::now();
        let mut dug = Self {
            // term_to_terms_idx: TermMap::default(),
            // term_to_terms: TermMap::default(),
            def_use: FxHashSet::default(),
            def_uses: FxHashMap::default(),
            use_defs: FxHashMap::default(),
            const_terms: TermSet::default(),
            good_terms: TermSet::default(),
            call_args: TermMap::default(),
            call_rets: TermMap::default(),
            call_args_terms: TermMap::default(),
            call_rets_terms: TermMap::default(),
            ret_good_terms: Vec::new(),
            self_ins: Vec::new(),
            self_outs: Vec::new(),
            call_rets_to_term: HashMap::new(),
            n_ref: TermMap::default(),
            cache_t: leaf_term(Op::Eq),
            cache_terms: Vec::new(),
            cache_flag: false,
            is_main: fname == "main",
            var_used: TermMap::default(),
            depth_bool: 0,
            depth_arith: 0,
            num_bool: 0,
            num_mul: 0,
            num_calls: 1,
        };
        dug.construct_def_use_with_dugs(c, dugs);
        // moved this after insert context
        println!("Time: Def Use Graph: {:?}", now.elapsed());
        now = Instant::now();
        dug.construct_mapping();
        println!("Time: Def Use Graph mapping: {:?}", now.elapsed());
        println!("DefUseGraph depth bool: {:?}", dug.depth_bool);
        println!("DefUseGraph depth mul: {:?}", dug.depth_arith);
        println!("DefUseGraph num_bool: {:?}", dug.num_bool);
        println!("DefUseGraph num_mul: {:?}", dug.num_mul);
        dug
    }

    pub fn set_num_calls(&mut self, cnt: &usize) {
        self.num_calls = *cnt;
    }
    pub fn get_k(&self) -> FxHashMap<String, f64> {
        let mut k_map: FxHashMap<String, f64> = FxHashMap::default();
        let max_k: f64 = 1.0;
        k_map.insert(
            "a".to_string(),
            max_k.min((self.depth_arith as f64) / ((self.num_mul * self.num_calls) as f64)),
        );
        k_map.insert(
            "b".to_string(),
            max_k.min((self.depth_bool as f64) / ((self.num_bool * self.num_calls) as f64)),
        );
        println!("num_calls: {}", self.num_calls);
        println!("k_map: {:?}", k_map);
        k_map
    }

    // Cnt # of refs for each term
    fn construct_n_ref(&mut self, c: &Computation) {
        for t in PostOrderIterV3::new(c.outputs.clone()) {
            for arg in t.cs().iter() {
                *self.n_ref.entry(arg.clone()).or_insert(0) += 1;
            }
        }
        for out in c.outputs.iter() {
            *self.n_ref.entry(out.clone()).or_insert(0) += 1;
        }
    }

    fn get_and_de_ref(
        &mut self,
        term_to_terms: &mut TermMap<Vec<(Term, usize, usize, usize)>>,
        t: &Term,
    ) -> Vec<(Term, usize, usize, usize)> {
        let cnt = self.n_ref.get_mut(t).unwrap();
        *cnt -= 1;
        if *cnt == 0 {
            term_to_terms.remove(t).unwrap()
        } else {
            term_to_terms.get(t).unwrap().clone()
        }
        // if t.clone() == self.cache_t{
        //     if *cnt == 1{
        //         self.cache_flag = false;
        //     }
        //     self.cache_terms.clone()
        // } else{
        //     self.term_to_terms.get(t).unwrap().clone()
        // }
        // term_to_terms.get(t).clone().unwrap_or_else(||{
        //     if cnt == 1{
        //         self.cache_flag = false;
        //     }
        //     &self.cache_terms
        // }).clone()
    }

    fn construct_def_use_with_dugs(
        &mut self,
        c: &Computation,
        dugs: &HashMap<String, DefUsesGraph>,
    ) {
        // let mut t_const = Duration::ZERO;
        // let mut t_field = Duration::ZERO;
        // let mut t_tuple = Duration::ZERO;
        // let mut t_update = Duration::ZERO;
        // let mut t_store = Duration::ZERO;
        // let mut t_select1 = Duration::ZERO;
        // let mut t_select2 = Duration::ZERO;
        // let mut t_select3 = Duration::ZERO;
        // let mut t_call = Duration::ZERO;
        // let mut t_ite = Duration::ZERO;
        // let mut t_other = Duration::ZERO;

        // let mut n_const = 0;
        // let mut n_field = 0;
        // let mut n_tuple = 0;
        // let mut n_update =0;
        // let mut n_store = 0;
        // let mut n_select =0;
        // let mut n_call = 0;
        // let mut n_ite = 0;
        // let mut n_other = 0;

        // let mut now = Instant::now();
        self.construct_n_ref(c);
        // println!("Construct n_ref time: {:?}", now.elapsed());
        // let for_now = Instant::now();
        let mut term_to_terms: TermMap<Vec<(Term, usize, usize, usize)>> = TermMap::default();
        for t in PostOrderIterV3::new(c.outputs().clone()) {
            match &t.op() {
                Op::Var(..) => {
                    term_to_terms.insert(t.clone(), vec![(t.clone(), 0, 0, 0)]);
                    if self.is_main {
                        self.add_term(&t);
                    }
                }
                Op::Const(Value::BitVector(_)) => {
                    term_to_terms.insert(t.clone(), vec![(t.clone(), 0, 0, 0)]);
                    self.add_term(&t);
                }
                Op::Const(Value::Tuple(tup)) => {
                    // now = Instant::now();
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    for val in tup.iter() {
                        terms.push((leaf_term(Op::Const(val.clone())), 0, 0, 0));
                        self.const_terms.insert(leaf_term(Op::Const(val.clone())));
                        // self.add_term(&leaf_term(Op::Const(val.clone())));
                    }
                    term_to_terms.insert(t.clone(), terms);
                    // t_const += now.elapsed();
                    // n_const +=1;
                }
                Op::Tuple => {
                    // now = Instant::now();
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    for c in t.cs().iter() {
                        terms.extend(self.get_and_de_ref(&mut term_to_terms, &c));
                    }
                    term_to_terms.insert(t.clone(), terms);
                    // t_tuple += now.elapsed();
                    // n_tuple +=1;
                }
                Op::Field(i) => {
                    // now = Instant::now();
                    let tuple_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    // println!("field child: {}", t.cs[0].op);
                    let tuple_sort = check(&t.cs()[0]);
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
                    term_to_terms.insert(t.clone(), field_terms.to_vec());
                    // t_field += now.elapsed();
                    // n_field +=1;
                }
                Op::Update(i) => {
                    // now = Instant::now();
                    let mut tuple_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    let value_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                    tuple_terms[*i] = value_terms[0].clone();
                    term_to_terms.insert(t.clone(), tuple_terms);
                    // t_update += now.elapsed();
                    // n_update +=1;
                }
                Op::Const(Value::Array(arr)) => {
                    // now = Instant::now();
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    let sort = check(&t);
                    if let Sort::Array(_, _, n) = sort {
                        // println!("Create a {} size array.", n);
                        let n = n as i32;
                        for i in 0..n {
                            let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                            let v = match arr.map.get(&idx) {
                                Some(c) => c,
                                None => &*arr.default,
                            };
                            terms.push((leaf_term(Op::Const(v.clone())), 0, 0, 0));
                            self.const_terms.insert(leaf_term(Op::Const(v.clone())));
                            // self.add_term(&leaf_term(Op::Const(v.clone())));
                        }
                    } else {
                        todo!("Const array sort not array????")
                    }
                    term_to_terms.insert(t.clone(), terms);
                    // t_const += now.elapsed();
                    // n_const +=1;
                }
                Op::Store => {
                    // now = Instant::now();
                    let mut array_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    let value_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[2]);
                    if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        // println!("Store the {} value on a  {} size array.",idx , array_terms.len());
                        array_terms[idx] = value_terms[0].clone();
                        term_to_terms.insert(t.clone(), array_terms);
                    } else {
                        self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        for idx in 0..array_terms.len() {
                            // self.def_use.insert((array_terms[idx].0.clone(), t.clone()));
                            self.add_def_use(&array_terms[idx].0, &t);
                            array_terms[idx] =
                                (t.clone(), 0, array_terms[idx].2 + 1, array_terms[idx].3);
                        }
                        self.def_use.insert((value_terms[0].0.clone(), t.clone()));
                        term_to_terms.insert(t.clone(), array_terms);
                        // self.add_term(&t);
                    }
                    // t_store += now.elapsed();
                    // n_store +=1;
                }
                Op::Select => {
                    let array_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        term_to_terms.insert(t.clone(), vec![array_terms[idx].clone()]);
                    } else {
                        self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        let mut depth_bool: usize = 0;
                        let mut depth_arith: usize = 0;
                        for idx in 0..array_terms.len() {
                            // self.def_use.insert((array_terms[idx].0.clone(), t.clone()));
                            self.add_def_use(&array_terms[idx].0, &t);
                            depth_bool = cmp::max(depth_bool, array_terms[idx].2);
                            depth_arith = cmp::max(depth_arith, array_terms[idx].3)
                        }
                        term_to_terms
                            .insert(t.clone(), vec![(t.clone(), 0, depth_bool + 1, depth_arith)]);
                        // self.add_term(&t);
                    }
                }
                Op::Call(callee, _, ret_sorts) => {
                    // Use call term itself as the placeholder
                    // Call term will be ignore by the ilp solver later
                    let mut ret_terms: Vec<(Term, usize)> = Vec::new();
                    let num_rets: usize = ret_sorts.iter().map(|ret| get_sort_len(ret)).sum();

                    // call site
                    let mut args: Vec<FxHashSet<usize>> = Vec::new();
                    let mut rets: Vec<FxHashSet<usize>> = Vec::new();
                    let mut args_t: Vec<Vec<Term>> = Vec::new();
                    let mut rets_t: Vec<Vec<Term>> = Vec::new();

                    // context inside the call
                    let context_args = dugs.get(callee).unwrap().self_ins.clone();
                    let context_rets = dugs.get(callee).unwrap().self_outs.clone();

                    // args -> call's in
                    let mut arg_id = 0;
                    let mut depth_bool: usize = 0;
                    let mut depth_arith: usize = 0;
                    for arg in t.cs().clone().iter() {
                        // Inlining callee's use
                        let arg_terms = self.get_and_de_ref(&mut term_to_terms, arg);
                        for tu in arg_terms.iter() {
                            // Ignore terms ret from a call
                            if !self.call_rets_to_term.contains_key(tu) {
                                let uses = context_args.get(arg_id).unwrap();
                                for u in uses.iter() {
                                    // println!("DEF USE: {}, {}", d.op, u.op);
                                    // self.def_use.insert((tu.0.clone(), u.clone()));
                                    // self.add_term(u);
                                    self.add_def_use(&tu.0, &u);
                                }
                                arg_id += 1;
                            }
                            depth_bool = cmp::max(depth_bool, tu.2);
                            depth_arith = cmp::max(depth_arith, tu.3);
                        }

                        // Safe call site
                        let mut arg_set: FxHashSet<usize> = FxHashSet::default();
                        let mut arg_vec: Vec<Term> = Vec::new();
                        for aarg in arg_terms.iter() {
                            arg_set.insert(get_op_id(&aarg.0.op()));
                            arg_vec.push(aarg.0.clone());
                        }
                        args_t.push(arg_vec);
                        args.push(arg_set);
                    }

                    // for _ in 0..num_rets {
                    //     rets.push(FxHashSet::default());
                    //     rets_t.push(Vec::new());
                    // }

                    let mut idx = 0;
                    // println!("{:?}", context_rets);
                    let ret_terms: Vec<(Term, usize, usize, usize)> = context_rets
                        .into_iter()
                        .flatten()
                        .map(|ret| {
                            // self.add_term(&ret);
                            let tu = (ret, idx, depth_bool, depth_arith);
                            idx += 1;
                            self.call_rets_to_term.insert(tu.clone(), t.clone());
                            rets.push(FxHashSet::default());
                            rets_t.push(Vec::new());
                            tu
                        })
                        .collect();

                    // for ret_t in ret_terms.iter() {
                    //     self.call_rets_to_term.insert(ret_t.clone(), t.clone());
                    // }

                    assert_eq!(num_rets, ret_terms.len());

                    term_to_terms.insert(t.clone(), ret_terms);
                    self.call_args.insert(t.clone(), args);
                    self.call_rets.insert(t.clone(), rets);
                    self.call_args_terms.insert(t.clone(), args_t);
                    self.call_rets_terms.insert(t.clone(), rets_t);
                }
                Op::Ite => {
                    if let Op::Store = t.cs()[1].op() {
                        // assert_eq!(t.cs[2].op, Op::Store);
                        let cond_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                        assert_eq!(cond_terms.len(), 1);
                        self.def_use.insert((cond_terms[0].0.clone(), t.clone()));
                        // true branch
                        let mut t_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        // false branch
                        let f_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[2]);
                        assert_eq!(t_terms.len(), f_terms.len());
                        for idx in 0..t_terms.len() {
                            // self.def_use.insert((t_terms[idx].0.clone(), t.clone()));
                            // self.def_use.insert((f_terms[idx].0.clone(), t.clone()));
                            self.add_def_use(&t_terms[idx].0, &t);
                            self.add_def_use(&f_terms[idx].0, &t);
                            t_terms[idx] = (t.clone(), 0, t_terms[idx].2 + 1, t_terms[idx].3);
                        }
                        term_to_terms.insert(t.clone(), t_terms);
                    } else {
                        let mut depth_bool: usize = 0;
                        let mut depth_arith: usize = 0;
                        for c in t.cs().iter() {
                            let terms = self.get_and_de_ref(&mut term_to_terms, c);
                            assert_eq!(terms.len(), 1);
                            if let Some(call_t) = self.call_rets_to_term.get(&terms[0]) {
                                // insert op to ret set
                                let rets = self.call_rets.get_mut(&call_t).unwrap();
                                rets.get_mut(terms[0].1).unwrap().insert(get_op_id(&t.op()));
                                // insert term to ret terms
                                let rets_t = self.call_rets_terms.get_mut(&call_t).unwrap();
                                rets_t.get_mut(terms[0].1).unwrap().push(t.clone());
                                // self.add_term(&terms[0].0);
                                // self.def_use.insert((terms[0].0.clone(), t.clone()));
                                self.add_def_use(&terms[0].0, &t);
                            } else {
                                // self.def_use.insert((terms[0].0.clone(), t.clone()));
                                self.add_def_use(&terms[0].0, &t);
                            }
                            depth_bool = cmp::max(depth_bool, terms[0].2);
                            depth_arith = cmp::max(depth_arith, terms[0].3);
                        }
                        term_to_terms
                            .insert(t.clone(), vec![(t.clone(), 0, depth_bool + 1, depth_arith)]);
                    }
                    // self.add_term(&t);
                }
                _ => {
                    let mut depth_bool: usize = 0;
                    let mut depth_arith: usize = 0;
                    for c in t.cs().iter() {
                        let terms = self.get_and_de_ref(&mut term_to_terms, c);
                        assert_eq!(terms.len(), 1);
                        if let Some(call_t) = self.call_rets_to_term.get(&terms[0]) {
                            // insert op to ret set
                            let rets = self.call_rets.get_mut(&call_t).unwrap();
                            rets.get_mut(terms[0].1).unwrap().insert(get_op_id(&t.op()));
                            // insert term to ret terms
                            let rets_t = self.call_rets_terms.get_mut(&call_t).unwrap();
                            rets_t.get_mut(terms[0].1).unwrap().push(t.clone());
                            // self.add_term(&terms[0].0);
                            // self.def_use.insert((terms[0].0.clone(), t.clone()));
                            self.add_def_use(&terms[0].0, &t);
                        } else {
                            // self.def_use.insert((terms[0].0.clone(), t.clone()));
                            self.add_def_use(&terms[0].0, &t);
                        }
                        depth_bool = cmp::max(depth_bool, terms[0].2);
                        depth_arith = cmp::max(depth_arith, terms[0].3);
                    }
                    match &t.clone().op() {
                        Op::BvNaryOp(BvNaryOp::Mul) => {
                            term_to_terms.insert(
                                t.clone(),
                                vec![(t.clone(), 0, depth_bool + 1, depth_arith + 1)],
                            );
                        }
                        _ => {
                            term_to_terms.insert(
                                t.clone(),
                                vec![(t.clone(), 0, depth_bool + 1, depth_arith)],
                            );
                        }
                    }
                    // self.add_term(&t);
                }
            }
        }
        for out in c.outputs().iter() {
            let out_terms = self.get_and_de_ref(&mut term_to_terms, out);
            let mut out_v: Vec<Term> = Vec::new();
            for (t, _, depth_bool, depth_arith) in out_terms.iter() {
                // v.push(t.clone());
                self.ret_good_terms.push(t.clone());
                out_v.push(t.clone());
                self.depth_bool = cmp::max(self.depth_bool, *depth_bool);
                self.depth_arith = cmp::max(self.depth_arith, *depth_arith);
            }
            self.self_outs.push(out_v);
        }
    }

    fn construct_def_use(&mut self, c: &Computation) {
        self.construct_n_ref(c);
        let mut term_to_terms: TermMap<Vec<(Term, usize, usize, usize)>> = TermMap::default();
        for t in PostOrderIterV3::new(c.outputs().clone()) {
            match &t.op() {
                Op::Const(Value::Tuple(tup)) => {
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    for val in tup.iter() {
                        terms.push((leaf_term(Op::Const(val.clone())), 0, 0, 0));
                        self.const_terms.insert(leaf_term(Op::Const(val.clone())));
                        self.add_term(&leaf_term(Op::Const(val.clone())));
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Tuple => {
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    for c in t.cs().iter() {
                        terms.extend(self.get_and_de_ref(&mut term_to_terms, &c));
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Field(i) => {
                    let tuple_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);

                    let tuple_sort = check(&t.cs()[0]);
                    let (offset, len) = match tuple_sort {
                        Sort::Tuple(t) => {
                            // println!("{} < {}", *i, t.len());

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
                    term_to_terms.insert(t.clone(), field_terms.to_vec());
                }
                Op::Update(i) => {
                    let mut tuple_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    let value_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                    tuple_terms[*i] = value_terms[0].clone();
                    term_to_terms.insert(t.clone(), tuple_terms);
                }
                Op::Const(Value::Array(arr)) => {
                    let mut terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    let sort = check(&t);
                    if let Sort::Array(_, _, n) = sort {
                        // println!("Create a {} size array.", n);
                        let n = n as i32;
                        for i in 0..n {
                            let idx = Value::BitVector(BitVector::new(Integer::from(i), 32));
                            let v = match arr.map.get(&idx) {
                                Some(c) => c,
                                None => &*arr.default,
                            };
                            terms.push((leaf_term(Op::Const(v.clone())), 0, 0, 0));
                            self.const_terms.insert(leaf_term(Op::Const(v.clone())));
                            self.add_term(&leaf_term(Op::Const(v.clone())));
                        }
                    } else {
                        todo!("Const array sort not array????")
                    }
                    term_to_terms.insert(t.clone(), terms);
                }
                Op::Store => {
                    // now = Instant::now();
                    let mut array_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    let value_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[2]);
                    if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        // println!("Store the {} value on a  {} size array.",idx , array_terms.len());
                        array_terms[idx] = value_terms[0].clone();
                        term_to_terms.insert(t.clone(), array_terms);
                    } else {
                        self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        for idx in 0..array_terms.len() {
                            // self.def_use.insert((array_terms[idx].0.clone(), t.clone()));
                            self.add_def_use(&array_terms[idx].0, &t);
                            array_terms[idx] =
                                (t.clone(), 0, array_terms[idx].2 + 1, array_terms[idx].3);
                        }
                        self.def_use.insert((value_terms[0].0.clone(), t.clone()));
                        term_to_terms.insert(t.clone(), array_terms);
                        // self.add_term(&t);
                    }
                    // t_store += now.elapsed();
                    // n_store +=1;
                }
                Op::Select => {
                    let array_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                    if let Op::Const(Value::BitVector(bv)) = &t.cs()[1].op() {
                        // constant indexing
                        let idx = bv.uint().to_usize().unwrap().clone();
                        term_to_terms.insert(t.clone(), vec![array_terms[idx].clone()]);
                    } else {
                        self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        let mut depth_bool: usize = 0;
                        let mut depth_arith: usize = 0;
                        for idx in 0..array_terms.len() {
                            // self.def_use.insert((array_terms[idx].0.clone(), t.clone()));
                            self.add_def_use(&array_terms[idx].0, &t);
                            depth_bool = cmp::max(depth_bool, array_terms[idx].2);
                            depth_arith = cmp::max(depth_arith, array_terms[idx].3)
                        }
                        term_to_terms
                            .insert(t.clone(), vec![(t.clone(), 0, depth_bool + 1, depth_arith)]);
                        // self.add_term(&t);
                    }
                }
                Op::Call(_, _, ret_sorts) => {
                    // Use call term itself as the placeholder
                    // Call term will be ignore by the ilp solver later
                    let mut ret_terms: Vec<(Term, usize, usize, usize)> = Vec::new();
                    let num_rets: usize = ret_sorts.iter().map(|ret| get_sort_len(ret)).sum();
                    let mut args: Vec<FxHashSet<usize>> = Vec::new();
                    let mut rets: Vec<FxHashSet<usize>> = Vec::new();
                    let mut args_t: Vec<Vec<Term>> = Vec::new();
                    let mut rets_t: Vec<Vec<Term>> = Vec::new();
                    let mut depth_bool: usize = 0;
                    let mut depth_arith: usize = 0;
                    for c in t.cs().iter() {
                        let arg_terms = self.get_and_de_ref(&mut term_to_terms, c);
                        let mut arg_set: FxHashSet<usize> = FxHashSet::default();
                        let mut arg_term: Vec<Term> = Vec::new();
                        for arg in arg_terms.iter() {
                            arg_set.insert(get_op_id(&arg.0.op()));
                            arg_term.push(arg.0.clone());
                            depth_bool = cmp::max(depth_bool, arg.2);
                            depth_arith = cmp::max(depth_arith, arg.3);
                        }
                        args_t.push(arg_term);
                        args.push(arg_set);
                    }
                    for idx in 0..num_rets {
                        rets.push(FxHashSet::default());
                        ret_terms.push((t.clone(), idx, depth_bool, depth_arith));
                        rets_t.push(Vec::new());
                    }
                    term_to_terms.insert(t.clone(), ret_terms);
                    self.call_args.insert(t.clone(), args);
                    self.call_rets.insert(t.clone(), rets);
                    self.call_args_terms.insert(t.clone(), args_t);
                    self.call_rets_terms.insert(t.clone(), rets_t);
                }
                Op::Ite => {
                    if let Op::Store = t.cs()[1].op() {
                        // assert_eq!(t.cs[2].op, Op::Store);
                        let cond_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[0]);
                        assert_eq!(cond_terms.len(), 1);
                        self.def_use.insert((cond_terms[0].0.clone(), t.clone()));
                        // true branch
                        let mut t_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[1]);
                        // false branch
                        let f_terms = self.get_and_de_ref(&mut term_to_terms, &t.cs()[2]);
                        assert_eq!(t_terms.len(), f_terms.len());
                        for idx in 0..t_terms.len() {
                            self.def_use.insert((t_terms[idx].0.clone(), t.clone()));
                            self.def_use.insert((f_terms[idx].0.clone(), t.clone()));
                            t_terms[idx] = (t.clone(), 0, t_terms[idx].2 + 1, t_terms[idx].3 + 1);
                        }
                        term_to_terms.insert(t.clone(), t_terms);
                    } else {
                        let mut depth_bool: usize = 0;
                        let mut depth_arith: usize = 0;
                        for c in t.cs().iter() {
                            if let Op::Call(..) = t.op() {
                                continue;
                            } else {
                                let terms = self.get_and_de_ref(&mut term_to_terms, c);
                                assert_eq!(terms.len(), 1);
                                if let Op::Call(..) = terms[0].0.op() {
                                    // insert op to ret set
                                    let rets = self.call_rets.get_mut(&terms[0].0).unwrap();
                                    rets.get_mut(terms[0].1).unwrap().insert(get_op_id(&t.op()));
                                    // insert term to ret terms
                                    let rets_t = self.call_rets_terms.get_mut(&terms[0].0).unwrap();
                                    rets_t.get_mut(terms[0].1).unwrap().push(t.clone());
                                } else {
                                    self.def_use.insert((terms[0].0.clone(), t.clone()));
                                }
                                depth_bool = cmp::max(depth_bool, terms[0].2);
                                depth_arith = cmp::max(depth_arith, terms[0].3);
                            }
                        }
                        term_to_terms
                            .insert(t.clone(), vec![(t.clone(), 0, depth_bool + 1, depth_arith)]);
                    }
                    self.add_term(&t);
                }
                _ => {
                    let mut depth_bool: usize = 0;
                    let mut depth_arith: usize = 0;
                    for c in t.cs().iter() {
                        if let Op::Call(..) = c.op() {
                            continue;
                        } else {
                            let terms = self.get_and_de_ref(&mut term_to_terms, c);
                            assert_eq!(terms.len(), 1);
                            if let Op::Call(..) = terms[0].0.op() {
                                // insert op to ret set
                                let rets = self.call_rets.get_mut(&terms[0].0).unwrap();
                                rets.get_mut(terms[0].1).unwrap().insert(get_op_id(&t.op()));
                                // insert term to ret terms
                                let rets_t = self.call_rets_terms.get_mut(&terms[0].0).unwrap();
                                rets_t.get_mut(terms[0].1).unwrap().push(t.clone());
                            } else {
                                self.def_use.insert((terms[0].0.clone(), t.clone()));
                            }
                            depth_bool = cmp::max(depth_bool, terms[0].2);
                            depth_arith = cmp::max(depth_arith, terms[0].3);
                        }
                    }
                    match &t.clone().op() {
                        Op::BvNaryOp(BvNaryOp::Mul) => {
                            term_to_terms.insert(
                                t.clone(),
                                vec![(t.clone(), 0, depth_bool + 1, depth_arith + 1)],
                            );
                        }
                        _ => {
                            term_to_terms.insert(
                                t.clone(),
                                vec![(t.clone(), 0, depth_bool + 1, depth_arith)],
                            );
                        }
                    }
                    self.add_term(&t);
                }
            }
        }

        for out in c.outputs().iter() {
            let out_terms = self.get_and_de_ref(&mut term_to_terms, out);
            let mut out_v: Vec<Term> = Vec::new();
            for (t, _, depth_bool, depth_arith) in out_terms.iter() {
                // v.push(t.clone());
                self.ret_good_terms.push(t.clone());
                out_v.push(t.clone());
                self.depth_bool = cmp::max(self.depth_bool, *depth_bool);
                self.depth_arith = cmp::max(self.depth_arith, *depth_arith);
            }
            self.self_outs.push(out_v);
        }

        // for (k, _) in self.term_to_terms.iter(){
        //     println!("Left over ts: {} {}", k.op, self.n_ref.get(k).unwrap());
        // }
        // todo!("TEsting")

        println!("Def Use Graph # of terms: {}", self.good_terms.len());
        println!("Def Use Graph # of edges: {}", self.def_use.len());
    }

    fn construct_mapping(&mut self) {
        for (def, _use) in self.def_use.iter() {
            if self.def_uses.contains_key(def) {
                self.def_uses.get_mut(def).unwrap().insert(_use.clone());
            } else {
                let mut uses: FxHashSet<Term> = FxHashSet::default();
                uses.insert(_use.clone());
                self.def_uses.insert(def.clone(), uses);
            }
            if self.use_defs.contains_key(_use) {
                self.use_defs.get_mut(_use).unwrap().insert(def.clone());
            } else {
                let mut defs: FxHashSet<Term> = FxHashSet::default();
                defs.insert(def.clone());
                self.def_uses.insert(_use.clone(), defs);
            }
        }
    }

    pub fn gen_in_out(&mut self, c: &Computation) {
        for n in c.metadata.computation_arg_names.iter() {
            // n is already a ssa name here
            let s = c.metadata.input_sort(n).clone();
            let t = leaf_term(Op::Var(n.clone(), s));
            if let Some(uses) = self.def_uses.get(&t) {
                self.self_ins.push(uses.clone());
            } else {
                // This argument is not being used at all!
                self.self_ins.push(FxHashSet::default());
            }
        }
    }

    /// Out put the call site from this function's computation
    pub fn get_call_site(
        &mut self,
    ) -> Vec<(
        String,
        Vec<usize>,
        Vec<Vec<Term>>,
        Vec<usize>,
        Vec<Vec<Term>>,
        Term,
    )> {
        let mut call_sites: Vec<(
            String,
            Vec<usize>,
            Vec<Vec<Term>>,
            Vec<usize>,
            Vec<Vec<Term>>,
            Term,
        )> = Vec::new();

        for (t, args_set) in self.call_args.iter() {
            // Stupid implementation, Should fix this
            if let Op::Call(fname, _, _) = &t.op() {
                let rets_set = self.call_rets.get(t).unwrap();
                let mut rets: Vec<usize> = Vec::new();
                let mut args: Vec<usize> = Vec::new();
                for s in rets_set.iter() {
                    let mut v: Vec<usize> = s.clone().into_iter().collect();
                    v.sort();
                    rets.extend(v);
                }
                for s in args_set.iter() {
                    let mut v: Vec<usize> = s.clone().into_iter().collect();
                    v.sort();
                    args.extend(v);
                }

                let args_t = self.call_args_terms.get(t).unwrap().clone();
                let rets_t = self.call_rets_terms.get(t).unwrap().clone();
                call_sites.push((fname.clone(), args, args_t, rets, rets_t, t.clone()));
            }
        }
        call_sites
    }

    /// insert the caller's context
    pub fn insert_context(
        &mut self,
        arg_names: &Vec<String>,
        arg_values: &Vec<Vec<Term>>,
        rets: &Vec<Vec<Term>>,
        caller_dug: &DefUsesGraph,
        callee: &Computation,
        extra_level: usize,
    ) {
        let mut input_set: TermSet = TermSet::default();
        let mut output_set: TermSet = TermSet::default();
        // insert def of args
        for (n, v) in arg_names.into_iter().zip(arg_values) {
            let ssa_names = callee.metadata.input_ssa_name_from_nice_name(n);
            for (sname, index) in ssa_names.iter() {
                let s = callee.metadata.input_sort(&sname).clone();
                // println!("Def: {}, Use: {}", v.get(*index).unwrap(), leaf_term(Op::Var(sname.clone(), s.clone())));
                let def_t = v.get(*index).unwrap().clone();
                let use_t = leaf_term(Op::Var(sname.clone(), s));
                if let Op::Call(..) = def_t.op {
                    continue;
                }
                if let Op::Var(..) = def_t.op {
                    continue;
                }
                if let Op::Const(_) = def_t.op {
                    continue;
                }
                // if !self.good_terms.contains(&use_t) {
                //     // println!("FIX: {}", use_t.op);
                //     // This is because the function doesn't use this arg
                //     //todo!("Fix this...");
                //     continue;
                // }
                if let Some(actual_used) = self.var_used.clone().get(&use_t) {
                    for actual_t in actual_used.iter() {
                        self.add_term(&def_t);
                        self.def_use.insert((def_t.clone(), actual_t.clone()));
                        input_set.insert(def_t.clone());
                    }
                }
            }
        }

        // insert use of rets
        let outs = self.ret_good_terms.clone();

        assert_eq!(outs.len(), rets.len());
        for (d, uses) in outs.into_iter().zip(rets) {
            for u in uses.iter() {
                // TODO: so weird
                self.add_term(&d);
                self.add_term(u);
                self.def_use.insert((d.clone(), u.clone()));
            }
        }

        // kind of mutation?
        // for i in 1..extra_level {
        //     // insert def of def
        //     for def in input_set.clone().iter() {
        //         let def_defs = caller_dug.def_uses.get(def).unwrap();
        //         for def_def in def_defs.iter() {
        //             self.add_term(def_def);
        //             self.def_use.insert((def_def.clone(), def.clone()));
        //             input_set.insert(def_def.clone());
        //         }
        //     }

        //     // insert use of use
        //     for _use in output_set.clone().iter() {
        //         let use_uses = caller_dug.def_uses.get(_use).unwrap();
        //         for use_use in use_uses.iter() {
        //             self.add_term(use_use);
        //             self.def_use.insert((_use.clone(), use_use.clone()));
        //             input_set.insert(use_use.clone());
        //         }
        //     }
        // }
        self.construct_mapping();
    }

    fn add_term(&mut self, t: &Term) {
        if !self.good_terms.contains(t) {
            self.good_terms.insert(t.clone());
            let defs: FxHashSet<Term> = FxHashSet::default();
            let uses: FxHashSet<Term> = FxHashSet::default();
            self.def_uses.insert(t.clone(), uses);
            self.use_defs.insert(t.clone(), defs);
            match &t.op() {
                Op::Ite => self.num_bool += 1,
                Op::BvNaryOp(o) => {
                    match o {
                        BvNaryOp::Xor => {
                            self.num_bool += 0;
                        }
                        BvNaryOp::Or => {
                            self.num_bool += 1;
                        }
                        BvNaryOp::And => {
                            self.num_bool += 1;
                        }
                        BvNaryOp::Add => {
                            // self.num_bool += 1;
                        }
                        BvNaryOp::Mul => {
                            // self.num_bool += 1;
                            self.num_mul += 1;
                        }
                    }
                }
                Op::BvBinOp(o) => {
                    match o {
                        BvBinOp::Sub => {
                            // self.num_bool += 1;
                        }
                        BvBinOp::Udiv => {
                            self.num_bool += 1;
                        }
                        BvBinOp::Urem => {
                            self.num_bool += 1;
                        }
                        _ => {}
                    }
                }
                Op::Eq => {
                    self.num_bool += 1;
                }
                Op::BvBinPred(_) => {
                    self.num_bool += 1;
                }
                Op::Store | Op::Select => {
                    if let Sort::Array(_, _, length) = check(&t.cs()[0]) {
                        self.num_bool += length;
                    }
                    // self.num_bool += 1;
                }
                _ => {}
            }
        }
    }

    fn add_def_use(&mut self, d: &Term, u: &Term) {
        if self.is_main {
            self.add_term(d);
            self.add_term(u);
            self.def_use.insert((d.clone(), u.clone()));
        } else {
            if let Op::Var(..) = d.op() {
                self.add_term(u);
                if self.var_used.contains_key(d) {
                    self.var_used.get_mut(d).unwrap().insert(u.clone());
                } else {
                    let mut var_used_set: TermSet = TermSet::default();
                    var_used_set.insert(u.clone());
                    self.var_used.insert(d.clone(), var_used_set);
                }
                return;
            } else {
                self.add_term(d);
                self.add_term(u);
                self.def_use.insert((d.clone(), u.clone()));
            }
        }
    }
}

pub fn is_good_term(t: &Term) -> bool {
    match t.op() {
        Op::Const(Value::Tuple(_))
        | Op::Tuple
        | Op::Field(_)
        | Op::Update(_)
        | Op::Const(Value::Array(_))
        | Op::Store
        | Op::Select
        | Op::Call(..) => false,
        _ => true,
    }
}

pub fn get_op_id(op: &Op) -> usize {
    match op {
        Op::Var(..) => 1,
        Op::Const(_) => 2,
        Op::Eq => 3,
        Op::Ite => 4,
        Op::Not => 5,
        Op::BoolNaryOp(o) => 6,
        Op::BvBinPred(o) => 7,
        Op::BvNaryOp(o) => 8,
        Op::BvBinOp(o) => 9,
        Op::Select => 10,
        Op::Store => 11,
        Op::Call(..) => 12,
        _ => todo!("What op?"),
    }
}
