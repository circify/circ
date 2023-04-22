//! Call Site Similarity

use crate::ir::term::*;
use crate::target::aby::assignment::def_uses::*;

use std::collections::HashMap;
use std::collections::HashSet;

#[derive(Clone)]
/// A structure that stores the context and all the call terms in one call site
struct CallSite {
    // Context's fname
    pub caller: String,
    pub callee: String,
    pub args: Vec<Vec<Term>>,
    pub rets: Vec<Vec<Term>>,
    pub calls: Vec<Term>,
    pub caller_dug: DefUsesGraph,
}

impl CallSite {
    pub fn new(
        caller: &String,
        callee: &String,
        args: &Vec<Vec<Term>>,
        rets: &Vec<Vec<Term>>,
        t: &Term,
        caller_dug: &DefUsesGraph,
    ) -> Self {
        Self {
            caller: caller.clone(),
            callee: callee.clone(),
            args: args.clone(),
            rets: rets.clone(),
            calls: vec![t.clone()],
            caller_dug: caller_dug.clone(),
        }
    }

    pub fn insert(&mut self, t: &Term) {
        self.calls.push(t.clone());
    }
}

pub struct CallSiteSimilarity {
    comps: Computations,
    dugs: HashMap<String, DefUsesGraph>,
    visited: HashSet<String>,
    call_sites: HashMap<(String, Vec<usize>, Vec<usize>), CallSite>,
    callee_caller: HashSet<(String, String)>,
    func_to_cs: HashMap<String, HashMap<usize, CallSite>>,
    dup_per_func: HashMap<String, usize>,
    call_cnt: HashMap<String, usize>,
    ml: usize,
}

impl CallSiteSimilarity {
    pub fn new(comps: &Computations, ml: &usize) -> Self {
        let mut css = Self {
            comps: comps.clone(),
            dugs: HashMap::new(),
            visited: HashSet::new(),
            call_sites: HashMap::new(),
            callee_caller: HashSet::new(),
            func_to_cs: HashMap::new(),
            dup_per_func: HashMap::new(),
            call_cnt: HashMap::new(),
            ml: ml.clone(),
        };
        css
    }

    fn traverse(&mut self, fname: &String) {
        *self.call_cnt.entry(fname.clone()).or_insert(0) += 1;
        let c = self.comps.get(fname).clone();
        for t in c.terms_postorder() {
            if let Op::Call(callee, ..) = &t.op() {
                self.traverse(&callee);
            }
        }
        if !self.visited.contains(fname) {
            println!("Building dug for {}", fname);
            let mut dug = DefUsesGraph::for_call_site(&c, &self.dugs, fname);
            dug.gen_in_out(&c);
            let cs: Vec<(Term, Vec<Vec<Term>>, Vec<Vec<Term>>)> = dug.get_call_site();
            for (t, args_t, rets_t) in cs.iter() {
                if let Op::Call(callee, _, _) = t.op() {
                    // convert term to op id
                    
                    let key: (String, Vec<usize>, Vec<usize>) =
                    (callee.clone(), to_key(args_t), to_key(rets_t));
                    if self.call_sites.contains_key(&key) {
                        self.call_sites.get_mut(&key).unwrap().insert(t);
                    } else {
                        // Use the first context
                        if let Op::Call(_, _, _) = &t.op() {
                            let cs = CallSite::new(fname, callee, args_t, rets_t, t, &dug);
                            self.call_sites.insert(key, cs);
                        }
                    }
                    // recording callee-caller
                    self.callee_caller.insert((callee.clone(), fname.clone()));
                }
            }
            self.dugs.insert(fname.clone(), dug);
            self.dup_per_func.insert(fname.clone(), 0);
            self.func_to_cs.insert(fname.clone(), HashMap::new());
            self.visited.insert(fname.clone());
        }
    }

    pub fn call_site_similarity_smart(&mut self) -> (Computations, HashMap<String, DefUsesGraph>) {
        let main = "main".to_string();
        self.traverse(&main);

        // Functions that have more than one call site
        let mut duplicated_f: HashSet<String> = HashSet::new();
        // Functions that need to be rewrote for calling to duplicated f
        // If a callee is duplicated, the caller need to be rewrote
        let mut rewriting_f: HashSet<String> = HashSet::new();
        let mut call_map: TermMap<usize> = TermMap::default();

        // Generating duplicate set
        for (key, cs) in self.call_sites.iter() {
            let call_id: usize = self.dup_per_func.get(&key.0).unwrap().clone();

            if call_id > 0 {
                // indicate this function need to be rewrote
                duplicated_f.insert(key.0.clone());
            }

            for t in cs.calls.iter() {
                call_map.insert(t.clone(), call_id);
            }
            self.dup_per_func.insert(key.0.clone(), call_id + 1);
            let id_to_cs = self.func_to_cs.get_mut(&key.0).unwrap();
            id_to_cs.insert(call_id, cs.clone());
        }

        // Generating rewriting set
        for (callee, caller) in self.callee_caller.iter() {
            if duplicated_f.contains(callee) {
                rewriting_f.insert(caller.clone());
            }
        }

        remap(
            &self.comps,
            &rewriting_f,
            &duplicated_f,
            &call_map,
            &self.call_cnt,
            &self.func_to_cs,
            self.ml,
        )
    }
}

/// Rewriting the call term to new call
fn rewrite_call(c: &mut Computation, call_map: &TermMap<usize>, duplicate_set: &HashSet<String>) {
    let mut cache = TermMap::<Term>::default();
    let mut children_added = TermSet::default();
    let mut stack = Vec::new();
    stack.extend(c.outputs.iter().cloned());
    while let Some(top) = stack.pop() {
        if !cache.contains_key(&top) {
            // was it missing?
            if children_added.insert(top.clone()) {
                stack.push(top.clone());
                stack.extend(top.cs().iter().filter(|c| !cache.contains_key(c)).cloned());
            } else {
                let get_children = || -> Vec<Term> {
                    top.cs()
                        .iter()
                        .map(|c| cache.get(c).unwrap())
                        .cloned()
                        .collect()
                };
                let new_t_op: Op = match &top.op() {
                    Op::Call(name, arg_sorts, ret_sorts) => {
                        let mut new_t = top.op().clone();
                        if duplicate_set.contains(name) {
                            if let Some(cid) = call_map.get(&top) {
                                let new_n = format_dup_call(name, cid);
                                // let mut new_arg_names: Vec<String> = Vec::new();
                                // todo!();
                                // for an in arg_names.iter() {
                                //     new_arg_names.push(an.replace(name, &new_n));
                                // }
                                // TODO: maybe wrong
                                new_t = Op::Call(
                                    new_n,
                                    arg_sorts.clone(),
                                    ret_sorts.clone(),
                                );
                            }
                        }
                        new_t
                    }
                    _ => top.op().clone(),
                };
                let new_t = term(new_t_op, get_children());
                cache.insert(top.clone(), new_t);
            }
        }
    }
    c.outputs = c
        .outputs
        .iter()
        .map(|o| cache.get(o).unwrap().clone())
        .collect();
}

/// Rewriting the var term to new name
fn rewrite_var(c: &mut Computation, fname: &String, cid: &usize) {
    let mut cache = TermMap::<Term>::default();
    let mut children_added = TermSet::default();
    let mut stack = Vec::new();
    stack.extend(c.outputs.iter().cloned());
    while let Some(top) = stack.pop() {
        if !cache.contains_key(&top) {
            // was it missing?
            if children_added.insert(top.clone()) {
                stack.push(top.clone());
                stack.extend(top.cs().iter().filter(|c| !cache.contains_key(c)).cloned());
            } else {
                let get_children = || -> Vec<Term> {
                    top.cs()
                        .iter()
                        .map(|c| cache.get(c).unwrap())
                        .cloned()
                        .collect()
                };
                let new_t_op: Op = match &top.op() {
                    Op::Var(name, sort) => {
                        let new_call_n = format_dup_call(fname, cid);
                        let new_var_n = name.replace(fname, &new_call_n);
                        Op::Var(new_var_n.clone(), sort.clone())
                    }
                    _ => top.op().clone(),
                };
                let new_t = term(new_t_op, get_children());
                cache.insert(top.clone(), new_t);
            }
        }
    }
    c.outputs = c
        .outputs
        .iter()
        .map(|o| cache.get(o).unwrap().clone())
        .collect();
}

fn traverse(comps: &Computations, fname: &String, dugs: &mut HashMap<String, DefUsesGraph>) {
    if !dugs.contains_key(fname) {
        let c = comps.get(fname).clone();
        for t in c.terms_postorder() {
            if let Op::Call(callee, ..) = &t.op() {
                traverse(comps, &callee, dugs);
            }
        }
        let mut dug = DefUsesGraph::for_call_site(&c, dugs, fname);
        dug.gen_in_out(&c);
        dugs.insert(fname.clone(), dug);
    }
}

fn remap(
    comps: &Computations,
    rewriting_set: &HashSet<String>,
    duplicate_set: &HashSet<String>,
    call_map: &TermMap<usize>,
    call_cnt: &HashMap<String, usize>,
    func_to_cs: &HashMap<String, HashMap<usize, CallSite>>,
    ml: usize,
) -> (Computations, HashMap<String, DefUsesGraph>) {
    let mut n_comps = Computations::new();
    let mut n_dugs: HashMap<String, DefUsesGraph> = HashMap::new();
    let mut context_map: HashMap<String, CallSite> = HashMap::new();
    let mut css_call_cnt: HashMap<String, usize> = HashMap::new();
    for (fname, comp) in comps.comps.iter() {
        let mut ncomp: Computation = comp.clone();
        let id_to_cs = func_to_cs.get(fname).unwrap();

        if rewriting_set.contains(fname) {
            rewrite_call(&mut ncomp, call_map, duplicate_set);
        }

        if duplicate_set.contains(fname) {
            for (cid, cs) in id_to_cs.iter() {
                let new_n: String = format_dup_call(fname, cid);
                let mut dup_comp: Computation = Computation {
                    outputs: ncomp.outputs().clone(),
                    metadata: ncomp.metadata.clone(),
                    precomputes: ncomp.precomputes.clone(),
                    persistent_arrays: Default::default(),
                };
                rewrite_var(&mut dup_comp, fname, cid);
                n_comps.comps.insert(new_n.clone(), dup_comp);
                context_map.insert(new_n.clone(), cs.clone());
                css_call_cnt.insert(new_n, call_cnt.get(fname).unwrap().clone());
            }
        } else {
            if let Some(cs) = id_to_cs.get(&0) {
                context_map.insert(fname.clone(), cs.clone());
                css_call_cnt.insert(fname.clone(), call_cnt.get(fname).unwrap().clone());
            }
            n_comps.comps.insert(fname.clone(), ncomp);
        }
    }
    let main = "main".to_string();
    traverse(&n_comps, &main, &mut n_dugs);

    for (fname, cs) in context_map.iter() {
        let mut dug = n_dugs.get_mut(fname).unwrap();
        let comp = n_comps.get(fname);
        dug.set_num_calls(css_call_cnt.get(fname).unwrap());
        // TODO: enable this
        // dug.insert_context(&cs.args, &cs.rets, &cs.caller_dug, comp, ml);
    }

    (n_comps, n_dugs)
}

fn format_dup_call(fname: &String, cid: &usize) -> String {
    format!("{}_circ_v_{}", fname, cid).clone()
}

fn to_key(vterms: &Vec<Vec<Term>>) -> Vec<usize> {
    let mut key: Vec<usize> = Vec::new();
    for terms in vterms{
        let mut v: Vec<usize> = Vec::new();
        for t in terms{
            v.push(get_op_id(t.op()));
        }
        v.sort();
        key.extend(v);
    }
    key
}

fn get_op_id(op: &Op) -> usize {
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