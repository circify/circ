//! Call Site Similarity

use crate::ir::term::*;
use crate::target::aby::assignment::def_uses::*;

use fxhash::{FxHashMap, FxHashSet};

use std::collections::HashMap;
use std::collections::HashSet;

/// What do we need for call site?
///
/// Call sites:
/// HashMap<(String, Vec<usize>, Vec<usize>), Vec<Term>>  
/// - Each entry of {call_sites} will become a copy of function
///
/// Computations:
/// HashMap<String, HashMap<usize, Computation>>
/// - String: fname
/// - usize: version id
///
/// DefUseGraph:
/// HashMap<String, DefUseGraph>
///
/// Surrounding info:
/// Two type:
/// 1. For inner calls:
///     - Per call
/// 2. For outer calls:
///     - Per call site
///
/// args: HashMap<String, Vec<Term>>
/// rets: HashMap<String, Vec<Term>>

#[derive(Clone)]
/// A structure that stores the context and all the call terms in one call site
struct CallSite {
    // Context's fname
    pub caller: String,
    pub callee: String,
    pub arg_names: Vec<String>,
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
        arg_names: &Vec<String>,
        rets: &Vec<Vec<Term>>,
        t: &Term,
        caller_dug: &DefUsesGraph,
    ) -> Self {
        Self {
            caller: caller.clone(),
            callee: callee.clone(),
            arg_names: arg_names.clone(),
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

/// Determine if call sites are similar based on input and output arguments to the call site
pub fn call_site_similarity(fs: &Functions) -> (Functions, HashMap<String, DefUsesGraph>) {
    let mut call_sites: HashMap<(String, Vec<usize>, Vec<usize>), CallSite> = HashMap::new();
    let mut func_to_cs: HashMap<String, HashMap<usize, CallSite>> = HashMap::new();

    let mut dup_per_func: HashMap<String, usize> = HashMap::new();

    // Mapping of callee-caller pair
    let mut callee_caller: HashSet<(String, String)> = HashSet::new();
    // Functions that have more than one call site
    let mut duplicated_f: HashSet<String> = HashSet::new();
    // Functions that need to be rewrote for calling to duplicated f
    // If a callee is duplicated, the caller need to be rewrote
    let mut rewriting_f: HashSet<String> = HashSet::new();

    // Iterate all the comp and retrieve call site info
    for (caller, comp) in fs.computations.iter() {
        let mut dug = DefUsesGraph::for_call_site(comp);
        let cs: Vec<(
            String,
            Vec<usize>,
            Vec<Vec<Term>>,
            Vec<usize>,
            Vec<Vec<Term>>,
            Term,
        )> = dug.get_call_site();
        // dugs.insert(caller.clone(), dug.clone());
        for (callee, args, args_t, rets, rets_t, t) in cs.iter() {
            let key: (String, Vec<usize>, Vec<usize>) =
                (callee.clone(), args.clone(), rets.clone());
            if call_sites.contains_key(&key) {
                call_sites.get_mut(&key).unwrap().insert(t);
            } else {
                // Use the first context
                if let Op::Call(_, arg_names, _, _) = &t.op {
                    let cs = CallSite::new(caller, callee, args_t, arg_names, rets_t, t, &dug);
                    call_sites.insert(key, cs);
                }
            }
            // recording callee-caller
            callee_caller.insert((callee.clone(), caller.clone()));
        }
        dup_per_func.insert(caller.clone(), 0);
        func_to_cs.insert(caller.clone(), HashMap::new());
        // // HACK: for main func:
        // if caller == "main"{
        //     new_dugs.get_mut(caller).unwrap().insert(0, dug.clone());
        // }
    }

    let mut call_map: TermMap<usize> = TermMap::new();

    // Generating duplicate set
    for (key, cs) in call_sites.iter() {
        let call_id: usize = dup_per_func.get(&key.0).unwrap().clone();

        if call_id > 0 {
            // indicate this function need to be rewrote
            duplicated_f.insert(key.0.clone());
        }

        for t in cs.calls.iter() {
            call_map.insert(t.clone(), call_id);
        }
        dup_per_func.insert(key.0.clone(), call_id + 1);
        let id_to_cs = func_to_cs.get_mut(&key.0).unwrap();
        id_to_cs.insert(call_id, cs.clone());
    }

    // Generating rewriting set
    for (callee, caller) in callee_caller.iter() {
        if duplicated_f.contains(callee) {
            rewriting_f.insert(caller.clone());
        }
    }

    remap(fs, &rewriting_f, &duplicated_f, &call_map, &func_to_cs)
}

/// Rewriting the call term to new call
fn rewrite_call(c: &mut Computation, call_map: &TermMap<usize>, duplicate_set: &HashSet<String>) {
    let mut cache = TermMap::<Term>::new();
    let mut children_added = TermSet::new();
    let mut stack = Vec::new();
    stack.extend(c.outputs.iter().cloned());
    while let Some(top) = stack.pop() {
        if !cache.contains_key(&top) {
            // was it missing?
            if children_added.insert(top.clone()) {
                stack.push(top.clone());
                stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
            } else {
                let get_children = || -> Vec<Term> {
                    top.cs
                        .iter()
                        .map(|c| cache.get(c).unwrap())
                        .cloned()
                        .collect()
                };
                let new_t_op: Op = match &top.op {
                    Op::Call(name, arg_names, arg_sorts, ret_sorts) => {
                        let mut new_t = top.op.clone();
                        if duplicate_set.contains(name) {
                            if let Some(cid) = call_map.get(&top) {
                                let new_n = format_dup_call(name, cid);
                                let mut new_arg_names: Vec<String> = Vec::new();
                                for an in arg_names.iter() {
                                    new_arg_names.push(an.replace(name, &new_n));
                                }
                                new_t = Op::Call(
                                    new_n,
                                    new_arg_names,
                                    arg_sorts.clone(),
                                    ret_sorts.clone(),
                                );
                            }
                        }
                        new_t
                    }
                    _ => top.op.clone(),
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
    let mut cache = TermMap::<Term>::new();
    let mut children_added = TermSet::new();
    let mut stack = Vec::new();
    stack.extend(c.outputs.iter().cloned());
    while let Some(top) = stack.pop() {
        if !cache.contains_key(&top) {
            // was it missing?
            if children_added.insert(top.clone()) {
                stack.push(top.clone());
                stack.extend(top.cs.iter().filter(|c| !cache.contains_key(c)).cloned());
            } else {
                let get_children = || -> Vec<Term> {
                    top.cs
                        .iter()
                        .map(|c| cache.get(c).unwrap())
                        .cloned()
                        .collect()
                };
                let new_t_op: Op = match &top.op {
                    Op::Var(name, sort) => {
                        let new_call_n = format_dup_call(fname, cid);
                        let new_var_n = name.replace(fname, &new_call_n);
                        Op::Var(new_var_n.clone(), sort.clone())
                    }
                    _ => top.op.clone(),
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

fn remap(
    fs: &Functions,
    rewriting_set: &HashSet<String>,
    duplicate_set: &HashSet<String>,
    call_map: &TermMap<usize>,
    func_to_cs: &HashMap<String, HashMap<usize, CallSite>>,
) -> (Functions, HashMap<String, DefUsesGraph>) {
    let mut n_fs = Functions::new();
    let mut n_dugs: HashMap<String, DefUsesGraph> = HashMap::new();
    for (fname, comp) in fs.computations.iter() {
        let mut ncomp: Computation = comp.clone();
        let id_to_cs = func_to_cs.get(fname).unwrap();

        if rewriting_set.contains(fname) {
            rewrite_call(&mut ncomp, call_map, duplicate_set);
        }

        if duplicate_set.contains(fname) {
            for (cid, cs) in id_to_cs.iter() {
                let new_n: String = format_dup_call(fname, cid);
                let mut dup_comp: Computation = Computation{
                    outputs: ncomp.outputs().clone(),
                    metadata: rewrite_metadata(&ncomp.metadata, fname, &new_n),
                    precomputes: ncomp.precomputes.clone(),
                };
                rewrite_var(&mut dup_comp, fname, cid);
                let mut dug = DefUsesGraph::new(&dup_comp);
                dug.insert_context(
                    &cs.arg_names,
                    &cs.args,
                    &cs.rets,
                    &cs.caller_dug,
                    &dup_comp,
                    4,
                );
                n_fs.insert(new_n.clone(), dup_comp);
                n_dugs.insert(new_n.clone(), dug);
            }
        } else {
            let mut dug = DefUsesGraph::new(&ncomp);
            // println!("fname {}", fname);
            // Main function might not have any call site info
            if let Some(cs) = id_to_cs.get(&0) {
                dug.insert_context(&cs.arg_names, &cs.args, &cs.rets, &cs.caller_dug, &ncomp, 4);
            }
            n_fs.insert(fname.clone(), ncomp);
            n_dugs.insert(fname.clone(), dug.clone());
        }
    }

    (n_fs, n_dugs)
}

fn format_dup_call(fname: &String, cid: &usize) -> String {
    format!("{}_circ_v_{}", fname, cid).clone()
}

fn rewrite_metadata(md: &ComputationMetadata, fname: &String, n_fname: &String) -> ComputationMetadata {

    let mut input_vis: FxHashMap<String, (Term, Option<PartyId>)> = FxHashMap::default();
    let mut computation_inputs: FxHashSet<String> = FxHashSet::default();
    let mut computation_arg_names: Vec<String> = Vec::new();

    for (s, tu) in md.input_vis.iter(){
        let s = s.clone();
        let new_s = s.replace(fname, n_fname);
        input_vis.insert(new_s, tu.clone());
    }

    for s in md.computation_inputs.iter(){
        let s = s.clone();
        let new_s = s.replace(fname, n_fname);
        computation_inputs.insert(new_s);
    }

    for s in md.computation_arg_names.iter(){
        let s = s.clone();
        let new_s = s.replace(fname, n_fname);
        computation_arg_names.push(new_s);
    }

    ComputationMetadata {
        party_ids: md.party_ids.clone(),
        next_party_id: md.next_party_id.clone(),
        input_vis,
        computation_inputs,
        computation_arg_names,
    }
}
