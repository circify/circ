//! Represent a persistent array as (committed) scalar values and a RAM.

use super::super::super::visit::RewritePass;
use super::*;
use crate::front::PROVER_VIS;
use log::debug;

/// Extract any persistent arrays from a computation, eand emit checks.
pub fn apply(c: &mut Computation, cfg: &AccessCfg) {
    let mut cfg = cfg.clone();
    cfg.create = true;
    let rams = persistent_to_ram(c, &cfg);
    check_rams(c, rams, &cfg);
}

/// Extract any persistent arrays from a computation, returning RAMs
pub fn persistent_to_ram(c: &mut Computation, cfg: &AccessCfg) -> Vec<Ram> {
    // a list of RAMs
    let mut rams = Vec::new();
    // a list of RAMs
    let mut term_rams = TermMap::default();

    // first, create the commitments
    for (i, (name, final_term)) in c.persistent_arrays.clone().into_iter().enumerate() {
        let sort = check(&final_term);
        let key_sort = sort.as_array().0.clone();
        let value_sort = sort.as_array().1.clone();
        let size = sort.as_array().2;
        let init_term = leaf_term(Op::Var(name.clone(), sort));

        // create a new var for each initial value
        let names: Vec<String> = (0..size).map(|i| format!("{name}.init.{i}")).collect();
        let terms: Vec<Term> = names
            .iter()
            .zip(key_sort.elems_iter())
            .map(|(name, idx)| {
                let val_term = term![Op::Select; init_term.clone(), idx];
                c.new_var(name, value_sort.clone(), PROVER_VIS, Some(val_term))
            })
            .collect();
        // and commit to them
        c.metadata.add_commitment(names);

        // create a new var for each final value
        let final_names: Vec<String> = (0..size).map(|i| format!("{name}.final.{i}")).collect();
        let final_terms: Vec<Term> = final_names
            .iter()
            .zip(key_sort.elems_iter())
            .map(|(name, idx)| {
                let val_term = term![Op::Select; final_term.clone(), idx];
                c.new_var(name, value_sort.clone(), PROVER_VIS, Some(val_term))
            })
            .collect();
        // and commit to them
        c.metadata.add_commitment(final_names);

        let boundary_conditions = BoundaryConditions::Persistent(terms, final_terms);
        let ram = Ram::new(
            i,
            size,
            cfg.clone(),
            Sort::Field(cfg.field.clone()),
            boundary_conditions,
        );

        term_rams.insert(init_term, i);
        rams.push(ram);

        c.metadata.remove_var(&name);
    }

    let mut rewritter = Rewriter { rams, term_rams };
    rewritter.traverse(c);
    // remove them
    c.persistent_arrays.clear();
    rewritter.rams
}

/// Check a persistent RAM using challenges.
pub fn check_rams(c: &mut Computation, rams: Vec<Ram>, cfg: &AccessCfg) {
    let n = rams.len();
    for (j, ram) in rams.into_iter().enumerate() {
        debug!(
            "Ram {}/{}: size {}, {} accesses",
            j + 1,
            n,
            ram.size,
            ram.accesses.len()
        );
        check_ram(c, ram, cfg);
    }
}

/// Check a persistent RAM using challenges.
pub fn check_ram(c: &mut Computation, mut ram: Ram, cfg: &AccessCfg) {
    let j = ram.id;
    let field = &cfg.field;
    let (inital_terms, final_terms) =
        if let BoundaryConditions::Persistent(i, f) = &ram.boundary_conditions {
            (i.clone(), f.clone())
        } else {
            panic!()
        };

    let field_s = Sort::Field(field.clone());
    let mut new_f_var =
        |name: &str, val: Term| c.new_var(name, field_s.clone(), PROVER_VIS, Some(val));
    let field_tuple_s = Sort::Tuple(Box::new([field_s.clone(), field_s.clone()]));
    let mut uhf_inputs = inital_terms.clone();
    uhf_inputs.extend(final_terms.iter().cloned());
    let uhf_key = term(
        Op::PfChallenge(format!("__uhf_key.{j}"), field.clone()),
        uhf_inputs,
    );
    let uhf = |idx: Term, val: Term| term![PF_ADD; val, term![PF_MUL; uhf_key.clone(), idx]];
    let init_and_fin_values = make_array(
        field_s.clone(),
        field_tuple_s,
        inital_terms
            .iter()
            .zip(&final_terms)
            .map(|(i, f)| term![Op::Tuple; i.clone(), f.clone()])
            .collect(),
    );
    let used_indices = make_array(
        field_s.clone(),
        field_s.clone(),
        ram.accesses.iter().map(|a| a.idx.clone()).collect(),
    );
    let split = term![Op::ExtOp(ExtOp::PersistentRamSplit); init_and_fin_values, used_indices];
    let unused_hashes: Vec<Term> = unmake_array(term![Op::Field(0); split.clone()])
        .into_iter()
        .enumerate()
        .map(|(i, entry)| {
            let idx_term = term![Op::Field(0); entry.clone()];
            let val_term = term![Op::Field(1); entry];
            new_f_var(&format!("__unused_hash.{j}.{i}"), uhf(idx_term, val_term))
        })
        .collect();
    let mut declare_access_vars = |array: Term, name: &str| -> Vec<(Term, Term)> {
        unmake_array(array)
            .into_iter()
            .enumerate()
            .map(|(i, access)| {
                let idx_term = term![Op::Field(0); access.clone()];
                let val_term = term![Op::Field(1); access];
                (
                    new_f_var(&format!("__{name}.{j}.{i}.idx"), idx_term),
                    new_f_var(&format!("__{name}.{j}.{i}.val"), val_term),
                )
            })
            .collect()
    };
    let init_reads = declare_access_vars(term![Op::Field(1); split.clone()], "init_read");
    let fin_writes = declare_access_vars(term![Op::Field(2); split], "fin_writes");
    let init_read_hashes: Vec<Term> = init_reads
        .iter()
        .map(|(idx, val)| uhf(idx.clone(), val.clone()))
        .collect();
    let fin_write_hashes: Vec<Term> = fin_writes
        .iter()
        .map(|(idx, val)| uhf(idx.clone(), val.clone()))
        .collect();
    let init_hashes: Vec<Term> = inital_terms
        .into_iter()
        .zip(field_s.elems_iter())
        .map(|(val, idx)| uhf(idx, val))
        .collect();
    let fin_hashes: Vec<Term> = final_terms
        .into_iter()
        .zip(field_s.elems_iter())
        .map(|(val, idx)| uhf(idx, val))
        .collect();
    // to be shown:
    // claim: multiset(init_hashes) = multiset(init_read_hashes || unused_hashes)
    // claim: multiset(fin_hashes) = multiset(fin_write_hashes || unused_hashes)
    let mut ms_hash_inputs = Vec::new();
    ms_hash_inputs.extend(init_hashes.iter().cloned());
    ms_hash_inputs.extend(fin_hashes.iter().cloned());
    ms_hash_inputs.extend(init_read_hashes.iter().cloned());
    ms_hash_inputs.extend(fin_write_hashes.iter().cloned());
    ms_hash_inputs.extend(unused_hashes.iter().cloned());
    let msh = super::hash::MsHasher::new(format!("__pers{j}_ms_hash_key"), field, ms_hash_inputs);
    // share ms_hash(unused_hashes)
    let ms_hash_unused = msh.hash(unused_hashes);
    let init_perm = term![EQ; msh.hash(init_hashes), term![PF_MUL; msh.hash(init_read_hashes), ms_hash_unused.clone()]];
    let fin_perm =
        term![EQ; msh.hash(fin_hashes), term![PF_MUL; msh.hash(fin_write_hashes), ms_hash_unused]];
    c.outputs[0] = term![AND; c.outputs[0].clone(), init_perm, fin_perm];
    for (idx, val) in init_reads {
        ram.new_init(idx, val);
    }
    for (idx, val) in fin_writes {
        ram.new_final_read(idx, val);
    }
    ram.boundary_conditions = BoundaryConditions::OnlyInit;
    super::checker::check_ram(c, ram)
}

struct Rewriter {
    rams: Vec<Ram>,
    term_rams: TermMap<usize>,
}

impl RewritePass for Rewriter {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        match orig.op() {
            Op::Store => {
                if let Some(ram_idx) = self.term_rams.get(&orig.cs()[0]) {
                    let ram = &mut self.rams[*ram_idx];
                    let mut children = rewritten_children();
                    let val = children.pop().unwrap();
                    let idx = children.pop().unwrap();
                    ram.new_write(idx, val, bool_lit(true));
                    self.term_rams.insert(orig.clone(), *ram_idx);
                    // dummy
                    Some(bool_lit(false))
                } else {
                    None
                }
            }
            Op::Select => {
                if let Some(ram_idx) = self.term_rams.get(&orig.cs()[0]) {
                    let ram = &mut self.rams[*ram_idx];
                    let mut children = rewritten_children();
                    let idx = children.pop().unwrap();
                    Some(ram.new_read(idx, computation, orig.clone()))
                } else {
                    None
                }
            }
            Op::CStore => {
                if let Some(ram_idx) = self.term_rams.get(&orig.cs()[0]) {
                    let ram = &mut self.rams[*ram_idx];
                    let mut children = rewritten_children();
                    let cond = children.pop().unwrap();
                    let val = children.pop().unwrap();
                    let idx = children.pop().unwrap();
                    ram.new_write(idx, val, cond);
                    self.term_rams.insert(orig.clone(), *ram_idx);
                    // dummy
                    Some(bool_lit(false))
                } else {
                    None
                }
            }
            Op::Ite => {
                assert!(!self.term_rams.contains_key(&orig.cs()[0]));
                None
            }
            Op::Eq => {
                assert!(!self.term_rams.contains_key(&orig.cs()[0]));
                assert!(!self.term_rams.contains_key(&orig.cs()[1]));
                None
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn length_4() {
        env_logger::try_init().ok();
        let mut cs = text::parse_computation(
            b"
            (computation
                (metadata
                    (parties P)
                    (inputs
                        (A (array (mod 11) (mod 11) 4) (committed))
                        (x (mod 11) (party 0))
                        (return (mod 11))
                    )
                    ; (commitments (commitment A))
                    (commitments)
                )
                (precompute () () (#t ))
                (persistent_arrays (A 4 (store A x #f0m11)))
                (= return (select A x))
            )
        ",
        );
        let values = text::parse_value_map(
            b"
            (set_default_modulus 11
            (let (
                (A (#l (mod 11) (#f1 #f2 #f3 #f4)))
                (x #f0)
                (return #f1)
            ) false ; ignored
            ))
        ",
        );
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
        let field = FieldT::from(rug::Integer::from(11));
        let cfg = AccessCfg::default_from_field(field);
        apply(&mut cs, &cfg);
        println!("{}", text::serialize_computation(&cs));
        assert_eq!(vec![Value::Bool(true)], cs.eval_all(&values));
    }
}
