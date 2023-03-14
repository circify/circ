//! Operator PersistentRamSplit

use crate::ir::term::ty::*;
use crate::ir::term::*;
use fxhash::FxHashSet as HashSet;

/// Type-check [super::ExtOp::PersistentRamSplit].
pub fn check(arg_sorts: &[&Sort]) -> Result<Sort, TypeErrorReason> {
    if let &[entries, indices] = arg_sorts {
        let (key, value, size) = ty::array_or(entries, "PersistentRamSplit entries")?;
        let f = pf_or(key, "PersistentRamSplit entries: indices must be field")?;
        let value_tup = ty::tuple_or(value, "PersistentRamSplit entries: value must be a tuple")?;
        if let &[old, new] = &value_tup {
            eq_or(
                f,
                old,
                "PersistentRamSplit entries: value must be a field pair",
            )?;
            eq_or(
                f,
                new,
                "PersistentRamSplit entries: value must be a field pair",
            )?;
            let (i_key, i_value, i_size) = ty::array_or(indices, "PersistentRamSplit indices")?;
            eq_or(f, i_key, "PersistentRamSplit indices: key must be a field")?;
            eq_or(
                f,
                i_value,
                "PersistentRamSplit indices: value must be a field",
            )?;
            let n_touched = i_size.min(size);
            let n_ignored = size - n_touched;
            let box_f = Box::new(f.clone());
            let f_pair = Sort::Tuple(Box::new([f.clone(), f.clone()]));
            let ignored_entries_sort =
                Sort::Array(box_f.clone(), Box::new(f_pair.clone()), n_ignored);
            let selected_entries_sort = Sort::Array(box_f, Box::new(f_pair), n_touched);
            Ok(Sort::Tuple(Box::new([
                ignored_entries_sort,
                selected_entries_sort.clone(),
                selected_entries_sort,
            ])))
        } else {
            // non-pair entries value
            Err(TypeErrorReason::Custom(
                "PersistentRamSplit: entries value must be a pair".into(),
            ))
        }
    } else {
        // wrong arg count
        Err(TypeErrorReason::ExpectedArgs(2, arg_sorts.len()))
    }
}

/// Evaluate [super::ExtOp::PersistentRamSplit].
///
/// Takes two arguments:
///
/// * entries: [(val_init_i, val_fin_i)] (len E)
/// * indices: [idx_i] (len I)
///
/// assumes I < E and 0 <= idx_i < E.
///
/// Let dedup_i be idx_i with duplicates removed
/// Let ext_i be dedup_i padded up to length I. The added elements are each i in 0.. (so long as i hasn't occured in ext_i already).
/// Let
///
///
/// Returns:
/// * a bunch of sequences of index-value pairs:
///   * untouched_entries (array field (tuple (field field)) (length I - E))
///   * init_reads (array field (tuple (field field)) (length I))
///   * fin_writes (array field (tuple (field field)) (length I))
pub fn eval(args: &[&Value]) -> Value {
    let entries = &args[0].as_array().values();
    let (init_vals, fin_vals): (Vec<Value>, Vec<Value>) = entries
        .iter()
        .map(|t| (t.as_tuple()[0].clone(), t.as_tuple()[1].clone()))
        .unzip();
    let indices = &args[1].as_array().values();
    let num_accesses = indices.len();
    let field = args[0].as_array().key_sort.as_pf();
    let uniq_indices = {
        let mut uniq_indices = Vec::<usize>::new();
        let mut used_indices = HashSet::<usize>::default();
        for i in indices.iter().map(|i| i.as_usize().unwrap()).chain(0..) {
            if uniq_indices.len() == num_accesses {
                break;
            }
            if !used_indices.contains(&i) {
                uniq_indices.push(i);
                used_indices.insert(i);
            }
        }
        uniq_indices.sort();
        uniq_indices
    };
    let mut init_reads = Vec::new();
    let mut fin_writes = Vec::new();
    let mut untouched_entries = Vec::new();
    let mut j = 0;
    for (i, (init_val, fin_val)) in init_vals.into_iter().zip(fin_vals).enumerate() {
        if j < uniq_indices.len() && uniq_indices[j] == i {
            init_reads.push((i, init_val));
            fin_writes.push((i, fin_val));
            j += 1;
        } else {
            untouched_entries.push((i, init_val));
        }
    }
    let key_sort = Sort::Field(field.clone());
    let entry_to_vals =
        |e: (usize, Value)| Value::Tuple(Box::new([Value::Field(field.new_v(e.0)), e.1]));
    let vec_to_arr = |v: Vec<(usize, Value)>| {
        let vals: Vec<Value> = v.into_iter().map(entry_to_vals).collect();
        Value::Array(Array::from_vec(
            key_sort.clone(),
            vals.first().unwrap().sort(),
            vals,
        ))
    };
    let init_reads = vec_to_arr(init_reads);
    let untouched_entries = vec_to_arr(untouched_entries);
    let fin_writes = vec_to_arr(fin_writes);
    Value::Tuple(vec![untouched_entries, init_reads, fin_writes].into_boxed_slice())
}
