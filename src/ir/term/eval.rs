//! IR Evaluation

use super::{
    check, extras, leaf_term, term, Array, BitVector, BoolNaryOp, BvBinOp, BvBinPred, BvNaryOp,
    BvUnOp, FieldToBv, FxHashMap, IntBinPred, IntNaryOp, Integer, Node, Op, PfNaryOp, PfUnOp, Sort,
    Term, TermMap, Value,
};
use crate::cfg::cfg_or_default;

use circ_fields::{FieldT, FieldV};

use log::trace;

/// Recursively the term `t`, using variable values in `h` and storing intermediate evaluations in
/// the cache `vs`.
pub fn eval_cached<'a>(
    t: &Term,
    h: &FxHashMap<String, Value>,
    vs: &'a mut TermMap<Value>,
) -> &'a Value {
    // the custom traversal (rather than [PostOrderIter]) allows us to break early based on the cache

    // (children pushed, term)
    let mut stack = vec![(false, t.clone())];
    while let Some((children_pushed, node)) = stack.pop() {
        if vs.contains_key(&node) {
            continue;
        }
        if children_pushed {
            eval_value(vs, h, node);
        } else {
            stack.push((true, node.clone()));
            for c in node.cs() {
                // vs doubles as our visited set.
                if !vs.contains_key(c) {
                    stack.push((false, c.clone()));
                }
            }
        }
    }
    vs.get(t).unwrap()
}

/// Recursively evaluate the term `t`, using variable values in `h`.
pub fn eval(t: &Term, h: &FxHashMap<String, Value>) -> Value {
    let mut vs = TermMap::<Value>::default();
    eval_cached(t, h, &mut vs).clone()
}

/// Helper function for eval function. Handles a single term
fn eval_value(vs: &mut TermMap<Value>, h: &FxHashMap<String, Value>, t: Term) -> Value {
    let args: Vec<&Value> = t.cs().iter().map(|c| vs.get(c).unwrap()).collect();
    trace!("Eval {} on {:?}", t.op(), args);
    let v = eval_op(t.op(), &args, h);
    trace!("=> {}", v);
    if let Value::Bool(false) = &v {
        trace!("term {}", t);
        for v in extras::free_variables(t.clone()) {
            trace!("  {} = {}", v, h.get(&v).unwrap());
        }
    }
    vs.insert(t, v.clone());
    v
}

/// Helper function for eval function. Handles a single op
#[allow(clippy::uninlined_format_args)]
pub fn eval_op(op: &Op, args: &[&Value], var_vals: &FxHashMap<String, Value>) -> Value {
    match op {
        Op::Var(n, _) => var_vals
            .get(n)
            .unwrap_or_else(|| panic!("Missing var: {} in {:?}", n, var_vals))
            .clone(),
        Op::Eq => Value::Bool(args[0] == args[1]),
        Op::Not => Value::Bool(!args[0].as_bool()),
        Op::Implies => Value::Bool(!args[0].as_bool() || args[1].as_bool()),
        Op::BoolNaryOp(BoolNaryOp::Or) => Value::Bool(args.iter().any(|a| a.as_bool())),
        Op::BoolNaryOp(BoolNaryOp::And) => Value::Bool(args.iter().all(|a| a.as_bool())),
        Op::BoolNaryOp(BoolNaryOp::Xor) => Value::Bool(
            args.iter()
                .map(|a| a.as_bool())
                .fold(false, std::ops::BitXor::bitxor),
        ),
        Op::BvBit(i) => Value::Bool(args[0].as_bv().uint().get_bit(*i as u32)),
        Op::BoolMaj => {
            let c0 = args[0].as_bool() as u8;
            let c1 = args[1].as_bool() as u8;
            let c2 = args[2].as_bool() as u8;
            Value::Bool(c0 + c1 + c2 > 1)
        }
        Op::BvConcat => Value::BitVector({
            let mut it = args.iter().map(|a| a.as_bv().clone());
            let f = it.next().unwrap();
            it.fold(f, BitVector::concat)
        }),
        Op::BvExtract(h, l) => Value::BitVector(args[0].as_bv().clone().extract(*h, *l)),
        Op::Const(v) => v.clone(),
        Op::BvBinOp(o) => Value::BitVector({
            let a = args[0].as_bv().clone();
            let b = args[1].as_bv().clone();
            match o {
                BvBinOp::Udiv => a / &b,
                BvBinOp::Urem => a % &b,
                BvBinOp::Sub => a - b,
                BvBinOp::Ashr => a.ashr(&b),
                BvBinOp::Lshr => a.lshr(&b),
                BvBinOp::Shl => a << &b,
            }
        }),
        Op::BvUnOp(o) => Value::BitVector({
            let a = args[0].as_bv().clone();
            match o {
                BvUnOp::Not => !a,
                BvUnOp::Neg => -a,
            }
        }),
        Op::BvNaryOp(o) => Value::BitVector({
            let mut xs = args.iter().map(|a| a.as_bv().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    BvNaryOp::Add => std::ops::Add::add,
                    BvNaryOp::Mul => std::ops::Mul::mul,
                    BvNaryOp::Xor => std::ops::BitXor::bitxor,
                    BvNaryOp::Or => std::ops::BitOr::bitor,
                    BvNaryOp::And => std::ops::BitAnd::bitand,
                },
            )
        }),
        Op::BvSext(w) => Value::BitVector({
            let a = args[0].as_bv().clone();
            let mask = ((Integer::from(1) << *w as u32) - 1)
                * Integer::from(a.uint().get_bit(a.width() as u32 - 1));
            BitVector::new(a.uint() | (mask << a.width() as u32), a.width() + w)
        }),
        Op::PfToBv(w) => Value::BitVector({
            let i = args[0].as_pf().i();
            if let FieldToBv::Panic = cfg_or_default().ir.field_to_bv {
                assert!(
                    (i.significant_bits() as usize) <= *w,
                    "{}",
                    "oversized input to Op::PfToBv({w})",
                );
            }
            BitVector::new(i % (Integer::from(1) << *w), *w)
        }),
        Op::BvUext(w) => Value::BitVector({
            let a = args[0].as_bv().clone();
            BitVector::new(a.uint().clone(), a.width() + w)
        }),
        Op::Ite => args[if args[0].as_bool() { 1 } else { 2 }].clone(),
        Op::BvBinPred(o) => Value::Bool({
            let a = args[0].as_bv();
            let b = args[1].as_bv();
            match o {
                BvBinPred::Sge => a.as_sint() >= b.as_sint(),
                BvBinPred::Sgt => a.as_sint() > b.as_sint(),
                BvBinPred::Sle => a.as_sint() <= b.as_sint(),
                BvBinPred::Slt => a.as_sint() < b.as_sint(),
                BvBinPred::Uge => a.uint() >= b.uint(),
                BvBinPred::Ugt => a.uint() > b.uint(),
                BvBinPred::Ule => a.uint() <= b.uint(),
                BvBinPred::Ult => a.uint() < b.uint(),
            }
        }),
        Op::BoolToBv => Value::BitVector(BitVector::new(Integer::from(args[0].as_bool()), 1)),
        Op::PfUnOp(o) => Value::Field({
            let a = args[0].as_pf().clone();
            match o {
                PfUnOp::Recip => {
                    if a.is_zero() {
                        a.ty().zero()
                    } else {
                        a.recip()
                    }
                }
                PfUnOp::Neg => -a,
            }
        }),
        Op::PfDiv => Value::Field({
            let a = args[0].as_pf().clone();
            let b = args[1].as_pf().clone();
            a * b.recip()
        }),
        Op::PfNaryOp(o) => Value::Field({
            let mut xs = args.iter().map(|a| a.as_pf().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    PfNaryOp::Add => std::ops::Add::add,
                    PfNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::IntBinPred(o) => Value::Bool({
            let a = args[0].as_int();
            let b = args[1].as_int();
            match o {
                IntBinPred::Ge => a >= b,
                IntBinPred::Gt => a > b,
                IntBinPred::Le => a <= b,
                IntBinPred::Lt => a < b,
            }
        }),
        Op::IntNaryOp(o) => Value::Int({
            let mut xs = args.iter().map(|a| a.as_int().clone());
            let f = xs.next().unwrap();
            xs.fold(
                f,
                match o {
                    IntNaryOp::Add => std::ops::Add::add,
                    IntNaryOp::Mul => std::ops::Mul::mul,
                },
            )
        }),
        Op::UbvToPf(fty) => Value::Field(fty.new_v(args[0].as_bv().uint())),
        Op::PfChallenge(name, field) => Value::Field(pf_challenge(name, field)),
        Op::Witness(_) => args[0].clone(),
        Op::PfFitsInBits(n_bits) => {
            Value::Bool(args[0].as_pf().i().signed_bits() <= *n_bits as u32)
        }
        // tuple
        Op::Tuple => Value::Tuple(args.iter().map(|a| (*a).clone()).collect()),
        Op::Field(i) => {
            let t = args[0].as_tuple();
            assert!(i < &t.len(), "{} out of bounds for {} on {:?}", i, op, args);
            t[*i].clone()
        }
        Op::Update(i) => {
            let mut t = Vec::from(args[0].as_tuple()).into_boxed_slice();
            assert!(i < &t.len(), "{} out of bounds for {} on {:?}", i, op, args);
            let e = args[1].clone();
            assert_eq!(t[*i].sort(), e.sort());
            t[*i] = e;
            Value::Tuple(t)
        }
        // array
        Op::Store => {
            let a = args[0].as_array().clone();
            let i = args[1].clone();
            let v = args[2].clone();
            Value::Array(a.store(i, v))
        }
        Op::CStore => {
            let a = args[0].as_array().clone();
            let i = args[1].clone();
            let v = args[2].clone();
            let c = args[3].as_bool();
            if c {
                Value::Array(a.store(i, v))
            } else {
                Value::Array(a)
            }
        }
        Op::Fill(key_sort, size) => {
            let v = args[0].clone();
            Value::Array(Array::new(
                key_sort.clone(),
                Box::new(v),
                Default::default(),
                *size,
            ))
        }
        Op::Array(key, value) => Value::Array(Array::from_vec(
            key.clone(),
            value.clone(),
            args.iter().cloned().cloned().collect(),
        )),
        Op::Select => {
            let a = args[0].as_array();
            let i = args[1];
            a.select(i)
        }
        Op::Map(inner_op) => {
            //  term_vecs[i] will store a vector of all the i-th index entries of the array arguments
            let mut arg_vecs: Vec<Vec<Value>> = vec![Vec::new(); args[0].as_array().size];

            for arg in args {
                let arr = arg.as_array().clone();
                let iter = match arg.sort() {
                    Sort::Array(k, _, s) => (*k).clone().elems_iter_values().take(s).enumerate(),
                    _ => panic!("Input type should be Array"),
                };
                for (j, jval) in iter {
                    arg_vecs[j].push(arr.select(&jval))
                }
            }
            let term = term(
                op.clone(),
                args.iter()
                    .map(|a| leaf_term(Op::Const((*a).clone())))
                    .collect(),
            );
            let (mut res, iter) = match check(&term) {
                Sort::Array(k, v, n) => (
                    Array::default((*k).clone(), &v, n),
                    (*k).clone().elems_iter_values().take(n).enumerate(),
                ),
                _ => panic!("Output type of map should be array"),
            };

            for (i, idxval) in iter {
                let args: Vec<&Value> = arg_vecs[i].iter().collect();
                let val = eval_op(inner_op, &args, var_vals);
                res.map.insert(idxval, val);
            }
            Value::Array(res)
        }
        Op::Rot(i) => {
            let a = args[0].as_array().clone();
            let (mut res, iter, len) = match args[0].sort() {
                Sort::Array(k, v, n) => (
                    Array::default((*k).clone(), &v, n),
                    (*k).clone().elems_iter_values().take(n).enumerate(),
                    n,
                ),
                _ => panic!("Input type should be Array"),
            };

            // calculate new rotation amount
            let rot = *i % len;
            for (idx, idx_val) in iter {
                let w = idx_val.as_bv().width();
                let new_idx = Value::BitVector(BitVector::new(Integer::from((idx + rot) % len), w));
                let new_val = a.select(&idx_val);
                res.map.insert(new_idx, new_val);
            }
            Value::Array(res)
        }
        Op::PfToBoolTrusted => {
            let v = args[0].as_pf().i();
            assert!(v == 0 || v == 1);
            Value::Bool(v == 1)
        }
        Op::ExtOp(o) => o.eval(args),

        o => unimplemented!("eval: {:?}", o),
    }
}

/// Compute a (deterministic) prime-field challenge.
pub fn pf_challenge(name: &str, field: &FieldT) -> FieldV {
    use rand::SeedableRng;
    use rand_chacha::ChaChaRng;
    use std::hash::{Hash, Hasher};
    // hash the string
    let mut hasher = fxhash::FxHasher::default();
    name.hash(&mut hasher);
    let hash: u64 = hasher.finish();
    // seed ChaCha with the hash
    let mut seed = [0u8; 32];
    seed[0..8].copy_from_slice(&hash.to_le_bytes());
    let mut rng = ChaChaRng::from_seed(seed);
    // sample from ChaCha
    field.random_v(&mut rng)
}
