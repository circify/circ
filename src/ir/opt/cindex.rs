//! Rewrite const indexed store and select terms

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// ITE cache.
#[derive(Default)]
struct ConstIndexer;

impl RewritePass for ConstIndexer {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        let cs = rewritten_children();
        match &orig.op {
            Op::Store => {
                let array = cs[0].as_array_opt();
                let index = cs[1].clone();
                let value = cs[2].clone();
                match array {
                    Some(a) => {
                        if index.is_const() && value.is_const()  {
                            let i = index.as_value_opt().unwrap();
                            let v = value.as_value_opt().unwrap();
                            Some(leaf_term(Op::Const(Value::Array(a.clone().store(i.clone(), v.clone())))))
                        } else if index.is_const() {
                            if let Value::BitVector(b) = index.as_value_opt().unwrap() {
                                let mut array_terms = a.to_terms();
                                array_terms[b.as_sint().to_usize().unwrap()] = value;
                                Some(term(Op::Array, array_terms))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    },
                    None => {
                        // store on array term?
                        match &cs[0].op {
                            Op::Array => {
                                if index.is_const() {
                                    if let Value::BitVector(b) = index.as_value_opt().unwrap() {
                                        let mut array_terms = cs[0].cs.clone();
                                        array_terms[b.as_sint().to_usize().unwrap()] = value;
                                        Some(term(Op::Array, array_terms))
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }
                            _ => None
                        }
                    }
                }
            }
            _ => None,
        }
    }
}

/// Binarize (expand) n-ary terms.
pub fn cindex(c: &mut Computation) {
    let mut pass = ConstIndexer;
    pass.traverse(c);
}
