//! Rewrite ITE terms

use crate::ir::opt::visit::RewritePass;
use crate::ir::term::*;

/// ITE cache.
#[derive(Default)]
struct IteRewriter;

impl RewritePass for IteRewriter {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _computation: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        let cs = rewritten_children();
        match &orig.op {
            Op::Ite => {
                let sel = cs[0].clone();
                let t = cs[1].clone();
                let f = cs[2].clone();
                match f.op {
                    Op::Ite => {
                        let child_sel = f.cs[0].clone();
                        let child_t = f.cs[1].clone();
                        if sel == term![Op::Not; child_sel.clone()] {
                            Some(term![Op::Ite; child_sel, child_t, t])
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

/// Binarize (expand) n-ary terms.
pub fn rewrite_ites(c: &mut Computation) {
    let mut pass = IteRewriter;
    pass.traverse(c);
}
