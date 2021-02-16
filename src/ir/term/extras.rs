use super::*;

/// Convert `t` to width `w`, though unsigned extension or extraction
pub fn to_width(t: &Term, w: usize) -> Term {
    let old_w = check(t).as_bv();
    if old_w < w {
        term(Op::BvUext(w - old_w), vec![t.clone()])
    } else if old_w == w {
        t.clone()
    } else {
        term(Op::BvExtract(w - 1, 0), vec![t.clone()])
    }
}
