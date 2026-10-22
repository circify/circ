//! Matrix-multiply transforms.
//!
//! Two passes over the constraints:
//!
//! * [mat_ip] is the randomized transform. Each matrix product the *verifier*
//!   would evaluate becomes a prover-supplied product `C`, plus the Freivalds
//!   check `C v = A (B v)` at a uniform random vector `v`. That takes the
//!   verifier from `O(n^3)` multiplications to `O(n^2)`, with soundness error
//!   `1/|F|` per product.
//! * [mat_lower] expands whatever matrix operators are left in the constraints
//!   into field arithmetic. It always runs; it is what makes an untransformed
//!   product cost the verifier its `O(n^3)`.
//!
//! Both work on the constraints only, so a product the *prover* computes is
//! left alone: after [crate::ir::opt::chall::deskolemize_witnesses], prover
//! computations live in precomputes, where [crate::ir::term::ext::mat]
//! evaluates them natively and the verifier pays nothing. This is the same
//! restriction the paper's compiler states as "witnesses are sinks".
//!
//! ## Rounds and coins
//!
//! A product's coins take that product's entries as their IR children. Those
//! children decide which round a challenge lands in ([crate::ir::opt::chall]
//! puts it after everything it depends on) and, just as importantly, they force
//! the product into an earlier round than the coins that check it: a variable no
//! challenge depends on is pushed to the *latest* legal round, which for a
//! product would mean the prover choosing it after seeing `v`. The coin's value
//! itself comes from Mirage's Fiat-Shamir over the commitment to the whole
//! preceding round, so every product is in fact bound by every later coin.
//!
//! Each product's vector is named by role -- coin `j` of a width-`c` vector --
//! so that products of the same width name their coins alike. That is this
//! transform declaring the checks independent;
//! [crate::ir::opt::chall::share_challenges] decides whether to act on it. When
//! it merges them the coin's dependents become the union, so sharing *widens*
//! what each coin binds rather than weakening it, and the round structure is
//! unchanged. Sharing is not proven sound in the paper, so it is off by default.

use super::visit::RewritePass;
use crate::front::PROVER_VIS;
use crate::ir::term::ext::mat::shape_or;
use crate::ir::term::ext::ExtOp;
use crate::ir::term::*;
use crate::util::ns::Namespace;

use log::debug;

/// The matrix product operator.
const MATMUL: Op = Op::ExtOp(ExtOp::MatMul);
/// The matrix sum operator.
const MATADD: Op = Op::ExtOp(ExtOp::MatAdd);

/// `(rows, cols, index sort, entry field)` of a matrix term.
fn shape(t: &Term) -> (usize, usize, Sort, Sort) {
    let s = check(t);
    let (r, c, key, f) = shape_or(&s, "matrix operator").expect("type-checked matrix");
    (r, c, key.clone(), f.clone())
}

/// `m[i][j]`, where `idx` holds the index literals.
fn entry(m: &Term, idx: &[Term], i: usize, j: usize) -> Term {
    term![Op::Select; term![Op::Select; m.clone(), idx[i].clone()], idx[j].clone()]
}

/// The entries of a matrix term, by row.
fn entries(m: &Term, idx: &[Term], rows: usize, cols: usize) -> Vec<Vec<Term>> {
    (0..rows)
        .map(|i| (0..cols).map(|j| entry(m, idx, i, j)).collect())
        .collect()
}

/// The matrix whose entries are `rows`.
fn matrix(rows: &[Vec<Term>], key: &Sort, f: &Sort) -> Term {
    let cols = rows[0].len();
    make_array(
        key.clone(),
        Sort::new_array(key.clone(), f.clone(), cols),
        rows.iter()
            .map(|r| make_array(key.clone(), f.clone(), r.clone()))
            .collect(),
    )
}

/// `m v`, for `m` given by its entries.
fn mat_vec(m: &[Vec<Term>], v: &[Term]) -> Vec<Term> {
    m.iter()
        .map(|row| {
            term(
                PF_ADD,
                row.iter()
                    .zip(v)
                    .map(|(a, b)| term![PF_MUL; a.clone(), b.clone()])
                    .collect(),
            )
        })
        .collect()
}

/// Index literals for a matrix's index sort, up to `n`.
fn indices(key: &Sort, n: usize) -> Vec<Term> {
    key.elems_iter().take(n).collect()
}

/// A product that has been outlined, and still needs its Freivalds check.
struct Product {
    /// The left factor.
    a: Term,
    /// The right factor.
    b: Term,
    /// The prover's product, by entry.
    c: Vec<Vec<Term>>,
    /// The index literals of the factors' index sort.
    idx: Vec<Term>,
    /// The entry field.
    f: Sort,
}

/// Replace each matrix product in the constraints with a prover-supplied
/// product and a Freivalds check at a random vector. See the module docs.
pub fn mat_ip(c: &mut Computation) {
    if !c.terms_postorder().any(|t| t.op() == &MATMUL) {
        return;
    }
    assert_eq!(c.outputs.len(), 1, "mat_ip expects a single assertion");
    let ns = Namespace::default().subspace("matmul");
    let mut pass = MatIp {
        ns: ns.clone(),
        products: Vec::new(),
    };
    pass.traverse(c);
    let products = pass.products;
    debug!("mat_ip: outlined {} matrix product(s)", products.len());

    let mut assertions = Vec::new();
    for p in &products {
        let cols = p.c[0].len();
        let (rows, inner, ..) = shape(&p.a);
        // Coin `j` of a width-`cols` vector, named by that role alone: every
        // product's j'th coin gets the same name, which is this transform
        // declaring that these checks are independent and so may share a coin.
        // `chall::share_challenges` then either merges them or renames them
        // apart, per `--ir-share-challenges`.
        let v: Vec<Term> = (0..cols)
            .map(|j| {
                term(
                    Op::new_chall(ns.fqn(format!("v{j}_{cols}")), p.f.as_pf().clone()),
                    p.c.iter().flatten().cloned().collect(),
                )
            })
            .collect();
        // C v == A (B v)
        let bv = mat_vec(&entries(&p.b, &p.idx, inner, cols), &v);
        let abv = mat_vec(&entries(&p.a, &p.idx, rows, inner), &bv);
        let cv = mat_vec(&p.c, &v);
        assertions.extend(cv.into_iter().zip(abv).map(|(l, r)| term![Op::Eq; l, r]));
    }
    assertions.push(c.outputs[0].clone());
    c.outputs[0] = term(AND, assertions);
}

struct MatIp {
    ns: Namespace,
    products: Vec<Product>,
}

impl RewritePass for MatIp {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        c: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        if orig.op() != &MATMUL {
            return None;
        }
        let cs = rewritten_children();
        let (a, b) = (cs[0].clone(), cs[1].clone());
        let (rows, inner, key, f) = shape(&a);
        let (_, cols, ..) = shape(&b);
        let ns = self.ns.subspace(self.products.len());
        let idx = indices(&key, rows.max(inner).max(cols));

        // The prover's product, and a variable per entry of it.
        let prod = term![MATMUL; a.clone(), b.clone()];
        let c_entries: Vec<Vec<Term>> = (0..rows)
            .map(|i| {
                (0..cols)
                    .map(|j| {
                        c.new_var(
                            &ns.fqn(format!("c{i}_{j}")),
                            f.clone(),
                            PROVER_VIS,
                            Some(entry(&prod, &idx, i, j)),
                        )
                    })
                    .collect()
            })
            .collect();

        let out = matrix(&c_entries, &key, &f);
        self.products.push(Product {
            a,
            b,
            c: c_entries,
            idx,
            f,
        });
        Some(out)
    }
}

/// Expand the matrix operators left in the constraints into field arithmetic.
pub fn mat_lower(c: &mut Computation) {
    if !c
        .terms_postorder()
        .any(|t| t.op() == &MATMUL || t.op() == &MATADD)
    {
        return;
    }
    MatLower.traverse(c);
}

struct MatLower;

impl RewritePass for MatLower {
    fn visit<F: Fn() -> Vec<Term>>(
        &mut self,
        _c: &mut Computation,
        orig: &Term,
        rewritten_children: F,
    ) -> Option<Term> {
        let is_mul = orig.op() == &MATMUL;
        if !is_mul && orig.op() != &MATADD {
            return None;
        }
        let cs = rewritten_children();
        let (a, b) = (cs[0].clone(), cs[1].clone());
        let (rows, inner, key, f) = shape(&a);
        let (_, cols, ..) = shape(&b);
        let idx = indices(&key, rows.max(inner).max(cols));
        let ae = entries(&a, &idx, rows, inner);
        let out: Vec<Vec<Term>> = if is_mul {
            let be = entries(&b, &idx, inner, cols);
            (0..rows)
                .map(|i| {
                    (0..cols)
                        .map(|j| {
                            term(
                                PF_ADD,
                                (0..inner)
                                    .map(|k| term![PF_MUL; ae[i][k].clone(), be[k][j].clone()])
                                    .collect(),
                            )
                        })
                        .collect()
                })
                .collect()
        } else {
            let be = entries(&b, &idx, rows, inner);
            (0..rows)
                .map(|i| {
                    (0..inner)
                        .map(|j| term![PF_ADD; ae[i][j].clone(), be[i][j].clone()])
                        .collect()
                })
                .collect()
        };
        Some(matrix(&out, &key, &f))
    }
}
