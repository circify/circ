//! RAM checking
use super::hash::{MsHasher, UniversalHasher};
use super::*;
use crate::front::PROVER_VIS;
use crate::util::ns::Namespace;
use circ_fields::FieldT;
use log::trace;

/// Check a RAM
pub fn check_ram(c: &mut Computation, ram: Ram) {
    trace!(
        "Checking RAM {}, size {}, {} accesses",
        ram.id,
        ram.size,
        ram.accesses.len()
    );
    let f = ram.cfg.field.clone();
    let (only_init, default) = match &ram.boundary_conditions {
        BoundaryConditions::Default(d) => (false, d.clone()),
        BoundaryConditions::OnlyInit => (true, ram.cfg.zero.clone()),
        BoundaryConditions::Persistent(..) => panic!(),
    };
    let id = ram.id;
    let ns = Namespace::new().subspace(&format!("ram{id}"));
    let f_s = Sort::Field(f.clone());
    let mut new_var =
        |name: &str, val: Term| c.new_var(&ns.fqn(name), f_s.clone(), PROVER_VIS, Some(val));

    // (1) sort the transcript
    let field_tuples: Vec<Term> = ram
        .accesses
        .iter()
        .map(|a| a.to_field_tuple(&ram.cfg))
        .collect();
    let sorted_field_tuple_values: Vec<Term> = unmake_array(
        term![Op::ExtOp(ExtOp::Sort); make_array(f_s.clone(), check(&field_tuples[0]), field_tuples.clone())],
    );
    let sorted_accesses: Vec<Access> = sorted_field_tuple_values
        .into_iter()
        .enumerate()
        .map(|(i, v)| {
            Access::declare_trusted(
                &ram.cfg,
                |name: &str, term: Term| new_var(&format!("sort_a{i}_{name}"), term),
                v,
            )
        })
        .collect();
    let uhf_inputs: Vec<Term> = field_tuples
        .into_iter()
        .chain(sorted_accesses.iter().map(|a| a.to_field_tuple(&ram.cfg)))
        .collect();
    let uhf = UniversalHasher::new(ns.fqn("uhf_key"), &f, uhf_inputs.clone(), ram.cfg.len());
    let msh = MsHasher::new(ns.fqn("ms_hash_key"), &f, uhf_inputs);

    // (2) permutation argument
    let univ_hashes_unsorted: Vec<Term> = ram
        .accesses
        .iter()
        .map(|a| a.universal_hash(&ram.cfg, &uhf))
        .collect();
    let univ_hashes_sorted: Vec<Term> = sorted_accesses
        .iter()
        .map(|a| a.universal_hash(&ram.cfg, &uhf))
        .collect();
    let ms_hash_passes = term![EQ; msh.hash(univ_hashes_unsorted), msh.hash(univ_hashes_sorted)];

    // (3) check the sorted transcript
    let mut assertions = vec![ms_hash_passes];
    let n = sorted_accesses.len();
    let mut accs = sorted_accesses;

    // set c value if needed.
    if !only_init {
        accs[0].create = FieldBit::from_bool_lit(&ram.cfg, true);
        for i in 0..(n - 1) {
            let create = term![NOT; term![EQ; accs[i].idx.clone(), accs[i+1].idx.clone()]];
            accs[i + 1].create = FieldBit::from_bool(&ram.cfg, create);
        }
    }

    // (3a) v' = ite(a',v',v)
    for i in 0..(n - 1) {
        accs[i + 1].val = term_c![Op::Ite; accs[i+1].active.b.clone(), accs[i+1].val, accs[i].val];
    }

    assertions.push(accs[0].create.b.clone());

    let zero = pf_lit(f.new_v(0));
    fn sub(a: &Term, b: &Term) -> Term {
        term![PF_ADD; a.clone(), term![PF_NEG; b.clone()]]
    }

    let mut deltas = Vec::new();
    for j in 0..(n - 1) {
        // previous entry
        let i = &accs[j].idx;
        let t = &accs[j].time;
        let v = &accs[j].val;
        // this entry
        let i_n = &accs[j + 1].idx;
        let t_n = &accs[j + 1].time;
        let v_n = &accs[j + 1].val;
        let c_n = &accs[j + 1].create;
        let w_n = &accs[j + 1].write;

        let v_p = if only_init {
            v.clone()
        } else if j == 0 {
            default.clone()
        } else {
            term![ITE; c_n.b.clone(), default.clone(), v.clone()]
        };

        // delta = (1 - c')(t' - t)
        deltas.push(term![PF_MUL; c_n.nf.clone(), sub(t_n, t)]);

        // check c value if not computed: (i' - i)(1 - c') = 0
        if only_init {
            assertions.push(term![EQ; term![PF_MUL; sub(i_n, i), c_n.nf.clone()], zero.clone()]);
        }
        // writes allow a value change: (v' - v)(1 - w') = 0
        assertions.push(term![EQ; term![PF_MUL; sub(v_n, &v_p), w_n.nf.clone()], zero.clone()]);
    }

    // check that index blocks are unique
    if !only_init {
        if ram.cfg.sort_indices {
            let bits = ram.size.next_power_of_two().ilog2() as usize;
            trace!("Index difference checks ({bits} bits)");
            assertions.push(term![Op::PfFitsInBits(bits); accs[0].idx.clone()]);
            for j in 0..(n - 1) {
                let d = pf_sub(accs[j + 1].idx.clone(), accs[j].idx.clone());
                assertions.push(term![Op::PfFitsInBits(bits); d]);
            }
        } else {
            derivative_gcd(
                c,
                accs.iter().map(|a| a.idx.clone()).collect(),
                accs.iter().map(|a| a.create.b.clone()).collect(),
                &ns,
                &mut assertions,
                &f,
            );
        }
    }

    // check ranges
    assertions.push(c.outputs[0].clone());
    #[allow(clippy::type_complexity)]
    let range_checker: Box<
        dyn Fn(&mut Computation, Vec<Term>, &Namespace, &mut Vec<Term>, usize, &FieldT),
    > = if ram.cfg.split_times {
        Box::new(&bit_split_range_check)
    } else {
        Box::new(&range_check)
    };
    range_checker(
        c,
        deltas,
        &ns.subspace("time"),
        &mut assertions,
        ram.next_time + 1,
        &f,
    );
    c.outputs[0] = term(AND, assertions);
}

/// Ensure that each element of `values` is in `[0, n)`.
///
/// Assumes that each value is a field element.
/// Creates new variables in `c`.
/// Emits assertions to `assertions`.
fn range_check(
    c: &mut Computation,
    mut values: Vec<Term>,
    ns: &Namespace,
    assertions: &mut Vec<Term>,
    n: usize,
    f: &FieldT,
) {
    let ns = ns.subspace("range");
    let f_sort = Sort::Field(f.clone());
    debug_assert!(values.iter().all(|v| check(v) == f_sort));
    let mut ms_hash_inputs = values.clone();
    values.extend(f_sort.elems_iter().take(n));
    let sorted_term = unmake_array(
        term![Op::ExtOp(ExtOp::Sort); make_array(f_sort.clone(), f_sort.clone(), values.clone())],
    );
    let sorted: Vec<Term> = sorted_term
        .into_iter()
        .enumerate()
        .map(|(i, t)| {
            let full_name = ns.fqn(i);
            c.new_var(&full_name, f_sort.clone(), PROVER_VIS, Some(t))
        })
        .collect();

    // permutation argument
    ms_hash_inputs.extend(sorted.iter().cloned());
    let msh = MsHasher::new(ns.fqn("key"), f, ms_hash_inputs);
    assertions.push(term![EQ; msh.hash(values), msh.hash(sorted.clone())]);

    // delta: 0 or 1
    let neg_one = pf_lit(f.new_v(-1));
    let zero = pf_lit(f.new_v(0));
    for w in sorted.windows(2) {
        let d = term![PF_ADD; w[1].clone(), term![PF_NEG; w[0].clone()]];
        assertions.push(
            term![EQ; term![PF_MUL; d.clone(), term![PF_ADD; d, neg_one.clone()]], zero.clone()],
        );
    }

    // starts and end
    assert!(n > 0);
    let end = pf_lit(f.new_v(n - 1));
    assertions.push(term![EQ; sorted[0].clone(), zero]);
    assertions.push(term![EQ; sorted.last().unwrap().clone(), end]);
}

/// Ensure that each element of `values` is in `[0, n)`.
///
/// Assumes that each value is a field element.
/// Creates new variables in `c`.
/// Emits assertions to `assertions`.
///
/// Just bit-splits them all.
fn bit_split_range_check(
    _c: &mut Computation,
    values: Vec<Term>,
    _ns: &Namespace,
    assertions: &mut Vec<Term>,
    n: usize,
    f: &FieldT,
) {
    let m = n.next_power_of_two();
    let d = pf_lit(f.new_v(m - n));
    let bits = m.ilog2() as usize;
    trace!("Range check [0,{n})], rounded to [0,{m}), adding {d} ({bits} bits)");
    let f_sort = Sort::Field(f.clone());
    debug_assert!(values.iter().all(|v| check(v) == f_sort));
    for v in values {
        if m != n {
            assertions.push(term![Op::PfFitsInBits(bits); term![PF_ADD; v.clone(), d.clone()]]);
        }
        assertions.push(term![Op::PfFitsInBits(bits); v]);
    }
}

fn derivative_gcd(
    comp: &mut Computation,
    values: Vec<Term>,
    conditions: Vec<Term>,
    ns: &Namespace,
    assertions: &mut Vec<Term>,
    f: &FieldT,
) {
    let ns = ns.subspace("uniq");
    let fs = Sort::Field(f.clone());
    let pairs = term(
        Op::Array(fs.clone(), Sort::Tuple(Box::new([fs.clone(), Sort::Bool]))),
        values
            .clone()
            .into_iter()
            .zip(conditions.clone())
            .map(|(v, c)| term![Op::Tuple; v, c])
            .collect(),
    );
    let two_polys = term![Op::ExtOp(ExtOp::UniqDeriGcd); pairs];
    let s_coeffs = unmake_array(term![Op::Field(0); two_polys.clone()]);
    let t_coeffs = unmake_array(term![Op::Field(1); two_polys]);
    let mut decl_poly = |coeffs: Vec<Term>, poly_name: &str| -> Vec<Term> {
        coeffs
            .into_iter()
            .enumerate()
            .map(|(i, coeff)| {
                comp.new_var(
                    &ns.fqn(format!("{poly_name}{i}")),
                    fs.clone(),
                    PROVER_VIS,
                    Some(coeff),
                )
            })
            .collect()
    };
    let s_coeffs_skolem = decl_poly(s_coeffs, "s");
    let t_coeffs_skolem = decl_poly(t_coeffs, "t");

    let mut terms_that_define_all_polys = Vec::new();
    terms_that_define_all_polys.extend(values.iter().cloned());
    terms_that_define_all_polys.extend(conditions.iter().cloned());
    terms_that_define_all_polys.extend(s_coeffs_skolem.iter().cloned());
    terms_that_define_all_polys.extend(t_coeffs_skolem.iter().cloned());
    let n = values.len();
    let x = term(
        Op::PfChallenge(ns.fqn("x"), f.clone()),
        terms_that_define_all_polys,
    );
    let r = values;
    let c = conditions;
    let one = pf_lit(f.new_v(1));
    let zero = pf_lit(f.new_v(0));
    let s_of_x = horner(s_coeffs_skolem, &x, f);
    let t_of_x = horner(t_coeffs_skolem, &x, f);
    // X - r
    let x_minus_r = bimap(pf_sub, vec![x; n], r);
    // define p(X) = prod (c ? (X - r) : 1); compute at x
    let muxed = trimap_op(ITE, c.clone(), x_minus_r, vec![one.clone(); n]);
    let p_of_x = term(PF_MUL, muxed.clone());

    // compute dp(X) = (d/dX p)(x)
    let recip_x_minus_r: Vec<Term> = muxed
        .into_iter()
        .enumerate()
        .map(|(i, d)| {
            let recip = comp.new_var(
                &ns.fqn(format!("recip{i}")),
                fs.clone(),
                PROVER_VIS,
                Some(term![PF_RECIP; d.clone()]),
            );
            assertions.push(term![EQ; term![PF_MUL; recip.clone(), d], one.clone()]);
            recip
        })
        .collect();
    let dp_of_x = term(
        PF_ADD,
        trimap_op(
            ITE,
            c,
            bimap_op(PF_MUL, recip_x_minus_r, vec![p_of_x.clone(); n]),
            vec![zero; n],
        ),
    );
    // Check s(X)p(X) + t(X)dp(X) = 1 at X = x
    assertions.push(term![EQ;
        term![PF_ADD;
            term![PF_MUL; s_of_x, p_of_x],
            term![PF_MUL; t_of_x, dp_of_x]
        ],
        one
    ]);
}

fn pf_sub(a: Term, b: Term) -> Term {
    term![PF_ADD; a, term![PF_NEG; b]]
}

fn bimap(mut f: impl FnMut(Term, Term) -> Term, a: Vec<Term>, b: Vec<Term>) -> Vec<Term> {
    assert_eq!(a.len(), b.len());
    a.into_iter().zip(b).map(|(a, b)| f(a, b)).collect()
}

fn bimap_op(op: Op, a: Vec<Term>, b: Vec<Term>) -> Vec<Term> {
    assert_eq!(a.len(), b.len());
    a.into_iter()
        .zip(b)
        .map(|(a, b)| term![op.clone(); a, b])
        .collect()
}

fn trimap_op(op: Op, a: Vec<Term>, b: Vec<Term>, c: Vec<Term>) -> Vec<Term> {
    a.into_iter()
        .zip(b)
        .zip(c)
        .map(|((a, b), c)| term![op.clone(); a, b, c])
        .collect()
}

/// Returns a term equal to p(x) in f.
fn horner(p: Vec<Term>, x: &Term, f: &FieldT) -> Term {
    let mut acc = pf_lit(f.zero());
    for c in p.into_iter().rev() {
        acc = term![PF_ADD; term![PF_MUL; x.clone(), acc], c];
    }
    acc
}
