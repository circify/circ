//! Datalog implementation

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::str::FromStr;

use fxhash::FxHashMap;
use log::debug;
use rug::Integer;

use crate::cfg::cfg;
use crate::circify::{Circify, Loc, Val};
use crate::front::{PROVER_VIS, PUBLIC_VIS};
use crate::ir::opt::cfold::fold;
use crate::ir::term::extras::as_uint_constant;
use crate::ir::term::*;

use super::FrontEnd;

pub mod error;
pub mod parser;
pub mod term;
pub mod ty;

use error::{Error, ErrorKind, Result};
use parser::ast;

/// Inputs to the datalog compilier
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
}

struct Gen<'ast> {
    rules: FxHashMap<&'ast str, &'ast ast::Rule_<'ast>>,
    stack_by_fn: FxHashMap<&'ast str, Vec<Option<Integer>>>,
    rec_limit: usize,
    circ: Circify<term::Datalog>,
}

impl<'ast> Gen<'ast> {
    fn new(rec_limit: usize) -> Self {
        Self {
            rules: FxHashMap::default(),
            rec_limit,
            stack_by_fn: FxHashMap::default(),
            // TODO: values !?
            circ: Circify::new(term::Datalog::new()),
        }
    }

    /// Attempt to enter a funciton.
    /// Returns `false` if doing so would violate the recursion limit.
    fn enter_function(&mut self, name: &'ast str, dec_value: Option<Integer>) -> bool {
        let e = self.stack_by_fn.entry(name).or_default();
        //assert_eq!(e.last().and_then(|l| l.as_ref()).is_some(), dec_value.is_some());
        let do_enter = if let (Some(last_val), Some(this_val)) =
            (e.last().and_then(|l| l.as_ref()), dec_value.as_ref())
        {
            last_val > this_val
        } else {
            e.len() <= self.rec_limit
        };
        if do_enter {
            e.push(dec_value);
            self.circ.enter_fn(name.into(), None);
            self.circ.enter_scope();
        }
        do_enter
    }

    fn exit_function(&mut self, name: &'ast str) {
        let e = self.stack_by_fn.get_mut(name).unwrap();
        e.pop();
        if e.is_empty() {
            self.stack_by_fn.remove(name);
        }
        self.circ.exit_scope();
        self.circ.exit_fn();
    }

    fn register_rules(&mut self, pgm: &'ast ast::Program<'ast>) {
        for r in &pgm.rules {
            assert!(!self.rules.contains_key(&r.name.value));
            self.rules.insert(r.name.value, r);
        }
    }

    /// Returns (ty, public)
    fn ty(&self, ty: &ast::QualType<'ast>) -> (ty::Ty, bool) {
        (
            ty.ty.array_sizes.iter().fold(
                match &ty.ty.base {
                    ast::BaseType::Bool(_) => ty::Ty::Bool,
                    ast::BaseType::Field(_) => ty::Ty::Field,
                    ast::BaseType::Uint(u) => {
                        ty::Ty::Uint(u8::from_str(&u.type_name[1..]).expect("bad uN"))
                    }
                },
                |t, size| {
                    let size = usize::from_str(size.value).expect("bad array size");
                    ty::Ty::Array(size, Box::new(t))
                },
            ),
            ty.qualifier
                .as_ref()
                .map(|q| match q {
                    ast::Visibility::Private(_) => false,
                    ast::Visibility::Public(_) => true,
                })
                .unwrap_or(false),
        )
    }

    fn entry_rule(&mut self, name: &'ast str) -> Result<()> {
        let rule = *self
            .rules
            .get(name)
            .ok_or_else(|| ErrorKind::MissingEntry(name.into()))?;
        self.enter_function(name, None);
        for d in &rule.args {
            let (ty, public) = self.ty(&d.ty);
            let vis = if public { PUBLIC_VIS } else { PROVER_VIS };
            self.circ
                .declare_input(d.ident.value.into(), &ty, vis, None, false)?;
        }
        let r = self.rule_cases(rule)?;
        self.exit_function(name);
        self.circ.assert(r.as_bool());
        Ok(())
    }

    fn rule_cases(&mut self, rule: &'ast ast::Rule_) -> Result<'ast, term::T> {
        rule.conds.iter().try_fold(term::bool_lit(false), |x, y| {
            let cond = self.condition(y)?;
            term::or(&x, &cond).map_err(|e| Error::from(e).with_span(rule.span))
        })
    }

    fn condition(&mut self, c: &'ast ast::Condition) -> Result<'ast, term::T> {
        if let Some(decls) = c.existential.as_ref() {
            for d in &decls.declarations {
                let (ty, _public) = self.ty(&d.ty);
                self.circ
                    .declare_input(d.ident.value.into(), &ty, PROVER_VIS, None, true)?;
            }
        }
        c.exprs.iter().try_fold(term::bool_lit(true), |x, y| {
            let cond = self.expr(y, true)?;
            term::and(&x, &cond).map_err(|e| Error::from(e).with_span(*y.span()))
        })
    }

    fn ident(&mut self, i: &'ast ast::Ident) -> Result<'ast, term::T> {
        Ok(self
            .circ
            .get_value(Loc::local(i.value.to_owned()))?
            .unwrap_term())
    }

    /// Generate IR for an expression.
    ///
    /// * `top_level` indicates whether this expression is a top-level expression in a condition.
    fn expr(&mut self, e: &'ast ast::Expression, top_level: bool) -> Result<'ast, term::T> {
        match e {
            ast::Expression::Binary(ref b) => self.bin_expr(b),
            ast::Expression::Unary(ref u) => self.un_expr(u),
            ast::Expression::Paren(ref i, _) => self.expr(i, top_level),
            ast::Expression::Identifier(ref i) => self.ident(i),
            ast::Expression::Literal(ref i) => self.literal(i),
            ast::Expression::Access(ref c) => {
                let arr = self.ident(&c.arr)?;
                c.idxs.iter().try_fold(arr, |arr, idx| {
                    let idx_v = self.expr(idx, false)?;
                    term::array_idx(&arr, &idx_v).map_err(|err| Error::new(err, *idx.span()))
                })
            }
            ast::Expression::Call(ref c) => {
                let args = c
                    .args
                    .iter()
                    .map(|a| self.expr(a, false))
                    .collect::<Result<Vec<_>>>()?;
                match c.fn_name.value {
                    "to_field" => {
                        assert_eq!(1, args.len(), "to_field takes 1 argument: {:?}", c.span);
                        term::uint_to_field(&args[0]).map_err(|err| Error::new(err, c.span))
                    }
                    name => {
                        assert!(
                            top_level,
                            "Rules must be at the top level {} at {:?}",
                            name, c.span
                        );
                        let rule = *self
                            .rules
                            .get(name)
                            .unwrap_or_else(|| panic!("No entry rule: {}", name));
                        let opt_const = if let Some((i, _)) = rule
                            .args
                            .iter()
                            .enumerate()
                            .find(|&(_, arg)| arg.dec.is_some())
                        {
                            let ir = &args[i].ir;
                            let reduced_ir = fold(ir, &[]);
                            let r = as_uint_constant(&reduced_ir);
                            debug!("Dec arg: {}, const value {:?}", rule.args[i].ident.value, r);
                            r
                        } else {
                            None
                        };
                        let can_call = self.enter_function(name, opt_const);
                        if can_call {
                            for (d, actual_arg) in rule.args.iter().zip(&args) {
                                let (ty, _public) = self.ty(&d.ty);
                                self.circ
                                    .declare_init(
                                        d.ident.value.into(),
                                        ty,
                                        Val::Term(actual_arg.clone()),
                                    )
                                    .unwrap();
                            }
                            let r = self.rule_cases(rule)?;
                            self.exit_function(name);
                            Ok(r)
                        } else {
                            Ok(term::bool_lit(false))
                        }
                    }
                }
            }
        }
    }
    fn literal(&mut self, e: &ast::Literal) -> Result<'ast, term::T> {
        match e {
            ast::Literal::BinLiteral(ref b) => {
                let len = b.value.len() as u8 - 2;
                let val = u64::from_str_radix(&b.value[2..], 2).unwrap();
                Ok(term::uint_lit(val, len))
            }
            ast::Literal::HexLiteral(ref b) => {
                let len = (b.value.len() as u8 - 2) * 4;
                let val = u64::from_str_radix(&b.value[2..], 16).unwrap();
                Ok(term::uint_lit(val, len))
            }
            ast::Literal::DecimalLiteral(ref b) => {
                let val = Integer::from_str(b.value).unwrap();
                Ok(term::pf_lit(val))
            }
            ast::Literal::BooleanLiteral(ref b) => {
                let val = bool::from_str(b.value).unwrap();
                Ok(term::bool_lit(val))
            }
        }
    }
    fn bin_expr(&mut self, e: &'ast ast::BinaryExpression) -> Result<'ast, term::T> {
        let l = self.expr(&e.left, false)?;
        let r = self.expr(&e.right, false)?;
        let res = match &e.op {
            ast::BinaryOperator::BitXor => term::bitxor(&l, &r),
            ast::BinaryOperator::BitAnd => term::bitand(&l, &r),
            ast::BinaryOperator::BitOr => term::bitor(&l, &r),
            ast::BinaryOperator::RightShift => term::shr(&l, &r),
            ast::BinaryOperator::LeftShift => term::shl(&l, &r),
            ast::BinaryOperator::Or => term::or(&l, &r),
            ast::BinaryOperator::And => term::and(&l, &r),
            ast::BinaryOperator::Add => term::add(&l, &r),
            ast::BinaryOperator::Sub => term::sub(&l, &r),
            ast::BinaryOperator::Mul => term::mul(&l, &r),
            ast::BinaryOperator::Div => term::div(&l, &r),
            ast::BinaryOperator::Rem => term::rem(&l, &r),
            ast::BinaryOperator::Eq => term::eq(&l, &r),
            ast::BinaryOperator::Lt => term::lt(&l, &r),
            ast::BinaryOperator::Gt => term::gt(&l, &r),
            ast::BinaryOperator::Lte => term::lte(&l, &r),
            ast::BinaryOperator::Gte => term::gte(&l, &r),
        };
        res.map_err(|err| Error::new(err, e.span))
    }
    fn un_expr(&mut self, e: &'ast ast::UnaryExpression) -> Result<'ast, term::T> {
        let l = self.expr(&e.expression, false)?;
        let res = match &e.op {
            ast::UnaryOperator::BitNot(_) => term::bitnot(&l),
            ast::UnaryOperator::Not(_) => term::not(&l),
            ast::UnaryOperator::Neg(_) => term::neg(&l),
        };
        res.map_err(|err| Error::new(err, e.span))
    }

    // Begin prim-rec linting
    fn lint_rules(&mut self) -> Result<()> {
        let rules: Vec<&'ast ast::Rule_> = self.rules.values().cloned().collect();
        let bug_if = rules.iter().try_fold(term::bool_lit(false), |x, rule| {
            let cond = self.lint_rule(rule)?;
            term::or(&x, &cond).map_err(|e| Error::from(e).with_span(rule.span))
        })?;
        self.circ.assert(bug_if.as_bool());
        Ok(())
    }

    fn lint_rule(&mut self, rule: &'ast ast::Rule_) -> Result<'ast, term::T> {
        if let Some((arg_idx, _)) = rule
            .args
            .iter()
            .enumerate()
            .find(|(_, arg)| arg.dec.is_some())
        {
            self.enter_function(rule.name.value, None);
            for d in &rule.args {
                let (ty, public) = self.ty(&d.ty);
                let vis = if public { PUBLIC_VIS } else { PROVER_VIS };
                self.circ
                    .declare_input(d.ident.value.into(), &ty, vis, None, false)?;
            }
            let mut bug_in_rule_if_any = Vec::new();
            for cond in &rule.conds {
                let mut bug_conditions = Vec::new();
                debug!("Start case: {}", &rule.name.value);
                self.circ.enter_scope();
                if let Some(decls) = cond.existential.as_ref() {
                    for d in &decls.declarations {
                        let (ty, _public) = self.ty(&d.ty);
                        self.circ
                            .declare_input(d.ident.value.into(), &ty, None, None, true)?;
                    }
                }
                let mut bad_recursion = Vec::new();
                for atom in &cond.exprs {
                    if let ast::Expression::Call(c) = &atom {
                        if c.fn_name.value == rule.name.value {
                            let formal_arg = self
                                .circ
                                .get_value(Loc::local(rule.args[arg_idx].ident.value.to_owned()))?
                                .unwrap_term();
                            let actual_arg = self.expr(&c.args[arg_idx], false)?;
                            let bug_cond = term::gte(&actual_arg, &formal_arg)?;
                            debug!("Bug if: {}", bug_cond);
                            bad_recursion.push(bug_cond);
                            continue;
                        }
                    }
                    let force = self.expr(atom, true)?;
                    debug!("Force: {}", force);
                    bug_conditions.push(force);
                }
                bug_in_rule_if_any.push(term::and(
                    &bug_conditions
                        .into_iter()
                        .try_fold(term::bool_lit(true), |x, y| {
                            term::and(&x, &y).map_err(|e| Error::from(e).with_span(rule.span))
                        })?,
                    &bad_recursion
                        .into_iter()
                        .try_fold(term::bool_lit(false), |x, y| {
                            term::or(&x, &y).map_err(|e| Error::from(e).with_span(rule.span))
                        })?,
                )?);
                self.circ.exit_scope();
            }
            self.exit_function(rule.name.value);
            bug_in_rule_if_any
                .into_iter()
                .try_fold(term::bool_lit(false), |x, y| {
                    term::or(&x, &y).map_err(|e| Error::from(e).with_span(rule.span))
                })
        } else {
            Ok(term::bool_lit(false))
        }
    }
}

/// The Datalog front-end. Implements [FrontEnd].
pub struct Datalog;

impl FrontEnd for Datalog {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computations {
        let mut f = File::open(i.file).unwrap();
        let mut buffer = String::new();
        f.read_to_string(&mut buffer).unwrap();
        let ast = parser::parse(&buffer);
        let ast = match ast {
            Ok(ast) => ast,
            Err(e) => {
                println!("{e}");
                panic!("parse error!")
            }
        };
        let mut g = Gen::new(cfg().datalog.rec_limit);
        g.register_rules(&ast);
        let r = if cfg().datalog.lint_prim_rec {
            g.lint_rules()
        } else {
            g.entry_rule("main")
        };
        if let Err(e) = r {
            eprintln!("{e}");
            panic!()
        }
        let mut cs = Computations::new();
        let main_comp = g.circ.consume().borrow().clone();
        cs.comps.insert("main".to_string(), main_comp);
        cs
    }
}
