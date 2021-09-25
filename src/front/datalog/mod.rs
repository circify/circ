//! Datalog implementation

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::str::FromStr;

use ahash::AHashMap;
use log::debug;
use rug::Integer;

use crate::circify::{Circify, Loc, Val};
use crate::front::zokrates::{PROVER_VIS, PUBLIC_VIS};
use crate::ir::term::*;
use crate::ir::opt::cfold::fold;
use crate::ir::term::extras::as_uint_constant;

use super::FrontEnd;

pub mod parser;
pub mod term;
pub mod ty;

use parser::ast;

/// Inputs to the datalog compilier
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
    /// How many recursions to tolerate
    pub rec_limit: usize,
}

struct Gen<'ast> {
    rules: AHashMap<&'ast str, &'ast ast::Rule_<'ast>>,
    stack_by_fn: AHashMap<&'ast str, Vec<Option<Integer>>>,
    rec_limit: usize,
    circ: Circify<term::Datalog>,
}

impl<'ast> Gen<'ast> {
    fn new(rec_limit: usize) -> Self {
        Self {
            rules: AHashMap::new(),
            rec_limit,
            stack_by_fn: AHashMap::new(),
            // TODO: values !?
            circ: Circify::new(term::Datalog::new()),
        }
    }

    /// Attempt to enter a funciton.
    /// Returns `false` if doing so would violate the recursion limit.
    fn enter_function(&mut self, name: &'ast str, dec_value: Option<Integer>) -> bool {
        let e = self.stack_by_fn.entry(name).or_insert_with(|| Vec::new());
        //assert_eq!(e.last().and_then(|l| l.as_ref()).is_some(), dec_value.is_some());
        let do_enter = if let (Some(last_val), Some(this_val)) = (e.last().and_then(|l| l.as_ref()), dec_value.as_ref()) {
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
            self.rules.insert(&r.name.value, r);
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
                    let size = usize::from_str(&size.value).expect("bad array size");
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

    fn entry_rule(&mut self, name: &'ast str) {
        let rule = *self
            .rules
            .get(name)
            .unwrap_or_else(|| panic!("No entry rule: {}", name));
        self.enter_function(name, None);
        for d in &rule.args {
            let (ty, public) = self.ty(&d.ty);
            let vis = if public { PUBLIC_VIS } else { PROVER_VIS };
            self.circ
                .declare(d.ident.value.into(), &ty, public, vis)
                .unwrap();
        }
        let r = self.rule_cases(&rule);
        self.exit_function(name);
        self.circ.assert(r.as_bool());
    }

    fn rule_cases(&mut self, rule: &'ast ast::Rule_) -> term::T {
        rule.conds
            .iter()
            .map(|c| self.condition(c))
            .fold(term::bool_lit(false), |x, y| term::or(&x, &y).unwrap())
    }

    fn condition(&mut self, c: &'ast ast::Condition) -> term::T {
        if let Some(decls) = c.existential.as_ref() {
            for d in &decls.declarations {
                let (ty, _public) = self.ty(&d.ty);
                self.circ
                    .declare(d.ident.value.into(), &ty, false, None)
                    .unwrap();
            }
        }
        c.exprs
            .iter()
            .map(|e| self.expr(e, true))
            .fold(term::bool_lit(true), |x, y| term::and(&x, &y).unwrap())
    }

    fn ident(&mut self, i: &'ast ast::Ident) -> term::T {
        self.circ
            .get_value(Loc::local(i.value.to_owned()))
            .expect("lookup")
            .unwrap_term()
    }
    /// Generate IR for an expression.
    ///
    /// * `top_level` indicates whether this expression is a top-level expression in a condition.
    fn expr(&mut self, e: &'ast ast::Expression, top_level: bool) -> term::T {
        match e {
            &ast::Expression::Binary(ref b) => self.bin_expr(b),
            &ast::Expression::Unary(ref u) => self.un_expr(u),
            &ast::Expression::Paren(ref i, _) => self.expr(i, top_level),
            &ast::Expression::Identifier(ref i) => self.ident(i),
            &ast::Expression::Literal(ref i) => self.literal(i),
            &ast::Expression::Access(ref c) => {
                let arr = self.ident(&c.arr);
                c.idxs.iter().fold(arr, |arr, idx| {
                    let idx = self.expr(idx, false);
                    term::array_idx(&arr, &idx).unwrap()
                })
            }
            &ast::Expression::Call(ref c) => {
                let args = c
                    .args
                    .iter()
                    .map(|a| self.expr(a, false))
                    .collect::<Vec<_>>();
                match c.fn_name.value {
                    "to_field" => {
                        assert_eq!(1, args.len(), "to_field takes 1 argument: {:?}", c.span);
                        term::uint_to_field(&args[0]).unwrap()
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
                        let opt_const = if let Some((i, _)) = rule.args.iter().enumerate().filter(|&(_, arg)| arg.dec.is_some()).next() {
                            let ir = &args[i].ir;
                            let reduced_ir = fold(ir);
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
                            let r = self.rule_cases(&rule);
                            self.exit_function(name);
                            r
                        } else {
                            term::bool_lit(false)
                        }
                    }
                }
            }
        }
    }
    fn literal(&mut self, e: &ast::Literal) -> term::T {
        match e {
            &ast::Literal::BinLiteral(ref b) => {
                let len = b.value.len() as u8 - 2;
                let val = u64::from_str_radix(&b.value[2..], 2).unwrap();
                term::uint_lit(val, len)
            }
            &ast::Literal::HexLiteral(ref b) => {
                let len = (b.value.len() as u8 - 2) * 4;
                let val = u64::from_str_radix(&b.value[2..], 16).unwrap();
                term::uint_lit(val, len)
            }
            &ast::Literal::DecimalLiteral(ref b) => {
                let val = Integer::from_str(&b.value).unwrap();
                term::pf_lit(val)
            }
            &ast::Literal::BooleanLiteral(ref b) => {
                let val = bool::from_str(&b.value).unwrap();
                term::bool_lit(val)
            }
        }
    }
    fn bin_expr(&mut self, e: &'ast ast::BinaryExpression) -> term::T {
        let l = self.expr(&e.left, false);
        let r = self.expr(&e.right, false);
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
        res.expect("Bad expression")
    }
    fn un_expr(&mut self, e: &'ast ast::UnaryExpression) -> term::T {
        let l = self.expr(&e.expression, false);
        let res = match &e.op {
            ast::UnaryOperator::BitNot(_) => term::bitnot(&l),
            ast::UnaryOperator::Not(_) => term::not(&l),
            ast::UnaryOperator::Neg(_) => term::neg(&l),
        };
        res.expect("Bad expression")
    }
}

/// The Datalog front-end. Implements [FrontEnd].
pub struct Datalog;

impl FrontEnd for Datalog {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let mut f = File::open(&i.file).unwrap();
        let mut buffer = String::new();
        f.read_to_string(&mut buffer).unwrap();
        let ast = parser::parse(&buffer);
        let ast = match ast {
            Ok(ast) => ast,
            Err(e) => {
                println!("{}", e);
                panic!("parse error!")
            }
        };
        println!("{:#?}", ast);
        let mut g = Gen::new(i.rec_limit);
        g.register_rules(&ast);
        g.entry_rule("main");
        g.circ.consume().borrow().clone()
    }
}
