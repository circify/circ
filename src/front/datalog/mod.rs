//! Datalog implementation

use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use std::str::FromStr;

use ahash::AHashMap;
use rug::Integer;

use crate::circify::{Circify, Loc, Val};
use crate::ir::term::*;

use super::FrontEnd;

pub mod parser;
pub mod term;
pub mod ty;

use parser::ast;

/// Inputs to the datalog compilier
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
}

struct Gen<'ast> {
    rules: AHashMap<&'ast str, &'ast ast::Rule_<'ast>>,
    circ: Circify<term::Datalog>,
}

impl<'ast> Gen<'ast> {
    fn new() -> Self {
        Self {
            rules: AHashMap::new(),
            // TODO: values !?
            circ: Circify::new(term::Datalog::new()),
        }
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
            match &ty.ty {
                ast::Type::Bool(_) => ty::Ty::Bool,
                ast::Type::Field(_) => ty::Ty::Field,
                ast::Type::Uint(u) => {
                    ty::Ty::Uint(u8::from_str(&u.type_name[1..]).expect("bad uN"))
                }
            },
            ty.qualifier
                .as_ref()
                .map(|q| match q {
                    ast::Visibility::Private(_) => false,
                    ast::Visibility::Public(_) => true,
                })
                .unwrap_or(false),
        )
    }

    fn entry_rule(&mut self, name: &str) {
        let rule = *self
            .rules
            .get(name)
            .unwrap_or_else(|| panic!("No entry rule: {}", name));
        self.circ.enter_fn(name.into(), None);
        self.circ.enter_scope();
        for d in &rule.args {
            let (ty, public) = self.ty(&d.ty);
            self.circ
                .declare(d.ident.value.into(), &ty, public, None)
                .unwrap();
        }
        let r = self.rule_cases(&rule);
        self.circ.assert(r.as_bool());
        self.circ.exit_scope();
        self.circ.exit_fn();
    }

    fn rule_cases(&mut self, rule: &ast::Rule_) -> term::T {
        rule.conds
            .iter()
            .map(|c| self.condition(c))
            .fold(term::bool_lit(false), |x, y| term::or(&x, &y).unwrap())
    }

    fn condition(&mut self, c: &ast::Condition) -> term::T {
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
            .map(|e| self.expr(e))
            .fold(term::bool_lit(true), |x, y| term::and(&x, &y).unwrap())
    }
    fn expr(&mut self, e: &ast::Expression) -> term::T {
        match e {
            &ast::Expression::Binary(ref b) => self.bin_expr(b),
            &ast::Expression::Unary(ref u) => self.un_expr(u),
            &ast::Expression::Paren(ref i, _) => self.expr(i),
            &ast::Expression::Identifier(ref i) => {
                self.circ.get_value(Loc::local(i.value.to_owned())).expect("lookup").unwrap_term()
            }
            &ast::Expression::Literal(ref i) => self.literal(i),
            &ast::Expression::Call(ref c) => todo!(),
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
    fn bin_expr(&mut self, e: &ast::BinaryExpression) -> term::T {
        let l = self.expr(&e.left);
        let r = self.expr(&e.right);
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
    fn un_expr(&mut self, e: &ast::UnaryExpression) -> term::T {
        let l = self.expr(&e.expression);
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
        let mut g = Gen::new();
        g.register_rules(&ast);
        g.entry_rule("main");
        g.circ.consume().borrow().clone()
    }
}
