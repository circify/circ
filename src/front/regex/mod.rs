#![allow(dead_code)]
#![allow(missing_docs)]
use regex_syntax::Parser;
use regex_syntax::hir::Hir;
use regex_syntax::hir::HirKind::{Group, Class, Concat, Alternation, Repetition, Literal};
use regex_syntax::hir::Literal::Unicode;
use regex_syntax::hir::RepetitionKind::{OneOrMore, ZeroOrMore};

#[derive(Debug, Clone)]
pub enum Regex<T> {
    Nil,
    Empty,
    Char(T),
    App(Box<Regex<T>>, Box<Regex<T>>),
    Alt(Box<Regex<T>>, Box<Regex<T>>),
    Star(Box<Regex<T>>)
}

fn to_regex<'a>(h: &'a Hir, ab: &str) -> Regex<char> {
    match h.kind() {
       Concat(l) =>
          match l.split_first() {
             Some((h,ts)) =>
                ts.iter().fold(to_regex(h, ab), |a,b| Regex::App(Box::new(a), Box::new(to_regex(b, ab)))),
             None => Regex::Nil
          },
       Alternation(l) =>
          match l.split_first() {
             Some((h,ts)) =>
                ts.iter().fold(to_regex(h, ab), |a,b| Regex::Alt(Box::new(a), Box::new(to_regex(b, ab)))),
             None => Regex::Empty
          },
       Repetition(r) => {
            let inner = Box::new(to_regex(&r.hir, ab));
            match r.kind {
                OneOrMore =>
                  Regex::App(inner.clone(), Box::new(Regex::Star(inner))),
                ZeroOrMore =>
                  Regex::Star(inner),
                _=> panic!("Supported repetition operators [+,*]: {:?}", r)
            }
       },
       Group(g) => to_regex(&g.hir, ab),
       Class(_) => // this is dot
            ab.chars().map(|a| Regex::Char(a)).reduce(|acc, a| Regex::Alt(Box::new(acc), Box::new(a))).unwrap(),
       Literal(Unicode(c)) => Regex::Char(*c),
       _ => panic!("Unsupported regex {:?}", h)
    }
}

pub fn regex_parser(r: &str, ab: &str) -> Regex<char> {
    match Parser::new().parse(r) {
        Ok(hir) => to_regex(&hir, &ab),
        Err(e) => panic!("Error parsing regexp {}", e)
    }
}


