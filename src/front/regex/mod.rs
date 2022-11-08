#![allow(dead_code)]
#![allow(missing_docs)]
use regex_syntax::Parser;
use regex_syntax::hir::Hir;
use regex_syntax::hir::HirKind::{Concat, Alternation, Repetition, Literal};
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

fn to_regex<'a>(h: &'a Hir) -> Regex<char> {
    match h.kind() {
       Concat(l) =>
          match l.split_first() {
             Some((h,ts)) =>
                ts.iter().fold(to_regex(h), |a,b| Regex::App(Box::new(a), Box::new(to_regex(b)))),
             None => Regex::Nil
          },
       Alternation(l) =>
          match l.split_first() {
             Some((h,ts)) =>
                ts.iter().fold(to_regex(h), |a,b| Regex::Alt(Box::new(a), Box::new(to_regex(b)))),
             None => Regex::Empty
          },
       Repetition(r) => {
            let inner = Box::new(to_regex(&r.hir));
            match r.kind {
                OneOrMore =>
                  Regex::App(inner.clone(), Box::new(Regex::Star(inner))),
                ZeroOrMore =>
                  Regex::Star(inner),
                _=> panic!("Supported repetition operators [+,*]: {:?}", r)
            }
       },
       Literal(Unicode(c)) => Regex::Char(*c),
       _ => panic!("Unsupported regex {:?}", h)
    }
}

pub fn regex_parser(r: &str) -> Regex<char> {
    match Parser::new().parse(r) {
        Ok(hir) => to_regex(&hir),
        Err(e) => panic!("Error parsing regexp {}", e)
    }
}


