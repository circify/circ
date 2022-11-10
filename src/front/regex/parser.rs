#![allow(dead_code)]
#![allow(missing_docs)]
use regex_syntax::Parser;
use regex_syntax::hir::Hir;
use regex_syntax::hir::HirKind::{Group, Class, Concat, Alternation, Repetition, Literal};
use regex_syntax::hir::Literal::Unicode;
use regex_syntax::hir::RepetitionKind::{OneOrMore, ZeroOrMore};

pub mod Re {
    use hashconsing::{consign, HConsed, HashConsign};

    pub type Regex = HConsed<RegexF>;

    #[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
    pub enum RegexF {
        Nil,
        Empty,
        Char(char),
        Not(Regex),
        App(Regex, Regex),
        Alt(Regex, Regex),
        Star(Regex)
    }

    consign! {
        /// Factory for terms.
        let G = consign(10) for RegexF ;
    }

    // Smart constructors for regex simplification
    pub fn nil() -> Regex {
        G.mk(RegexF::Nil)
    }

    pub fn empty() -> Regex {
        G.mk(RegexF::Empty)
    }

    pub fn character(c: char) -> Regex {
        G.mk(RegexF::Char(c))
    }

    pub fn app(a: Regex, b: Regex) -> Regex {
        match (&*a, &*b) {
            (RegexF::App(x, y), _) => app(x.clone(), app(y.clone(), b)),
            (_, RegexF::Nil) => a,
            (RegexF::Nil, _) => b,
            (_, RegexF::Empty) | (RegexF::Empty, _) => empty(),
            (_, _) => G.mk(RegexF::App(a, b))
        }
    }

    pub fn alt(a: Regex, b: Regex) -> Regex {
        match (&*a, &*b) {
            (x, y) if x == y => a,
            (RegexF::Alt(x, y), _) => alt(x.clone(), alt(y.clone(), b)),
            (RegexF::Not(inner), _) if *inner == empty() =>
                G.mk(RegexF::Not(empty())),
            (RegexF::Empty, _) => b,
            (_, RegexF::Empty) => a,
            (x, y) if y < x => alt(b, a),
            (_, _) => G.mk(RegexF::Alt(a, b)),
        }
    }

    pub fn star(a: Regex) -> Regex {
        match *a {
            RegexF::Star(_) | RegexF::Nil => a,
            RegexF::Empty => nil(),
            _ => G.mk(RegexF::Star(a))
        }
    }

    pub fn not(a: Regex) -> Regex {
        match &*a {
            RegexF::Not(a) => a.clone(),
            _ => G.mk(RegexF::Not(a))
        }
    }
}

use Re::Regex;

/// Parser based on crate regex-syntax
fn to_regex<'a>(h: &'a Hir, ab: &'a str) -> Regex {
    match h.kind() {
       Concat(l) =>
            l.iter()
             .map(|a| to_regex(&a, ab))
             .reduce(Re::app)
             .unwrap_or(Re::nil()),
       Alternation(l) =>
           l.iter()
             .map(|a| to_regex(&a, ab))
             .reduce(Re::alt)
             .unwrap_or(Re::empty()),
       Repetition(r) => {
            let inner = to_regex(&r.hir, ab);
            match r.kind {
                OneOrMore => Re::app(inner.clone(), Re::star(inner)),
                ZeroOrMore => Re::star(inner),
                _=> panic!("Supported repetition operators [+,*]: {:?}", r)
            }
       },
       Group(g) => to_regex(&g.hir, ab),
       Class(_) => // this is dot
            ab.chars().map(|a| Re::character(a)).reduce(|acc, a| Re::alt(acc, a)).unwrap(),
       Literal(Unicode(c)) => Re::character(*c),
       _ => panic!("Unsupported regex {:?}", h)
    }
}

pub fn regex_parser<'a>(r: &'a str, ab: &'a str) -> Regex {
    match Parser::new().parse(r) {
        Ok(hir) => to_regex(&hir, &ab),
        Err(e) => panic!("Error parsing regexp {}", e)
    }
}

