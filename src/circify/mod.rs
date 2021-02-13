use crate::ir::term::*;

use std::collections::HashMap;
use std::fmt::Display;

pub mod mem;

type Version = usize;

type VarName = String;

/// A *value*. Can be a term, or a reference.
enum Val<T> {
    Term(T),
    Ref(Box<Val<T>>),
}

/// A *location*. Can be a local name, or a reference.
enum Loc {
    Name(VarName),
    Ref(AbsLoc),
}

/// An absolute *location*.
struct AbsLoc {
    /// Lexical scope index, from the top of the stack
    scope_idx: ScopeIdx,
    /// Name in that scope
    name: VarName,
}

struct ScopeIdx {
    fn_idx: usize,
    lex_idx: usize,
}

#[derive(Hash, PartialEq, Eq)]
struct VerVar {
    name: VarName,
    ver: Version,
}

struct LexScope<Ty, T> {
    tys: HashMap<VarName, Ty>,
    vers: HashMap<VarName, Version>,
    terms: HashMap<VerVar, Val<T>>,
    prefix: String,
}

/// A language whose state can be managed
trait State {
    /// Type for this language
    type Ty: Display;
    /// Terms for this language
    type T: Display;

    // TODO: memory?
    fn declare(&self, ty: Self::Ty, raw_name: String, user_name: Option<String>) -> Self::T;
    fn ite(&self, cond: Term, t: Self::T, f: Self::T) -> Self::T;
}
