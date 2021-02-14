use crate::ir::term::*;

use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

pub mod mem;

type Version = usize;

type VarName = String;

type SsaName = String;

/// A *value*. Can be a term, or a reference.
#[derive(Clone, Debug)]
pub enum Val<T> {
    Term(T),
    Ref(Loc),
}

impl<T: Display> Display for Val<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Val::Term(t) => write!(f, "{}", t),
            Val::Ref(_) => write!(f, "REF"),
        }
    }
}

/// A *location*. Can be a name in the current scope, or a reference to an alternate scope.
#[derive(Debug, Clone)]
pub struct Loc {
    name: VarName,
    /// Optional (fn, lex) scope indices
    idx: Option<ScopeIdx>,
}

impl Loc {
    pub fn local(name: VarName) -> Self {
        Self { name, idx: None }
    }
}

#[derive(Debug, Clone)]
struct ScopeIdx {
    fn_: usize,
    lex: usize,
}

#[derive(Hash, PartialEq, Eq)]
struct VerVar {
    name: VarName,
    ver: Version,
}

struct LexEntry<Ty> {
    ver: Version,
    ssa_name: SsaName,
    name: String,
    ty: Ty,
}

impl<Ty> LexEntry<Ty> {
    pub fn next_ver(&mut self) {
        self.ver += 1;
        self.set_ssa_name();
    }
    fn set_ssa_name(&mut self) {
        self.ssa_name = format!("{}_v{}", self.name, self.ver);
    }
    pub fn new(name: String, ty: Ty) -> Self {
        let mut this = Self {
            ver: 0,
            ssa_name: "".to_string(),
            name,
            ty,
        };
        this.set_ssa_name();
        this
    }
}

struct LexScope<Ty> {
    entries: HashMap<VarName, LexEntry<Ty>>,
    prefix: String,
}

impl<Ty: Display> LexScope<Ty> {
    fn with_prefix(prefix: String) -> Self {
        Self {
            prefix,
            entries: HashMap::new(),
        }
    }
    fn declare(&mut self, name: VarName, ty: Ty) -> &SsaName {
        let p = &self.prefix;
        &self
            .entries
            .entry(name.clone())
            .and_modify(|e| {
                panic!("{} already declared as ty {}", name, e.ty);
            })
            .or_insert_with(|| LexEntry::new(format!("{}_{}", p, name), ty))
            .ssa_name
    }
    fn get_name(&self, name: &str) -> &SsaName {
        &self.entries.get(name).unwrap().ssa_name
    }
    fn get_ty(&self, name: &str) -> &Ty {
        &self.entries.get(name).unwrap().ty
    }
    fn next_ver(&mut self, name: &str) -> &SsaName {
        let e = self.entries.get_mut(name).unwrap();
        e.next_ver();
        &e.ssa_name
    }
    fn has_name(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }
}

pub struct CirCtx {
    pub mem: mem::MemManager,
    pub cs: Rc<RefCell<Constraints>>,
}

enum StateEntry<Ty> {
    Lex(LexScope<Ty>),
    Cond(Term),
    /// A block `name`, which has been broken out of if any condition is satisfied.
    Break(String, Vec<Term>),
}

pub struct FnFrame<Ty> {
    stack: Vec<StateEntry<Ty>>,
    scope_ctr: usize,
    prefix: String,
    has_return: bool,
}

impl<Ty: Display> FnFrame<Ty> {
    fn new(prefix: String, has_return: bool) -> Self {
        let mut this = Self {
            stack: Vec::new(),
            scope_ctr: 0,
            prefix,
            has_return,
        };
        this.enter_scope();
        this.enter_breakable(RET_BREAK_NAME.to_owned());
        this
    }
    fn last_lex_mut(&mut self) -> &mut LexScope<Ty> {
        self.stack
            .iter_mut()
            .rev()
            .filter_map(|f| match f {
                StateEntry::Lex(l) => Some(l),
                _ => None,
            })
            .next()
            .expect("No lexical scopes!")
    }
    fn declare(&mut self, name: VarName, ty: Ty) -> &SsaName {
        self.last_lex_mut().declare(name, ty)
    }
    fn enter_scope(&mut self) {
        self.stack
            .push(StateEntry::Lex(LexScope::with_prefix(format!(
                "{}_lex{}",
                self.prefix, self.scope_ctr
            ))));
        self.scope_ctr += 1;
    }
    #[track_caller]
    fn exit_scope(&mut self) {
        if let Some(StateEntry::Lex(_)) = self.stack.pop() {
        } else {
            panic!("Stack does not end with a lexical scope");
        }
    }
    fn enter_condition(&mut self, condition: Term) {
        assert!(check(&condition) == Sort::Bool);
        self.stack.push(StateEntry::Cond(condition));
    }
    #[track_caller]
    fn exit_condition(&mut self) {
        if let Some(StateEntry::Cond(_)) = self.stack.pop() {
        } else {
            panic!("Stack does not end with a condition");
        }
    }
    fn conditions(&self) -> Vec<Term> {
        let mut cs = Vec::new();
        for s in &self.stack {
            match s {
                StateEntry::Cond(t) => cs.push(t.clone()),
                StateEntry::Break(_, break_conds) => {
                    cs.extend(break_conds.iter().map(|c| term![Op::Not; c.clone()]))
                }
                _ => {}
            }
        }
        cs
    }

    fn enter_breakable(&mut self, name: String) {
        self.stack.push(StateEntry::Break(name, Vec::new()));
    }

    #[track_caller]
    fn exit_breakable(&mut self) {
        if let Some(StateEntry::Break(..)) = self.stack.pop() {
        } else {
            panic!("Stack does not end with a breakable block");
        }
    }

    fn break_(&mut self, name: &str) {
        // Walk back to the breakable block, accumulating conditions...
        let mut break_if = Vec::new();
        for s in self.stack.iter_mut().rev() {
            match s {
                StateEntry::Cond(c) => break_if.push(c.clone()),
                StateEntry::Break(name_, ref mut break_conds) => {
                    if name_ == name {
                        break_conds.push(if break_if.len() == 0 {
                            leaf_term(Op::Const(Value::Bool(true)))
                        } else {
                            term(Op::BoolNaryOp(BoolNaryOp::And), break_if)
                        });
                        return;
                    } else {
                        break_if.extend(break_conds.iter().map(|c| term![Op::Not; c.clone()]));
                    }
                }
                _ => {}
            }
        }
        panic!("Could not find breakable block: '{}'", name);
    }
}

/// A language whose state can be managed
pub trait Embeddable {
    /// Type for this language
    type Ty: Display + Clone;
    /// Terms for this language
    type T: Display + Clone;

    // TODO: memory?
    fn declare(
        &self,
        ctx: &mut CirCtx,
        ty: Self::Ty,
        raw_name: String,
        user_name: Option<String>,
    ) -> Self::T;
    fn ite(&self, ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T;
    fn assign(&self, ctx: &mut CirCtx, ty: Self::Ty, name: &str, t: Self::T) -> Self::T;
    fn values(&self) -> bool;
}

pub struct Circify<E: Embeddable> {
    e: E,
    vals: HashMap<String, Val<E::T>>,
    fn_stack: Vec<FnFrame<E::Ty>>,
    fn_ctr: usize,
    globals: LexScope<E::Ty>,
    cir_ctx: CirCtx,
    condition: Term,
}

impl<E: Embeddable> Circify<E> {
    pub fn new(e: E) -> Self {
        let cs = Rc::new(RefCell::new(Constraints::new(e.values())));
        Self {
            e,
            vals: HashMap::new(),
            fn_stack: Vec::new(),
            fn_ctr: 0,
            globals: LexScope::with_prefix("global".to_string()),
            cir_ctx: CirCtx {
                mem: mem::MemManager::new(cs.clone()),
                cs,
            },
            condition: leaf_term(Op::Const(Value::Bool(true))),
        }
    }

    /// Declares a new (unconstrained) value of
    pub fn declare(&mut self, name: VarName, ty: E::Ty, input: bool) {
        let ssa_name = if let Some(back) = self.fn_stack.last_mut() {
            back.declare(name.clone(), ty.clone())
        } else {
            self.globals.declare(name.clone(), ty.clone())
        };
        self.e.declare(
            &mut self.cir_ctx,
            ty,
            ssa_name.to_string(),
            if input { Some(name) } else { None },
        );
    }

    /// Lookup this name in the current fn/lexical scopes.
    /// Returns `None` if it's in the global scope.
    /// Returns `Some` if it's in a local scope.
    /// Panics if the name cannot be found.
    fn mk_abs(&self, name: &VarName) -> Option<ScopeIdx> {
        if let Some(fn_) = self.fn_stack.last() {
            for (lex_i, e) in fn_.stack.iter().enumerate().rev() {
                match e {
                    StateEntry::Lex(l) => {
                        if l.has_name(name) {
                            return Some(ScopeIdx {
                                lex: lex_i,
                                fn_: self.fn_stack.len() - 1,
                            });
                        }
                    }
                    _ => {}
                }
            }
        };
        if self.globals.has_name(name) {
            None
        } else {
            panic!("No name: {}", name)
        }
    }

    /// Gets the indicated scope.
    /// A `None` scope is the global one.
    fn get_scope_mut(&mut self, idx: Option<ScopeIdx>) -> &mut LexScope<E::Ty> {
        match idx {
            None => &mut self.globals,
            Some(ScopeIdx { lex, fn_ }) => {
                if let StateEntry::Lex(e) = &mut self.fn_stack[fn_].stack[lex] {
                    e
                } else {
                    unreachable!()
                }
            }
        }
    }

    /// Gets the indicated scope.
    /// A `None` scope is the global one.
    fn get_scope_ref(&self, idx: Option<ScopeIdx>) -> &LexScope<E::Ty> {
        match idx {
            None => &self.globals,
            Some(ScopeIdx { lex, fn_ }) => {
                if let StateEntry::Lex(e) = &self.fn_stack[fn_].stack[lex] {
                    e
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn get_lex_mut(&mut self, loc: &Loc) -> &mut LexScope<E::Ty> {
        let idx = loc.idx.clone().or_else(|| self.mk_abs(&loc.name));
        self.get_scope_mut(idx)
    }

    fn get_lex_ref(&self, loc: &Loc) -> &LexScope<E::Ty> {
        let idx = loc.idx.clone().or_else(|| self.mk_abs(&loc.name));
        self.get_scope_ref(idx)
    }

    pub fn assign(&mut self, loc: Loc, val: Val<E::T>) -> Val<E::T> {
        let lex = self.get_lex_mut(&loc);
        let old_name = lex.get_name(&loc.name).clone();
        let ty = lex.get_ty(&loc.name).clone();
        let new_name = lex.next_ver(&loc.name).clone();
        let old_val = self.vals.get(&old_name).unwrap();
        match (old_val, val) {
            (Val::Term(old), Val::Term(new)) => {
                let guard = self.condition();
                let ite_val = self.e.ite(&mut self.cir_ctx, guard, (*old).clone(), new);
                let new_val = Val::Term(self.e.assign(&mut self.cir_ctx, ty, &new_name, ite_val));
                assert!(self.vals.insert(new_name, new_val.clone()).is_none());
                new_val
            }
            (_, v @ Val::Ref(_)) => {
                // TODO: think about this more...
                self.vals.insert(new_name, v.clone());
                v
            }
            (_, v) => panic!(
                "Cannot assign {} to a location {:?}, with a {}",
                v, loc, old_val
            ),
        }
    }

    pub fn enter_breakable(&mut self, name: String) {
        self.fn_stack
            .last_mut()
            .expect("No fn")
            .enter_breakable(name);
    }

    #[track_caller]
    pub fn exit_breakable(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_breakable();
    }

    pub fn break_(&mut self, name: &str) {
        self.fn_stack.last_mut().expect("No fn").break_(name);
    }

    pub fn enter_scope(&mut self) {
        self.fn_stack.last_mut().expect("No fn").enter_scope()
    }

    #[track_caller]
    pub fn exit_scope(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_scope()
    }

    pub fn enter_condition(&mut self, condition: Term) {
        assert!(check(&condition) == Sort::Bool);
        self.fn_stack
            .last_mut()
            .expect("No fn")
            .enter_condition(condition);
        self.condition = self.condition();
    }

    #[track_caller]
    pub fn exit_codition(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_condition();
        self.condition = self.condition();
    }

    pub fn condition(&self) -> Term {
        // TODO:  more precise conditions, depending on lex scopes.
        let cs: Vec<_> = self.fn_stack.iter().flat_map(|f| f.conditions()).collect();
        if cs.len() == 0 {
            leaf_term(Op::Const(Value::Bool(true)))
        } else {
            term(Op::BoolNaryOp(BoolNaryOp::And), cs)
        }
    }

    pub fn enter_fn(&mut self, name: String, ret_ty: Option<E::Ty>) {
        let prefix = format!("{}_f{}", name, self.fn_ctr);
        self.fn_ctr += 1;
        self.fn_stack.push(FnFrame::new(prefix, ret_ty.is_some()));
        if let Some(ty) = ret_ty {
            self.declare(RET_NAME.to_owned(), ty, false);
        }
    }

    pub fn return_(&mut self, val: E::T) {
        self.assign(
            Loc {
                name: RET_NAME.to_owned(),
                idx: None,
            },
            Val::Term(val),
        );
        self.break_(RET_BREAK_NAME);
    }

    pub fn exit_fn(&mut self) -> Option<Val<E::T>> {
        if let Some(fn_) = self.fn_stack.last() {
            let ret = if fn_.has_return {
                Some(self.get_value(Loc::local(RET_NAME.to_owned())))
            } else {
                None
            };
            self.fn_stack.pop().unwrap();
            ret
        } else {
            panic!("No fn to exit")
        }
    }

    pub fn get_value(&self, loc: Loc) -> Val<E::T> {
        let l = self.get_lex_ref(&loc);
        self.vals.get(l.get_name(&loc.name)).unwrap().clone()
    }
}

const RET_NAME: &str = "return";
const RET_BREAK_NAME: &str = "return";
