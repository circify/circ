//! A library for building front-ends
use crate::circify::mem::AllocId;
use crate::ir::term::*;

use std::cell::RefCell;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::fmt::{self, Debug, Display, Formatter};
use std::rc::Rc;
use thiserror::Error;

pub mod includer;
pub mod mem;

type Version = usize;

type VarName = String;

type SsaName = String;

/// A *value*. Can be a term, or a reference.
#[derive(Clone, Debug)]
pub enum Val<T> {
    /// A language term
    Term(T),
    /// A location reference
    Ref(Loc),
}

#[derive(Error, Debug)]
/// An error in circuit translation
pub enum CircError {
    #[error("Location '{0}' is invalid")]
    /// Invalid location
    InvalidLoc(Loc),
    #[error("Identifier '{0}' cannot be found")]
    /// Unknown identifier
    NoName(VarName),
    #[error("No lexical scope in fn '{0}'")]
    /// The requested operation can only be performed inside a scope
    NoScope(String),
    #[error("Identifier '{0}' already declared as a '{1}'")]
    /// Attempted rebinding
    Rebind(String, String),
    #[error("Term '{0}' is not a boolean, as conditionals must be.")]
    /// Boolean required
    NotBool(Term),
    #[error("The break label '{0}' is unknown.")]
    /// The requested operation can only be performed inside a breakable block
    UnknownBreak(String),
    #[error("Cannot assign '{0}' to location '{1}', which held '{2}'")]
    /// Type error
    MisTypedAssign(String, String, String),
    #[error("Function '{0}' has a return value: {1}. Return stmt has a value: {2}'")]
    /// Statement and function don't agree about return value presence.
    ReturnMismatch(String, bool, bool),
}

/// A `T` or a [CircError].
pub type Result<T> = std::result::Result<T, CircError>;

impl<T: Display> Display for Val<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Val::Term(t) => write!(f, "{t}"),
            Val::Ref(l) => write!(f, "&{l}"),
        }
    }
}

impl<T> Val<T> {
    /// Unwrap as a language term, panicking otherwise
    pub fn unwrap_term(self) -> T {
        match self {
            Val::Term(t) => t,
            Val::Ref(l) => panic!("{:?} is not a term", l),
        }
    }
}

/// A *location*. Can be a name in the current scope, or a reference to an alternate scope.
#[derive(Debug, Clone)]
pub struct Loc {
    name: VarName,
    /// Optional (fn, lex) scope indices
    /// The outer option indicates whether this is a local or absolute location.
    /// The inner indicates whether this is a global variable.
    idx: Option<Option<ScopeIdx>>,
}

impl Loc {
    /// The location of a local variable.
    pub fn local(name: VarName) -> Self {
        Self { name, idx: None }
    }
}

impl Display for Loc {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match &self.idx {
            Some(_) => write!(f, "*{}", self.name),
            None => write!(f, "{}", self.name),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ScopeIdx {
    fn_: usize,
    lex: usize,
}

#[derive(Hash, PartialEq, Eq)]
struct VerVar {
    name: VarName,
    ver: Version,
}

#[derive(Debug)]
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

#[derive(Debug)]
struct LexScope<Ty> {
    entries: HashMap<VarName, LexEntry<Ty>>,
    prefix: String,
}

impl<Ty: Display> LexScope<Ty> {
    fn with_prefix(prefix: String) -> Self {
        Self {
            prefix,
            entries: HashMap::default(),
        }
    }
    fn declare(&mut self, name: VarName, ty: Ty) -> Result<&SsaName> {
        let p = &self.prefix;
        match self.entries.entry(name.clone()) {
            Entry::Vacant(v) => Ok(&v.insert(LexEntry::new(format!("{p}_{name}"), ty)).ssa_name),
            Entry::Occupied(o) => Err(CircError::Rebind(name, format!("{}", o.get().ty))),
        }
    }
    fn get_name(&self, name: &str) -> Result<&SsaName> {
        Ok(&self
            .entries
            .get(name)
            .ok_or_else(|| CircError::NoName(name.to_owned()))?
            .ssa_name)
    }
    fn get_ty(&self, name: &str) -> Result<&Ty> {
        Ok(&self
            .entries
            .get(name)
            .ok_or_else(|| CircError::NoName(name.to_owned()))?
            .ty)
    }
    fn next_ver(&mut self, name: &str) -> Result<&SsaName> {
        let e = self
            .entries
            .get_mut(name)
            .ok_or_else(|| CircError::NoName(name.to_owned()))?;
        e.next_ver();
        Ok(&e.ssa_name)
    }
    fn has_name(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }
}

/// Circuit construction context. Useful for addition assertions, using memory, etc.
pub struct CirCtx {
    /// Memory manager
    pub mem: Rc<RefCell<mem::MemManager>>,
    /// Underlying constraint system
    pub cs: Rc<RefCell<Computation>>,
}

#[derive(Debug)]
enum StateEntry<Ty> {
    Lex(LexScope<Ty>),
    Cond(Term),
    /// A block `name`, which has been broken out of if any condition is satisfied.
    Break(String, Vec<Term>),
}

#[derive(Debug)]
struct FnFrame<Ty> {
    stack: Vec<StateEntry<Ty>>,
    scope_ctr: usize,
    prefix: String,
    name: String,
    has_return: bool,
}

impl<Ty: Display> FnFrame<Ty> {
    fn new(name: String, prefix: String, has_return: bool) -> Self {
        let mut this = Self {
            stack: Vec::new(),
            scope_ctr: 0,
            prefix,
            name,
            has_return,
        };
        this.enter_scope();
        this.enter_breakable(RET_BREAK_NAME.to_owned());
        this
    }
    fn last_lex_mut(&mut self) -> Result<&mut LexScope<Ty>> {
        if let Some(n) = self.stack.iter_mut().rev().find_map(|f| match f {
            StateEntry::Lex(l) => Some(l),
            _ => None,
        }) {
            Ok(n)
        } else {
            Err(CircError::NoScope(self.name.clone()))
        }
    }
    pub fn declare(&mut self, name: VarName, ty: Ty) -> Result<&SsaName> {
        self.last_lex_mut()?.declare(name, ty)
    }
    pub fn enter_scope(&mut self) {
        self.stack
            .push(StateEntry::Lex(LexScope::with_prefix(format!(
                "{}_lex{}",
                self.prefix, self.scope_ctr
            ))));
        self.scope_ctr += 1;
    }
    #[track_caller]
    pub fn exit_scope(&mut self) {
        if let Some(StateEntry::Lex(_)) = self.stack.pop() {
        } else {
            panic!("Stack does not end with a scope");
        }
    }
    fn enter_condition(&mut self, condition: Term) -> Result<()> {
        if check(&condition) == Sort::Bool {
            self.stack.push(StateEntry::Cond(condition));
            Ok(())
        } else {
            Err(CircError::NotBool(condition))
        }
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

    fn break_(&mut self, name: &str) -> Result<()> {
        // Walk back to the breakable block, accumulating conditions...
        let mut break_if = Vec::new();
        for s in self.stack.iter_mut().rev() {
            match s {
                StateEntry::Cond(c) => break_if.push(c.clone()),
                StateEntry::Break(name_, ref mut break_conds) => {
                    if name_ == name {
                        break_conds.push(if break_if.is_empty() {
                            leaf_term(Op::Const(Value::Bool(true)))
                        } else {
                            term(Op::BoolNaryOp(BoolNaryOp::And), break_if)
                        });
                        return Ok(());
                    } else {
                        break_if.extend(break_conds.iter().map(|c| term![Op::Not; c.clone()]));
                    }
                }
                _ => {}
            }
        }
        Err(CircError::UnknownBreak(name.to_owned()))
    }
}

/// Trait for *values* that have *types*. `Self` is the value-type. `T` is the type-type.
pub trait Typed<T> {
    /// Compute the type of this value.
    fn type_(&self) -> T;
}

/// A language whose state can be managed
pub trait Embeddable {
    /// Type for this language
    type Ty: Display + Clone + Debug + PartialEq + Eq;
    /// Terms for this language
    type T: Display + Clone + Debug + Typed<Self::Ty>;

    /// Declare a language-level *input* to the computation.
    ///
    /// ## Arguments
    ///
    ///    * `ctx`: circuit context: you must add the circuit-level *input*
    ///    * `ty`: the type
    ///    * `name`: the name
    ///    * `visibility`: who knows it
    ///    * `precompute`: an optional term for pre-computing the values of this input. If a party
    ///    knows the inputs to the precomputation, they can use the precomputation.
    fn declare_input(
        &self,
        ctx: &mut CirCtx,
        ty: &Self::Ty,
        name: String,
        visibility: Option<PartyId>,
        precompute: Option<Self::T>,
    ) -> Self::T;

    /// Create a new uninitialized value of the given term in your language.
    ///
    /// For most languages, this should just be a kind of default value.
    ///
    /// ## Arguments
    ///
    ///    * `ctx`: circuit context: you must add the circuit-level *input*
    ///    * `ty`: the type
    fn create_uninit(&self, ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T;

    /// Construct an it-then-else (ternary) langauge value.
    ///
    /// Conceptually, `(ite cond t f)`
    fn ite(&self, ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T;

    /// Create a new term for the default return value of a function returning type `ty`.
    /// The name `ssa_name` is globally unique, and can be used if needed.
    // Because the type alias may change.
    #[allow(clippy::ptr_arg)]
    fn initialize_return(&self, ty: &Self::Ty, ssa_name: &SsaName) -> Self::T;

    /// Wrap an IR field->field array as a language-level persistent array.
    fn wrap_persistent_array(&self, _t: Term) -> Self::T {
        unimplemented!("wrap_persistent_array")
    }
}

/// Manager for circuit-embedded state.
pub struct Circify<E: Embeddable> {
    /// The reference to the FE embedding machinery
    e: E,
    vals: HashMap<SsaName, Val<E::T>>,
    fn_stack: Vec<FnFrame<E::Ty>>,
    fn_ctr: usize,
    globals: LexScope<E::Ty>,
    cir_ctx: CirCtx,
    condition: Term,
    typedefs: HashMap<String, E::Ty>,
}

impl<E: Embeddable> Debug for Circify<E> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("Circify")
            .field("vals", &self.vals)
            .field("fn_stack", &self.fn_stack)
            .field("globals", &self.globals)
            .field("cir_ctx", &"*omitted*")
            .field("condition", &self.condition)
            .field("typedefs", &self.typedefs)
            .finish()
    }
}

impl<E: Embeddable> Drop for Circify<E> {
    fn drop(&mut self) {
        // drop all fields that contain T or Ty
        self.vals.clear();
        self.fn_stack.clear();
        self.globals.entries.clear();
        self.typedefs.clear();

        // we don't bother dropping cir_ctx before garbage collecting.
        // If we're dropping Circify after calling consume(), then
        // we'd just be dropping a dummy. Otherwise, we're dropping
        // a live CirCtx, in which case the Computation's Drop impl
        // will garbage collect.
        //
        //drop(self.take_ctx());

        // force garbage collection
        garbage_collect();
    }
}

impl<E: Embeddable> Circify<E> {
    /// Creates an empty state management module
    pub fn new(e: E) -> Self {
        let cs = Rc::new(RefCell::new(Computation::new()));
        Self {
            e,
            vals: HashMap::default(),
            fn_stack: Vec::new(),
            fn_ctr: 0,
            globals: LexScope::with_prefix("global".to_string()),
            cir_ctx: CirCtx {
                mem: Rc::new(RefCell::new(mem::MemManager::default())),
                cs,
            },
            condition: leaf_term(Op::Const(Value::Bool(true))),
            typedefs: HashMap::default(),
        }
    }

    /// Get the circuit generation context
    pub fn cir_ctx(&self) -> &CirCtx {
        &self.cir_ctx
    }

    /// Initialize environment entry binding `name` to `ty`.
    fn declare_env_name(&mut self, name: VarName, ty: &E::Ty) -> Result<&SsaName> {
        if let Some(back) = self.fn_stack.last_mut() {
            back.declare(name, ty.clone())
        } else {
            self.globals.declare(name, ty.clone())
        }
    }

    /// Declare a new *input* to the computation.
    ///
    /// See [Embeddable::declare_input]
    ///
    /// ## Arguments
    /// * nice_name: the in-program name of the input
    /// * ty: the type
    /// * visibility: who should know this input
    /// * mangle_name: if true, then creates a unique version of nice_name, and declares that. Otherwise, uses nice_name.
    pub fn declare_input(
        &mut self,
        nice_name: VarName,
        ty: &E::Ty,
        visibility: Option<PartyId>,
        precomputed_value: Option<E::T>,
        mangle_name: bool,
    ) -> Result<E::T> {
        let ssa_name = self.declare_env_name(nice_name.clone(), ty)?.clone();
        let name = if mangle_name {
            ssa_name.clone()
        } else {
            nice_name
        };
        let t = self
            .e
            .declare_input(&mut self.cir_ctx, ty, name, visibility, precomputed_value);
        assert!(self.vals.insert(ssa_name, Val::Term(t.clone())).is_none());
        Ok(t)
    }

    /// Declares a new (uninitialized) value of type `ty`, with name `name`, in the current lexical
    /// scope.
    pub fn declare_uninit(&mut self, name: VarName, ty: &E::Ty) -> Result<()> {
        let ssa_name = self.declare_env_name(name, ty)?.clone();
        let t = self.e.create_uninit(&mut self.cir_ctx, ty);
        assert!(self.vals.insert(ssa_name, Val::Term(t)).is_none());
        Ok(())
    }

    /// Lookup this name in the current fn/lexical scopes.
    /// Returns `None` if it's in the global scope.
    /// Returns `Some` if it's in a local scope.
    /// Errors if the name cannot be found.
    // Because the type alias may change.
    #[allow(clippy::ptr_arg)]
    fn mk_abs(&self, name: &VarName) -> Result<Option<ScopeIdx>> {
        if let Some(fn_) = self.fn_stack.last() {
            for (lex_i, e) in fn_.stack.iter().enumerate().rev() {
                if let StateEntry::Lex(l) = e {
                    if l.has_name(name) {
                        return Ok(Some(ScopeIdx {
                            lex: lex_i,
                            fn_: self.fn_stack.len() - 1,
                        }));
                    }
                }
            }
        }
        if self.globals.has_name(name) {
            Ok(None)
        } else {
            Err(CircError::NoName(name.clone()))
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

    fn get_lex_mut(&mut self, loc: &Loc) -> Result<&mut LexScope<E::Ty>> {
        let idx = loc.idx.ok_or(()).or_else(|_| self.mk_abs(&loc.name))?;
        Ok(self.get_scope_mut(idx))
    }

    fn get_lex_ref(&self, loc: &Loc) -> Result<&LexScope<E::Ty>> {
        let idx = loc.idx.ok_or(()).or_else(|_| self.mk_abs(&loc.name))?;
        Ok(self.get_scope_ref(idx))
    }

    /// Declare `name` in the current scope as being a `ty`, and being equal to `val`.
    ///
    /// If `public`, then make it a public (fixed) rather than private (existential) circuit input.
    pub fn declare_init(&mut self, name: VarName, ty: E::Ty, val: Val<E::T>) -> Result<Val<E::T>> {
        let ssa_name = self.declare_env_name(name, &ty)?.clone();
        // TODO: add language-specific coersion here if needed
        assert!(self.vals.insert(ssa_name, val.clone()).is_none());
        Ok(val)
    }

    /// Assign `loc` in the current scope to `val`.
    ///
    /// If `public`, then make the new variable version a public (fixed) rather than private
    /// (existential) circuit input.
    pub fn assign(&mut self, loc: Loc, val: Val<E::T>) -> Result<Val<E::T>> {
        // Find the lexical scope that this location is in.
        let lex = self.get_lex_mut(&loc)?;
        // Get the old SSA name
        let old_name = lex.get_name(&loc.name)?.clone();
        // Get the type
        let ty = lex.get_ty(&loc.name)?.clone();
        // Get a new SSA name
        let new_name = lex.next_ver(&loc.name)?.clone();
        // Done w/ lexical scope
        // Grab old term
        let old_val = self.vals.get(&old_name).unwrap();
        match (old_val, val) {
            (Val::Term(old), Val::Term(new)) => {
                let new_ty = new.type_();
                assert_eq!(
                    ty, new_ty,
                    "{}",
                    "Term {new} has type {new_ty} but was assigned to {loc} of type {ty}",
                );
                // get condition under which assignment happens
                let guard = self.condition.clone();
                // build condition-aware new value
                let ite = match guard.as_bool_opt() {
                    Some(true) => new,
                    Some(false) => old.clone(),
                    None => self.e.ite(&mut self.cir_ctx, guard, new, (*old).clone()),
                };
                let ite_val = Val::Term(ite);
                // TODO: add language-specific coersion here if needed
                assert!(self.vals.insert(new_name, ite_val.clone()).is_none());
                Ok(ite_val)
            }
            (_, v @ Val::Ref(_)) => {
                // TODO: think about this more...
                self.vals.insert(new_name, v.clone());
                Ok(v)
            }
            (_, v) => Err(CircError::MisTypedAssign(
                format!("{v}"),
                format!("{loc}"),
                format!("{old_val}"),
            )),
        }
    }

    /// Enter a breakable block, called `name`.
    ///
    /// This is a block of code that can be skipped to the end of.
    pub fn enter_breakable(&mut self, name: String) {
        self.fn_stack
            .last_mut()
            .expect("No fn")
            .enter_breakable(name);
    }

    #[track_caller]
    /// End a breakable block
    pub fn exit_breakable(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_breakable();
    }

    #[track_caller]
    /// Emit a break statement for the breakable block, `name`.
    pub fn break_(&mut self, name: &str) -> Result<()> {
        self.fn_stack.last_mut().expect("No fn").break_(name)
    }

    #[track_caller]
    /// Enter a lexical scope
    pub fn enter_scope(&mut self) {
        self.fn_stack.last_mut().expect("No fn").enter_scope()
    }

    #[track_caller]
    /// Exit a lexical scope
    pub fn exit_scope(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_scope()
    }

    /// Enter a conditional block
    pub fn enter_condition(&mut self, condition: Term) -> Result<()> {
        assert!(check(&condition) == Sort::Bool);
        self.fn_stack
            .last_mut()
            .expect("No fn")
            .enter_condition(condition)?;
        self.condition = self.condition();
        Ok(())
    }

    /// Exit a conditional block
    pub fn exit_condition(&mut self) {
        self.fn_stack.last_mut().expect("No fn").exit_condition();
        self.condition = self.condition();
    }

    /// Get the current path condition
    pub fn condition(&self) -> Term {
        // TODO:  more precise conditions, depending on lex scopes.
        let cs: Vec<_> = self.fn_stack.iter().flat_map(|f| f.conditions()).collect();
        if cs.is_empty() {
            leaf_term(Op::Const(Value::Bool(true)))
        } else {
            term(Op::BoolNaryOp(BoolNaryOp::And), cs)
        }
    }

    /// Enter a function, `name`, with return type `ret_ty`.
    pub fn enter_fn(&mut self, name: String, ret_ty: Option<E::Ty>) {
        let prefix = format!("{}_f{}", name, self.fn_ctr);
        self.fn_ctr += 1;
        self.fn_stack
            .push(FnFrame::new(name, prefix, ret_ty.is_some()));
        if let Some(ty) = ret_ty {
            let ssa_name = self
                .declare_env_name(RET_NAME.to_owned(), &ty)
                .unwrap()
                .clone();
            let default_ret_val = self.e.initialize_return(&ty, &ssa_name);
            assert!(self
                .vals
                .insert(ssa_name, Val::Term(default_ret_val))
                .is_none());
        }
    }

    /// Return (subject to the current path condition).
    pub fn return_(&mut self, val: Option<E::T>) -> Result<()> {
        let last = self.fn_stack.last().expect("No fn");
        if val.is_some() != last.has_return {
            return Err(CircError::ReturnMismatch(
                last.name.clone(),
                last.has_return,
                val.is_some(),
            ));
        }
        if let Some(r) = val {
            self.assign(
                Loc {
                    name: RET_NAME.to_owned(),
                    idx: None,
                },
                Val::Term(r),
            )?;
        }
        self.break_(RET_BREAK_NAME)
    }

    /// Assert something
    pub fn assert(&mut self, t: Term) {
        self.cir_ctx.cs.borrow_mut().assert(t);
    }

    #[track_caller]
    /// Exit a function call.
    ///
    /// ## Returns
    ///
    /// Returns the return value of the function, if any.
    pub fn exit_fn(&mut self) -> Option<Val<E::T>> {
        if let Some(fn_) = self.fn_stack.last() {
            let ret = if fn_.has_return {
                Some(self.get_value(Loc::local(RET_NAME.to_owned())).unwrap())
            } else {
                None
            };
            self.fn_stack.pop().unwrap();
            ret
        } else {
            panic!("No fn to exit")
        }
    }

    /// Exit a function call.
    ///
    /// ## Returns
    ///
    /// Returns the return value of the function, if any.
    pub fn exit_fn_call(&mut self, ret_names: &Vec<String>) -> Option<Vec<Val<E::T>>> {
        if let Some(fn_) = self.fn_stack.last() {
            let mut rets: Vec<Val<E::T>> = Vec::new();
            // Get return value if possible
            if fn_.has_return {
                rets.push(self.get_value(Loc::local(RET_NAME.to_owned())).unwrap());
            }

            // Get references if possible
            for name in ret_names {
                rets.push(self.get_value(Loc::local(name.to_string())).unwrap());
            }

            self.fn_stack.pop().unwrap();
            Some(rets)
        } else {
            panic!("No fn to exit")
        }
    }

    /// Get the current value of a location
    pub fn get_value(&self, loc: Loc) -> Result<Val<E::T>> {
        let l = self.get_lex_ref(&loc)?;
        self.vals
            .get(l.get_name(&loc.name)?)
            .cloned()
            .ok_or(CircError::InvalidLoc(loc))
    }

    /// Dereference a reference into a location.
    ///
    /// Panics if not a reference.
    pub fn deref(&self, v: &Val<E::T>) -> Loc {
        match v {
            Val::Ref(l) => l.clone(),
            Val::Term(_) => panic!("{} is not dereferencable", v),
        }
    }

    /// Create a reference to a variable.
    // Because the type alias may change.
    #[allow(clippy::ptr_arg)]
    pub fn ref_(&self, name: &VarName) -> Result<Val<E::T>> {
        let idx = self.mk_abs(name)?;
        Ok(Val::Ref(Loc {
            name: name.to_owned(),
            idx: Some(idx),
        }))
    }

    /// Define a new type
    pub fn def_type(&mut self, name: &str, ty: E::Ty) {
        if let Some(old_ty) = self.typedefs.insert(name.to_owned(), ty) {
            panic!("{} already defined as {}", name, old_ty)
        }
    }

    /// Get a defined type
    pub fn get_type(&mut self, name: &str) -> &E::Ty {
        self.typedefs
            .get(name)
            .unwrap_or_else(|| panic!("No type {}", name))
    }

    /// Get the constraints from this manager
    pub fn consume(mut self) -> Rc<RefCell<Computation>> {
        std::mem::replace(
            &mut self.cir_ctx,
            CirCtx {
                mem: Rc::new(RefCell::new(mem::MemManager::default())),
                cs: Rc::new(RefCell::new(Computation::new())),
            },
        )
        .cs
    }

    /// Load from an AllocId
    pub fn load(&self, id: AllocId, offset: Term) -> Term {
        self.cir_ctx.mem.borrow_mut().load(id, offset)
    }

    /// Conditional store to an AllocId based on an explicit condition
    pub fn cond_store(&mut self, id: AllocId, offset: Term, val: Term, cond: Term) {
        self.cir_ctx.mem.borrow_mut().store(id, offset, val, cond);
    }

    /// Conditional store to an AllocId based on current path condition
    pub fn store(&mut self, id: AllocId, offset: Term, val: Term) {
        let cond = self.condition();
        self.cir_ctx.mem.borrow_mut().store(id, offset, val, cond);
    }

    /// Replace term at AllocId
    pub fn replace(&mut self, id: AllocId, val: Term) {
        self.cir_ctx.mem.borrow_mut().replace(id, val);
    }

    /// Zero allocate an array
    pub fn zero_allocate(&mut self, size: usize, addr_width: usize, val_width: usize) -> AllocId {
        self.cir_ctx
            .mem
            .borrow_mut()
            .zero_allocate(size, addr_width, val_width)
    }

    /// Create a new persistent array.
    pub fn start_persistent_array(
        &mut self,
        var: &str,
        size: usize,
        field: circ_fields::FieldT,
        party: PartyId,
    ) -> E::T {
        let ir = self
            .cir_ctx
            .cs
            .borrow_mut()
            .start_persistent_array(var, size, field, party);
        let t = self.e.wrap_persistent_array(ir);
        let ssa_name = self
            .declare_env_name(var.into(), &t.type_())
            .unwrap()
            .clone();
        assert!(self.vals.insert(ssa_name, Val::Term(t.clone())).is_none());
        t
    }

    /// Record the final state
    pub fn end_persistent_array(&mut self, var: &str, final_state: Term) {
        self.cir_ctx
            .cs
            .borrow_mut()
            .end_persistent_array(var, final_state)
    }
}

const RET_NAME: &str = "return";
const RET_BREAK_NAME: &str = "return";

#[cfg(test)]
mod test {
    use super::*;
    use crate::ir::proof::*;

    #[allow(dead_code)]
    mod bool_pair {
        use super::*;

        #[derive(Clone, Debug)]
        enum T {
            Base(Term),
            Pair(Box<T>, Box<T>),
        }

        impl Display for T {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    T::Base(t) => write!(f, "{t}"),
                    T::Pair(a, b) => write!(f, "({a}, {b})"),
                }
            }
        }

        #[derive(Clone, Debug, PartialEq, Eq)]
        enum Ty {
            Bool,
            Pair(Box<Ty>, Box<Ty>),
        }

        impl Display for Ty {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                match self {
                    Ty::Bool => write!(f, "bool"),
                    Ty::Pair(a, b) => write!(f, "({a}, {b})"),
                }
            }
        }

        impl Ty {
            fn default(&self) -> T {
                match self {
                    Ty::Bool => T::Base(leaf_term(Op::Const(Value::Bool(false)))),
                    Ty::Pair(a, b) => T::Pair(Box::new(a.default()), Box::new(b.default())),
                }
            }
        }

        #[derive(Clone)]
        enum Val {
            Base(bool),
            Pair(Box<T>, Box<T>),
        }

        struct BoolPair();

        impl Embeddable for BoolPair {
            type T = T;
            type Ty = Ty;

            fn create_uninit(&self, _ctx: &mut CirCtx, ty: &Self::Ty) -> Self::T {
                ty.default()
            }

            fn ite(&self, _ctx: &mut CirCtx, cond: Term, t: Self::T, f: Self::T) -> Self::T {
                match (t, f) {
                    (T::Base(a), T::Base(b)) => T::Base(term![Op::Ite; cond, a, b]),
                    (T::Pair(a0, a1), T::Pair(b0, b1)) => T::Pair(
                        Box::new(self.ite(_ctx, cond.clone(), *a0, *b0)),
                        Box::new(self.ite(_ctx, cond, *a1, *b1)),
                    ),
                    (a, b) => panic!("Cannot ITE {}, {}", a, b),
                }
            }

            fn initialize_return(&self, ty: &Self::Ty, _ssa_name: &SsaName) -> Self::T {
                ty.default()
            }

            fn declare_input(
                &self,
                ctx: &mut CirCtx,
                ty: &Self::Ty,
                name: String,
                visibility: Option<PartyId>,
                precompute: Option<Self::T>,
            ) -> Self::T {
                match ty {
                    Ty::Bool => T::Base(ctx.cs.borrow_mut().new_var(
                        &name,
                        Sort::Bool,
                        visibility,
                        precompute.map(|p| match p {
                            T::Base(t) => t,
                            _ => panic!("Invalid precompute {:?} for Bool type", p),
                        }),
                    )),
                    Ty::Pair(a, b) => {
                        let (p_1, p_2) = match precompute {
                            Some(T::Pair(a, b)) => (Some(*a), Some(*b)),
                            None => (None, None),
                            _ => panic!("Invalid precompute {:?} for Pair type", precompute),
                        };
                        T::Pair(
                            Box::new(self.declare_input(
                                ctx,
                                a,
                                format!("{name}.0"),
                                visibility,
                                p_1,
                            )),
                            Box::new(self.declare_input(
                                ctx,
                                b,
                                format!("{name}.1"),
                                visibility,
                                p_2,
                            )),
                        )
                    }
                }
            }
        }

        impl Typed<Ty> for T {
            fn type_(&self) -> Ty {
                match self {
                    T::Base(_a) => Ty::Bool,
                    T::Pair(a, b) => Ty::Pair(Box::new(a.type_()), Box::new(b.type_())),
                }
            }
        }

        #[test]
        fn trial() {
            let e = BoolPair();
            let mut c = Circify::new(e);
            c.cir_ctx.cs.borrow_mut().metadata.add_prover_and_verifier();
            c.declare_input("a".to_owned(), &Ty::Bool, Some(PROVER_ID), None, false)
                .unwrap();
            c.declare_input(
                "b".to_owned(),
                &Ty::Pair(Box::new(Ty::Bool), Box::new(Ty::Bool)),
                Some(PROVER_ID),
                None,
                false,
            )
            .unwrap();
        }
    }
}
