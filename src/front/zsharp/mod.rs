//! The ZoKrates/Z# front-end

mod parser;
mod term;
pub mod zvisit;

use super::FrontEnd;
use crate::circify::{CircError, Circify, Loc, Val};
use crate::ir::proof::{self, ConstraintMetadata};
use crate::ir::term::extras::Letified;
use crate::ir::term::*;
use log::{debug, warn};
use rug::Integer;
use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::{self, Display, Formatter};
use std::path::{Path, PathBuf};
use std::str::FromStr;
use zokrates_pest_ast as ast;

use term::*;
use zvisit::{ZConstLiteralRewriter, ZGenericInf, ZStatementWalker, ZVisitorMut};

/// The modulus for the ZSharp language
pub use term::ZSHARP_MODULUS;
/// The modulus for the ZSharp language (ARC)
pub use term::ZSHARP_MODULUS_ARC;
/// The modulus for the Z# language as a Sort
pub use term::ZSHARP_FIELD_SORT;

/// The prover visibility
pub const PROVER_VIS: Option<PartyId> = Some(proof::PROVER_ID);
/// Public visibility
pub const PUBLIC_VIS: Option<PartyId> = None;

/// Inputs to the Z# compilier
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
    /// The file to look for concrete arguments to main in. Optional.
    ///
    /// ## Examples
    ///
    /// If main takes `x: u64, y: field`, this file might contain
    ///
    /// ```ignore
    /// x 4
    /// y -1
    /// ```
    pub inputs: Option<PathBuf>,
    /// The mode to generate for (MPC or proof). Effects visibility.
    pub mode: Mode,
}

#[derive(Clone, Copy, Debug)]
/// Kind of circuit to generate. Effects privacy labels.
pub enum Mode {
    /// Generating an MPC circuit. Inputs are public or private (to a party in 1..N).
    Mpc(u8),
    /// Generating for a proof circuit. Inputs are public of private (to the prover).
    Proof,
    /// Generating for an optimization circuit. Inputs are existentially quantified.
    /// There should be only one output, which will be maximized.
    Opt,
    /// Find inputs that yeild an output at least this large,
    /// and then prove knowledge of them.
    ProofOfHighValue(u64),
}

impl Display for Mode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            &Mode::Mpc(n) => write!(f, "{}-pc", n),
            &Mode::Proof => write!(f, "proof"),
            &Mode::Opt => write!(f, "opt"),
            &Mode::ProofOfHighValue(v) => write!(f, "proof_of_high_value({})", v),
        }
    }
}

/// The Z# front-end. Implements [FrontEnd].
pub struct ZSharpFE;

impl FrontEnd for ZSharpFE {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let loader = parser::ZLoad::new();
        let asts = loader.load(&i.file);
        let mut g = ZGen::new(i.inputs, asts, i.mode, loader.stdlib());
        g.visit_files();
        g.file_stack_push(i.file);
        g.generics_stack_push(HashMap::new());
        g.entry_fn("main");
        g.generics_stack_pop();
        g.file_stack_pop();
        g.circ.into_inner().consume().borrow().clone()
    }
}

impl ZSharpFE {
    /// Execute the Z# front-end interpreter on the supplied file with the supplied inputs
    pub fn interpret(i: Inputs) -> T {
        i.inputs.as_ref().map(|_| panic!("zsharp::interpret() requires main() to take no args"));

        let loader = parser::ZLoad::new();
        let asts = loader.load(&i.file);
        let mut g = ZGen::new(i.inputs, asts, i.mode, loader.stdlib());
        g.visit_files();
        g.file_stack_push(i.file);
        g.generics_stack_push(HashMap::new());
        g.const_entry_fn("main")
    }
}

struct ZGen<'ast> {
    circ: RefCell<Circify<ZSharp>>,
    stdlib: &'ast parser::ZStdLib,
    asts: HashMap<PathBuf, ast::File<'ast>>,
    file_stack: RefCell<Vec<PathBuf>>,
    generics_stack: RefCell<Vec<HashMap<String, T>>>,
    functions: HashMap<PathBuf, HashMap<String, ast::FunctionDefinition<'ast>>>,
    structs: HashMap<PathBuf, HashMap<String, ast::StructDefinition<'ast>>>,
    constants: HashMap<PathBuf, HashMap<String, (ast::Type<'ast>, T)>>,
    import_map: HashMap<PathBuf, HashMap<String, (PathBuf, String)>>,
    mode: Mode,
    cvars_stack: RefCell<Vec<Vec<HashMap<String, T>>>>,
    crets_stack: RefCell<Vec<T>>,
    lhs_ty: RefCell<Option<Ty>>,
    ret_ty_stack: RefCell<Vec<Ty>>,
}

struct ZLoc {
    var: Loc,
    accesses: Vec<ZAccess>,
}

enum ZAccess {
    Member(String),
    Idx(T),
}

fn loc_store(struct_: T, loc: &[ZAccess], val: T) -> Result<T, String> {
    match loc.first() {
        None => Ok(val),
        Some(ZAccess::Member(field)) => {
            let inner = field_select(&struct_, &field)?;
            let new_inner = loc_store(inner, &loc[1..], val)?;
            field_store(struct_, &field, new_inner)
        }
        Some(ZAccess::Idx(idx)) => {
            let old_inner = array_select(struct_.clone(), idx.clone())?;
            let new_inner = loc_store(old_inner, &loc[1..], val)?;
            array_store(struct_, idx.clone(), new_inner)
        }
    }
}

impl<'ast> ZGen<'ast> {
    fn new(inputs: Option<PathBuf>, asts: HashMap<PathBuf, ast::File<'ast>>, mode: Mode, stdlib: &'ast parser::ZStdLib) -> Self {
        let this = Self {
            circ: RefCell::new(Circify::new(ZSharp::new(inputs.map(|i| parser::parse_inputs(i))))),
            asts,
            stdlib,
            file_stack: Default::default(),
            generics_stack: Default::default(),
            functions: HashMap::new(),
            structs: HashMap::new(),
            constants: HashMap::new(),
            import_map: HashMap::new(),
            mode,
            cvars_stack: Default::default(),
            crets_stack: Default::default(),
            lhs_ty: Default::default(),
            ret_ty_stack: Default::default(),
        };
        this.circ
            .borrow()
            .cir_ctx()
            .cs
            .borrow_mut()
            .metadata
            .add_prover_and_verifier();
        this
    }

    /// Unwrap a result with a span-dependent error
    fn err<E: Display>(&self, e: E, s: &ast::Span) -> ! {
        println!("Error: {}", e);
        println!("In: {}", self.cur_path().display());
        s.lines().for_each(|l| print!("  {}", l));
        std::process::exit(1)
    }

    fn unwrap<T, E: Display>(&self, r: Result<T, E>, s: &ast::Span) -> T {
        r.unwrap_or_else(|e| self.err(e, s))
    }

    fn builtin_call(f_name: &str, mut args: Vec<T>, mut generics: Vec<T>) -> Result<T, String> {
        debug!("Builtin Call: {} {:?} {:?}", f_name, args, generics);
        match f_name {
            "u8_to_bits" | "u16_to_bits" | "u32_to_bits" | "u64_to_bits" => {
                if args.len() != 1 {
                    Err(format!("Got {} args to EMBED/{}, expected 1", args.len(), f_name))
                } else if !generics.is_empty() {
                    Err(format!("Got {} generic args to EMBED/{}, expected 0", generics.len(), f_name))
                } else {
                    uint_to_bits(args.pop().unwrap())
                }
            }
            "u8_from_bits" | "u16_from_bits" | "u32_from_bits" | "u64_from_bits" => {
                if args.len() != 1 {
                    Err(format!("Got {} args to EMBED/{}, expected 1", args.len(), f_name))
                } else if !generics.is_empty() {
                    Err(format!("Got {} generic args to EMBED/{}, expected 0", generics.len(), f_name))
                } else {
                    uint_from_bits(args.pop().unwrap())
                }
            }
            "unpack" => {
                if args.len() != 1 {
                    Err(format!("Got {} args to EMBED/unpack, expected 1", args.len()))
                } else if generics.len() != 1 {
                    Err(format!("Got {} generic args to EMBED/unpack, expected 1", generics.len()))
                } else {
                    let nbits = const_int(generics.pop().unwrap())?
                        .to_usize()
                        .ok_or_else(|| "builtin_call failed to convert unpack's N to usize".to_string())?;
                    field_to_bits(args.pop().unwrap(), nbits)
                }
            }
            "bit_array_le" => {
                if args.len() != 2 {
                    Err(format!("Got {} args to EMBED/bit_array_le, expected 1", args.len()))
                } else if generics.len() != 1 {
                    Err(format!("Got {} generic args to EMBED/bit_array_le, expected 1", generics.len()))
                } else {
                    let nbits = const_int(generics.pop().unwrap())?
                        .to_usize()
                        .ok_or_else(|| "builtin_call failed to convert bit_array_le's N to usize".to_string())?;

                    let second_arg = args.pop().unwrap();
                    let first_arg = args.pop().unwrap();
                    bit_array_le(first_arg, second_arg, nbits)
                }
            }
            "get_field_size" => {
                if args.len() != 0 {
                    Err(format!("Got {} args to EMBED/get_field_size, expected 0", args.len()))
                } else if !generics.is_empty() {
                    Err(format!("Got {} generic args to EMBED/get_field_size, expected 0", generics.len()))
                } else {
                    Ok(uint_lit(ZSHARP_MODULUS.significant_bits(), 32))
                }
            }
            _ => Err(format!("Unknown or unimplemented builtin '{}'", f_name)),
        }
    }

    fn stmt(&self, s: &ast::Statement<'ast>) {
        debug!("Stmt: {}", s.span().as_str());
        match s {
            ast::Statement::Return(r) => {
                // XXX(unimpl) multi-return unimplemented
                assert!(r.expressions.len() <= 1);
                if let Some(e) = r.expressions.first() {
                    self.set_lhs_ty_ret(r);
                    let ret = self.expr(e);
                    let ret_res = self.circ_return_(Some(ret));
                    self.unwrap(ret_res, &r.span);
                } else {
                    let ret_res = self.circ_return_(None);
                    self.unwrap(ret_res, &r.span);
                }
            }
            ast::Statement::Assertion(e) => {
                // handle constant assertions (useful at compile time)
                if let Ok(b) = self.const_expr_(&e.expression).and_then(|b| const_bool_ref(&b)) {
                    if b {
                        return;
                    } else {
                        self.err("const assert failed", &e.span);
                    }
                }
                let b = bool(self.expr(&e.expression));
                let e = self.unwrap(b, &e.span);
                self.circ_assert(e);
            }
            ast::Statement::Iteration(i) => {
                let ty = self.type_(&i.ty);
                // iteration type constructor - must be Field or u*
                let ival_cons = match ty {
                    Ty::Field => T::new_field,
                    Ty::Uint(8) => T::new_u8,
                    Ty::Uint(16) => T::new_u16,
                    Ty::Uint(32) => T::new_u32,
                    Ty::Uint(64) => T::new_u64,
                    _ => self.err("Iteration variable must be Field or Unit", &i.span),
                };

                let s = self.const_int(&i.from);
                let e = self.const_int(&i.to);
                let v_name = i.index.value.clone();
                self.circ_enter_scope();
                let decl_res = self.circ_declare(v_name.clone(), &ty, false, PROVER_VIS);
                self.unwrap(decl_res, &i.index.span);
                for j in s..e {
                    self.circ_enter_scope();
                    let ass_res = self
                        .circ_assign(Loc::local(v_name.clone()), Val::Term(ival_cons(j)));
                    self.unwrap(ass_res, &i.index.span);
                    for s in &i.statements {
                        self.stmt(s);
                    }
                    self.circ_exit_scope();
                }
                self.circ_exit_scope();
            }
            ast::Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                // evaluate expression, possibly extracting lhs type first
                self.set_lhs_ty_defn::<false>(d);
                let e = self.expr(&d.expression);

                if let Some(l) = d.lhs.first() {
                    let ty = e.type_();
                    match l {
                        ast::TypedIdentifierOrAssignee::Assignee(l) => {
                            let lval = self.lval(l);
                            let mod_res = self.mod_lval(lval, e);
                            self.unwrap(mod_res, &d.span);
                        }
                        ast::TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                            let decl_ty = self.type_(&l.ty);
                            if decl_ty != ty {
                                self.err(
                                    format!(
                                        "Assignment type mismatch: {} annotated vs {} actual",
                                        decl_ty, ty,
                                    ),
                                    &d.span,
                                );
                            }
                            let d_res = self.circ_declare_init(
                                l.identifier.value.clone(),
                                decl_ty,
                                Val::Term(e),
                            );
                            self.unwrap(d_res, &d.span);
                        }
                    }
                }
            }
        }
    }

    fn mod_lval(&self, loc: ZLoc, val: T) -> Result<(), String> {
        let old = self
            .circ_get_value(loc.var.clone())
            .map_err(|e| format!("{}", e))?
            .unwrap_term();
        let new = loc_store(old, &loc.accesses, val)?;
        debug!("Assign: {:?} = {}", loc.var, Letified(new.term.clone()));
        self.circ_assign(loc.var, Val::Term(new))
            .map_err(|e| format!("{}", e))
            .map(|_| ())
    }

    fn lval(&self, l: &ast::Assignee<'ast>) -> ZLoc {
        let mut loc = ZLoc {
            var: Loc::local(l.id.value.clone()),
            accesses: vec![],
        };
        for acc in &l.accesses {
            loc.accesses.push(match acc {
                ast::AssigneeAccess::Member(m) => ZAccess::Member(m.id.value.clone()),
                ast::AssigneeAccess::Select(m) => ZAccess::Idx(
                    if let ast::RangeOrExpression::Expression(e) = &m.expression {
                        self.expr(&e)
                    } else {
                        self.err("Cannot assign to slice", &m.span);
                    },
                ),
            })
        }
        loc
    }

    fn literal_(&self, e: &ast::LiteralExpression<'ast>) -> Result<T, String> {
        match e {
            ast::LiteralExpression::DecimalLiteral(d) => {
                let vstr = &d.value.span.as_str();
                match &d.suffix {
                    Some(ast::DecimalSuffix::U8(_)) => {
                        Ok(uint_lit(u8::from_str_radix(vstr, 10).unwrap(), 8))
                    }
                    Some(ast::DecimalSuffix::U16(_)) => {
                        Ok(uint_lit(u16::from_str_radix(vstr, 10).unwrap(), 16))
                    }
                    Some(ast::DecimalSuffix::U32(_)) => {
                        Ok(uint_lit(u32::from_str_radix(vstr, 10).unwrap(), 32))
                    }
                    Some(ast::DecimalSuffix::U64(_)) => {
                        Ok(uint_lit(u64::from_str_radix(vstr, 10).unwrap(), 64))
                    }
                    Some(ast::DecimalSuffix::Field(_)) => {
                        Ok(field_lit(Integer::from_str_radix(vstr, 10).unwrap()))
                    }
                    _ => Err("Could not infer literal type. Annotation needed.".to_string()),
                }
            }
            ast::LiteralExpression::BooleanLiteral(b) => {
                Ok(z_bool_lit(bool::from_str(&b.value).unwrap()))
            }
            ast::LiteralExpression::HexLiteral(h) => match &h.value {
                ast::HexNumberExpression::U8(h) => Ok(
                    uint_lit(u8::from_str_radix(&h.value, 16).unwrap(), 8),
                ),
                ast::HexNumberExpression::U16(h) => Ok(
                    uint_lit(u16::from_str_radix(&h.value, 16).unwrap(), 16),
                ),
                ast::HexNumberExpression::U32(h) => Ok(
                    uint_lit(u32::from_str_radix(&h.value, 16).unwrap(), 32),
                ),
                ast::HexNumberExpression::U64(h) => Ok(
                    uint_lit(u64::from_str_radix(&h.value, 16).unwrap(), 64),
                ),
            },
        }
    }

    fn unary_op(&self, o: &ast::UnaryOperator) -> fn(T) -> Result<T, String> {
        match o {
            ast::UnaryOperator::Pos(_) => |x| Ok(x),
            ast::UnaryOperator::Neg(_) => neg,
            ast::UnaryOperator::Not(_) => not,
        }
    }

    fn bin_op(&self, o: &ast::BinaryOperator) -> fn(T, T) -> Result<T, String> {
        match o {
            ast::BinaryOperator::BitXor => bitxor,
            ast::BinaryOperator::BitAnd => bitand,
            ast::BinaryOperator::BitOr => bitor,
            ast::BinaryOperator::RightShift => shr,
            ast::BinaryOperator::LeftShift => shl,
            ast::BinaryOperator::Or => or,
            ast::BinaryOperator::And => and,
            ast::BinaryOperator::Add => add,
            ast::BinaryOperator::Sub => sub,
            ast::BinaryOperator::Mul => mul,
            ast::BinaryOperator::Div => div,
            ast::BinaryOperator::Rem => rem,
            ast::BinaryOperator::Eq => eq,
            ast::BinaryOperator::NotEq => neq,
            ast::BinaryOperator::Lt => ult,
            ast::BinaryOperator::Gt => ugt,
            ast::BinaryOperator::Lte => ule,
            ast::BinaryOperator::Gte => uge,
            ast::BinaryOperator::Pow => pow,
        }
    }

    fn file_stack_push(&self, path: PathBuf) {
        self.file_stack.borrow_mut().push(path);
    }

    fn file_stack_pop(&self) -> Option<PathBuf> {
        self.file_stack.borrow_mut().pop()
    }

    fn generics_stack_push(&self, generics: HashMap<String, T>) {
        self.generics_stack.borrow_mut().push(generics)
    }

    fn generics_stack_pop(&self) {
        self.generics_stack.borrow_mut().pop();
    }

    fn explicit_generic_values(
        &self,
        eg: Option<&ast::ExplicitGenerics<'ast>>,
        gv: Vec<ast::IdentifierExpression<'ast>>,
    ) -> HashMap<String, T> {
        eg.map(|g| {
            g.values
                .iter()
                .map(|cgv| match cgv {
                    ast::ConstantGenericValue::Value(l) => self.unwrap(self.literal_(&l), l.span()),
                    ast::ConstantGenericValue::Identifier(i) => {
                        if let Some(v) = self.generic_lookup_(&i.value) {
                            v
                        } else if let Some(v) = self.const_lookup_(&i.value) {
                            v.clone()
                        } else {
                            self.err(
                                format!(
                                    "no const {} in current context",
                                    &i.value
                                ),
                                &i.span,
                            );
                        }
                    }
                    ast::ConstantGenericValue::Underscore(u) => {
                        self.err(
                            "non-monomorphized generic argument",
                            &u.span,
                        );
                    }
                })
                .zip(gv.into_iter())
                .map(|(g, n)| (n.value, g))
                .collect()
        })
        .unwrap_or_else(|| HashMap::new())
    }

    fn identifier_(&self, u: &ast::IdentifierExpression<'ast>) -> T {
        if let Some(v) = self.generic_lookup_(&u.value) {
            v
        } else if let Some(v) = self.const_lookup_(&u.value) {
            v.clone()
        } else {
            self.unwrap(self.circ_get_value(Loc::local(u.value.clone())), &u.span)
               .unwrap_term()
        }
    }

    fn expr(&self, e: &ast::Expression<'ast>) -> T {
        debug!("Expr: {}", e.span().as_str());
        let res = match e {
            ast::Expression::Ternary(u) => {
                let c = self.expr(&u.first);
                let a = self.expr(&u.second);
                let b = self.expr(&u.third);
                cond(c, a, b)
            }
            ast::Expression::Binary(u) => {
                let f = self.bin_op(&u.op);
                let a = self.expr(&u.left);
                let b = self.expr(&u.right);
                f(a, b)
            }
            ast::Expression::Unary(u) => {
                let f = self.unary_op(&u.op);
                let a = self.expr(&u.expression);
                f(a)
            }
            ast::Expression::Identifier(u) => Ok(self.identifier_(u)),
            ast::Expression::InlineArray(u) => {
                let mut avals = Vec::with_capacity(u.expressions.len());
                u.expressions.iter().for_each(|ee| match ee {
                    ast::SpreadOrExpression::Expression(eee) => avals.push(self.expr(eee)),
                    ast::SpreadOrExpression::Spread(s) => {
                        let arr = self.expr(&s.expression).unwrap_array();
                        avals.append(&mut self.unwrap(arr, s.expression.span()));
                    }
                });
                T::new_array(avals)
            }
            ast::Expression::Literal(l) => self.literal_(l),
            ast::Expression::InlineStruct(u) => Ok(T::new_struct(
                u.ty.value.clone(),
                u.members
                    .iter()
                    .map(|m| (m.id.value.clone(), self.expr(&m.expression)))
                    .collect(),
            )),
            ast::Expression::ArrayInitializer(a) => {
                let v = self.expr(&a.value);
                let n = self.const_usize(&a.count);
                array(vec![v; n])
            }
            ast::Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                let (base, accs) = if let Some(ast::Access::Call(c)) = p.accesses.first() {
                    let (f_path, f_name) = self.deref_import(&p.id.value);
                    debug!("Call: {} {:?} {:?}", p.id.value, f_path, f_name);
                    let args = c
                        .arguments
                        .expressions
                        .iter()
                        .map(|e| self.expr(e))
                        .collect::<Vec<_>>();
                    let exp_ty = self.lhs_ty_take()
                        .and_then(|ty| if p.accesses.len() > 1 { None } else { Some(ty) });
                    let res = self.function_call(args, c, exp_ty, f_path, f_name);
                    (self.unwrap(res, &c.span), &p.accesses[1..])
                } else {
                    // assume no calls
                    (
                        self.unwrap(
                            self.circ_get_value(Loc::local(p.id.value.clone())),
                            &p.id.span,
                        )
                        .unwrap_term(),
                        &p.accesses[..],
                    )
                };
                accs.iter().fold(Ok(base), |b, acc| match acc {
                    ast::Access::Member(m) => field_select(&b?, &m.id.value),
                    ast::Access::Select(a) => match &a.expression {
                        ast::RangeOrExpression::Expression(e) => array_select(b?, self.expr(e)),
                        ast::RangeOrExpression::Range(r) => {
                            let s = r.from.as_ref().map(|s| self.const_usize(&s.0));
                            let e = r.to.as_ref().map(|s| self.const_usize(&s.0));
                            slice(b?, s, e)
                        }
                    },
                    ast::Access::Call(_) => unreachable!("stray call"),
                })
            }
        };
        self.unwrap(res, e.span())
    }

    fn function_call(
        &self,
        args: Vec<T>,
        call: &ast::CallAccess<'ast>,
        exp_ty: Option<Ty>,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<T, String> {
        debug!("Function call: {} {:?} {:?}", f_name, f_path, args);
        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;
        let generics = ZGenericInf::new(self, f).unify_generic(call, exp_ty, &args[..])?;

        if self.stdlib.is_embed(&f_path) {
            let mut generics = generics;
            let generics = f.generics.iter()
                .map(|gid| generics.remove(&gid.value).ok_or_else(|| format!(
                    "Failed to find generic argument {} for builtin call {}",
                    &gid.value,
                    &f_name,
                )))
                .collect::<Result<Vec<_>,_>>()?;
            Self::builtin_call(&f_name, args, generics)
        } else {
            let f = f.clone();
            if f.generics.len() != generics.len() {
                return Err("Wrong number of generic params for function call".to_string());
            }
            if f.parameters.len() != args.len() {
                return Err("Wrong nimber of arguments for function call".to_string());
            }
            self.file_stack_push(f_path);
            self.generics_stack_push(generics);
            self.ret_ty_stack_push::<false>(&f);
            // XXX(unimpl) tuple returns not supported
            assert!(f.returns.len() <= 1);
            let ret_ty = f.returns.first().map(|r| self.type_(r));
            self.circ_enter_fn(f_name, ret_ty);
            for (p, a) in f.parameters.into_iter().zip(args) {
                let ty = self.type_(&p.ty);
                self.circ_declare_init(p.id.value, ty, Val::Term(a))
                    .map_err(|e| format!("{}", e))?;
            }
            for s in &f.statements {
                self.stmt(s);
            }
            let ret = self
                .circ_exit_fn()
                .map(|a| a.unwrap_term())
                .unwrap_or_else(|| z_bool_lit(false));
            self.ret_ty_stack_pop();
            self.generics_stack_pop();
            self.file_stack_pop();
            Ok(ret)
        }
    }

    fn const_entry_fn(&self, n: &str) -> T {
        debug!("Const entry: {}", n);
        let (f_file, f_name) = self.deref_import(n);
        if let Some(f) = self.functions.get(&f_file).and_then(|m| m.get(&f_name)) {
            if !f.generics.is_empty() {
                panic!("const_entry_fn cannot be called on a generic function")
            } else if !f.parameters.is_empty() {
                panic!("const_entry_fn must be called on a function with zero arguments")
            }
        } else {
            panic!("No function '{:?}//{}' attempting const_entry_fn", &f_file, &f_name);
        }

        self.const_function_call_(Vec::new(), None, None, f_file, f_name)
            .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
    }

    fn entry_fn(&self, n: &str) {
        debug!("Entry: {}", n);
        // find the entry function
        let (f_file, f_name) = self.deref_import(n);
        let f = self
            .functions
            .get(&f_file)
            .unwrap_or_else(|| panic!("No file '{:?}'", &f_file))
            .get(&f_name)
            .unwrap_or_else(|| panic!("No function '{}'", &f_name))
            .clone();
        // XXX(unimpl) tuple returns not supported
        assert!(f.returns.len() <= 1);
        if !f.generics.is_empty() {
            self.err("Entry function cannot be generic. Try adding a wrapper function that supplies an explicit generic argument.", &f.span);
        }
        // get return type
        let ret_ty = f.returns.first().map(|r| self.type_(r));
        // set up stack frame for entry function
        self.circ_enter_fn(n.to_owned(), ret_ty.clone());
        for p in f.parameters.iter() {
            let ty = self.type_(&p.ty);
            debug!("Entry param: {}: {}", p.id.value, ty);
            let vis = self.interpret_visibility(&p.visibility);
            let r = self.circ_declare(p.id.value.clone(), &ty, true, vis);
            self.unwrap(r, &p.span);
        }
        for s in &f.statements {
            self.stmt(s);
        }
        if let Some(r) = self.circ_exit_fn() {
            match self.mode {
                Mode::Mpc(_) => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    self.circ
                        .borrow()
                        .cir_ctx()
                        .cs
                        .borrow_mut()
                        .outputs
                        .extend(ret_terms);
                }
                Mode::Proof => {
                    let ty = ret_ty.as_ref().unwrap();
                    let name = "return".to_owned();
                    let term = r.unwrap_term();
                    let _r = self.circ_declare(name.clone(), &ty, false, PROVER_VIS);
                    self.circ_assign_with_assertions(name, term, &ty, PUBLIC_VIS);
                }
                Mode::Opt => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    assert!(
                        ret_terms.len() == 1,
                        "When compiling to optimize, there can only be one output"
                    );
                    let t = ret_terms.into_iter().next().unwrap();
                    let t_sort = check(&t);
                    if !matches!(t_sort, Sort::BitVector(_)) {
                        panic!("Cannot maximize output of type {}", t_sort);
                    }
                    self.circ.borrow().cir_ctx().cs.borrow_mut().outputs.push(t);
                }
                Mode::ProofOfHighValue(v) => {
                    let ret_term = r.unwrap_term();
                    let ret_terms = ret_term.terms();
                    assert!(
                        ret_terms.len() == 1,
                        "When compiling to optimize, there can only be one output"
                    );
                    let t = ret_terms.into_iter().next().unwrap();
                    let cmp = match check(&t) {
                        Sort::BitVector(w) => term![BV_UGE; t, bv_lit(v, w)],
                        s => panic!("Cannot maximize output of type {}", s),
                    };
                    self.circ.borrow().cir_ctx().cs.borrow_mut().outputs.push(cmp);
                }
            }
        }
    }
    fn interpret_visibility(&self, visibility: &Option<ast::Visibility<'ast>>) -> Option<PartyId> {
        match visibility {
            None | Some(ast::Visibility::Public(_)) => PUBLIC_VIS.clone(),
            Some(ast::Visibility::Private(private)) => match self.mode {
                Mode::Proof | Mode::Opt | Mode::ProofOfHighValue(_) => {
                    if private.number.is_some() {
                        self.err(
                            format!(
                                "Party number found, but we're generating a {} circuit",
                                self.mode
                            ),
                            &private.span,
                        );
                    }
                    PROVER_VIS.clone()
                }
                Mode::Mpc(n_parties) => {
                    let num_str = private
                        .number
                        .as_ref()
                        .unwrap_or_else(|| self.err("No party number", &private.span));
                    let num_val =
                        u8::from_str_radix(&num_str.value[1..num_str.value.len() - 1], 10)
                            .unwrap_or_else(|e| {
                                self.err(format!("Bad party number: {}", e), &private.span)
                            });
                    if num_val <= n_parties {
                        Some(num_val - 1)
                    } else {
                        self.err(
                            format!(
                                "Party number {} greater than the number of parties ({})",
                                num_val, n_parties
                            ),
                            &private.span,
                        )
                    }
                }
            },
        }
    }

    fn cur_path(&self) -> PathBuf {
        self.file_stack.borrow().last().unwrap().to_path_buf()
    }

    fn cur_dir(&self) -> PathBuf {
        let mut p = self.cur_path();
        p.pop();
        p
    }

    fn cur_import_map(&self) -> Option<&HashMap<String, (PathBuf, String)>> {
        self.import_map.get(self.file_stack.borrow().last().unwrap())
    }

    fn deref_import(&self, s: &str) -> (PathBuf, String) {
        // import map is flattened, so we only need to chase through at most one indirection
        self.cur_import_map()
            .and_then(|m| m.get(s))
            .cloned()
            .unwrap_or_else(|| (self.cur_path(), s.to_string()))
    }

    fn const_int(&self, e: &ast::Expression<'ast>) -> isize {
        let i = const_int(self.expr(e));
        self.unwrap(i, e.span()).to_isize().unwrap()
    }

    fn const_usize(&self, e: &ast::Expression<'ast>) -> usize {
        self.unwrap(const_int(self.expr(e)), e.span()).to_usize().unwrap()
    }

    fn generic_lookup_(&self, i: &str) -> Option<T> {
        self.generics_stack.borrow().last().and_then(|m| m.get(i)).cloned()
    }

    fn const_ty_lookup_(&self, i: &str) -> Option<&ast::Type<'ast>> {
        let (f_file, f_name) = self.deref_import(i);
        self.constants
            .get(&f_file)
            .and_then(|m| m.get(&f_name))
            .map(|(t, _)| t)
    }

    fn const_lookup_(&self, i: &str) -> Option<&T> {
        let (f_file, f_name) = self.deref_import(i);
        self.constants
            .get(&f_file)
            .and_then(|m| m.get(&f_name))
            .map(|(_, v)| v)
    }

    fn const_defined(&self, i: &str) -> bool {
        let (f_file, f_name) = self.deref_import(i);
        self.constants
            .get(&f_file)
            .map(|m| m.contains_key(&f_name))
            .unwrap_or(false)
    }

    fn const_identifier_(&self, i: &ast::IdentifierExpression<'ast>) -> Result<T, String> {
        self.generic_lookup_(i.value.as_ref())
            .or_else(|| self.const_lookup_(i.value.as_ref()).cloned())
            .or_else(|| self.cvar_lookup(i.value.as_ref()))
            .ok_or_else(|| format!("Undefined const identifier {}", &i.value))
    }

    fn const_isize_r_(&self, e: &ast::Expression<'ast>) -> Result<isize, String> {
        const_int(self.const_expr_(e)?)?
            .to_isize()
            .ok_or_else(|| "Constant integer outside isize range".to_string())
    }

    fn const_usize_r_(&self, e: &ast::Expression<'ast>) -> Result<usize, String> {
        const_int(self.const_expr_(e)?)?
            .to_usize()
            .ok_or_else(|| "Constant integer outside usize range".to_string())
    }

    fn const_usize_(&self, e: &ast::Expression<'ast>) -> usize {
        let res = self.const_usize_r_(e);
        self.unwrap(res, e.span())
    }

    // XXX(rsw) make Result<T, (String, &Span)> to give more precise error messages?
    fn const_expr_(&self, e: &ast::Expression<'ast>) -> Result<T, String> {
        debug!("Const expr: {}", e.span().as_str());
        match e {
            ast::Expression::Ternary(u) => {
                match self.const_expr_(&u.first).and_then(|b| const_bool_ref(&b)) {
                    Ok(true) => self.const_expr_(&u.second),
                    Ok(false) => self.const_expr_(&u.third),
                    Err(e) => self.err(format!("ternary condition not const bool: {}", e), &u.span),
                }
            }
            ast::Expression::Binary(b) => {
                let left = self.const_expr_(&b.left)?;
                let right = self.const_expr_(&b.right)?;
                let op = self.bin_op(&b.op);
                op(left, right).and_then(|res| const_val(res))
            }
            ast::Expression::Unary(u) => {
                let arg = self.const_expr_(&u.expression)?;
                let op = self.unary_op(&u.op);
                op(arg).and_then(|res| const_val(res))
            }
            ast::Expression::Identifier(i) => self.const_identifier_(i),
            ast::Expression::Literal(l) => self.literal_(l),
            ast::Expression::InlineArray(ia) => {
                let mut avals = Vec::with_capacity(ia.expressions.len());
                ia.expressions.iter().try_for_each::<_, Result<_, String>>(|ee| match ee {
                    ast::SpreadOrExpression::Expression(eee) => Ok(avals.push(self.const_expr_(eee)?)),
                    ast::SpreadOrExpression::Spread(s) => Ok(avals.append(
                        &mut self.const_expr_(&s.expression)?.unwrap_array()?
                    )),
                })?;
                T::new_array(avals)
            }
            ast::Expression::ArrayInitializer(ai) => {
                let val = self.const_expr_(&ai.value)?;
                let num = self.const_usize_r_(&ai.count)?;
                array(vec![val; num])
            }
            ast::Expression::Postfix(p) => {
                assert!(p.accesses.len() > 0);
                let (mut arr, accs) = if let Some(ast::Access::Call(c)) = p.accesses.first() {
                    // XXX(TODO) use top of lhs_ty_stack if p.accesses.len() == 1

                    let (f_path, f_name) = self.deref_import(&p.id.value);
                    debug!("Const call: {} {:?} {:?}", p.id.value, f_path, f_name);
                    let args = c
                        .arguments
                        .expressions
                        .iter()
                        .map(|e| self.const_expr_(e))
                        .collect::<Result<Vec<_>, _>>()?;
                    let exp_ty = self.lhs_ty_take()
                        .and_then(|ty| if p.accesses.len() > 1 { None } else { Some(ty) });
                    let res = self.const_function_call_(args, Some(c), exp_ty, f_path, f_name)?;
                    (res, &p.accesses[1..])
                } else {
                    (self.const_identifier_(&p.id)?, &p.accesses[..])
                };
                for acc in accs.into_iter() {
                    match acc {
                        ast::Access::Call(_) => Err("Function call in non-first-acc position in const expr".to_string())?,
                        ast::Access::Member(a) => {
                            arr = match arr {
                                T::Struct(ty, mut m) => m.remove(&a.id.value)
                                    .ok_or_else(|| format!("No field '{}' accessing const struct of type {:?}", &a.id.value, ty)),
                                x => Err(format!("Tried to access member of non-Struct type {}", x.type_())),
                            }?;
                        }
                        ast::Access::Select(s) => {
                            arr = match arr {
                                T::Array(ty, mut v) => match &s.expression {
                                    ast::RangeOrExpression::Expression(e) => {
                                        let idx = self.const_usize_r_(e)?;
                                        if v.len() > idx {
                                            Ok(v.swap_remove(idx))
                                        } else {
                                            Err(format!("Out-of-bounds array access: wanted {}, but len was {}", idx, v.len()))
                                        }
                                    }
                                    ast::RangeOrExpression::Range(r) => {
                                        let start = r.from.as_ref().map(|s| self.const_usize_r_(&s.0)).transpose()?.unwrap_or(0);
                                        let end = r.to.as_ref().map(|s| self.const_usize_r_(&s.0)).transpose()?.unwrap_or(v.len());
                                        if start > end || end > v.len() {
                                            Err(format!("Got bad range {}..{} for vec of length {}", start, end, v.len()))
                                        } else {
                                            Ok(T::Array(ty, v.drain(start..end).collect()))
                                        }
                                    }
                                }
                                x => Err(format!("Tried to index into non-Array type {}", x.type_())),
                            }?;
                        }
                    }
                }
                Ok(arr)
            }
            ast::Expression::InlineStruct(u) => u.members.iter()
                    .map(|m| self.const_expr_(&m.expression)
                        .map(|m_expr| (m.id.value.clone(), m_expr))
                    )
                    .collect::<Result<BTreeMap<_,_>,String>>()
                    .map(|members| T::Struct(u.ty.value.clone(), members)),
        }
    }

    fn const_function_call_(
        &self,
        args: Vec<T>,
        call: Option<&ast::CallAccess<'ast>>,
        exp_ty: Option<Ty>,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<T, String> {
        debug!("Const function call: {} {:?} {:?}", f_name, f_path, args);
        let f = self
                .functions
                .get(&f_path)
                .ok_or_else(|| format!("No file '{:?}' attempting const fn call", &f_path))?
                .get(&f_name)
                .ok_or_else(|| format!("No function '{}' attempting const fn call", &f_name))?;
        let generics = if let Some(c) = call {
            ZGenericInf::new(self, f).unify_generic(c, exp_ty, &args[..])?
        } else {
            HashMap::new()
        };

        if self.stdlib.is_embed(&f_path) {
            let mut generics = generics;
            let generics = f.generics.iter()
                .map(|gid| generics.remove(&gid.value).ok_or_else(|| format!(
                    "Failed to find generic argument {} for const builtin call {}",
                    &gid.value,
                    &f_name,
                )))
                .collect::<Result<Vec<_>,_>>()?;
            Self::builtin_call(&f_name, args, generics)
        } else {
            let f = f.clone();
            if f.generics.len() != generics.len() {
                Err("Wrong number of generic params for function call".to_string())?;
            }
            if f.parameters.len() != args.len() {
                Err("Wrong number of arguments for function call".to_string())?;
            }
            // XXX(unimpl) tuple returns not supported
            assert!(f.returns.len() <= 1);
            self.file_stack_push(f_path);
            self.generics_stack_push(generics);
            self.ret_ty_stack_push::<true>(&f);
            self.cvar_enter_function();
            let ret_ty = f.returns.first().map(|r| self.const_type_(r)).unwrap_or(Ty::Bool);
            for (p, a) in f.parameters.into_iter().zip(args) {
                let ty = self.const_type_(&p.ty);
                self.cvar_declare_init(p.id.value, &ty, a)?;
            }
            for s in &f.statements {
                self.const_stmt_(s)?;
            }
            let ret = self.crets_pop();
            self.cvar_exit_function();
            self.ret_ty_stack_pop();
            self.generics_stack_pop();
            self.file_stack_pop();
            if ret.type_() != ret_ty {
                Err(format!("Return type mismatch: expected {}, got {}", ret_ty, ret.type_()))
            } else {
                Ok(ret)
            }
        }
    }

    fn const_stmt_(&self, s: &ast::Statement<'ast>) -> Result<(), String> {
        debug!("Const stmt: {}", s.span().as_str());
        match s {
            ast::Statement::Return(r) => {
                // XXX(unimpl) multi-return unimplemented
                assert!(r.expressions.len() <= 1);
                // XXX(TODO) get return type of current function and set_lhs_ty_
                if let Some(e) = r.expressions.first() {
                    self.set_lhs_ty_ret(r);
                    let ret = self.const_expr_(e)?;
                    self.crets_push(ret);
                } else {
                    self.crets_push(Self::const_bool(false));
                }
                Ok(())
            }
            ast::Statement::Assertion(e) => {
                if self.const_expr_(&e.expression)
                    .and_then(|b| const_bool_ref(&b))
                    .or_else(|err| Err(format!(
                        "Const bool expression {} eval failed: {}",
                        span_to_string(e.expression.span()),
                        err,
                    )))? {
                    Ok(())
                } else {
                    Err(format!("Const assert failed:\n{}", span_to_string(s.span())))
                }
            }
            ast::Statement::Iteration(i) => {
                let ty = self.const_type_(&i.ty);
                let ival_cons = match ty {
                    Ty::Field => T::new_field,
                    Ty::Uint(8) => T::new_u8,
                    Ty::Uint(16) => T::new_u16,
                    Ty::Uint(32) => T::new_u32,
                    Ty::Uint(64) => T::new_u64,
                    _ => { return Err(format!("Iteration variable must be Field or Uint, got {:?}", ty)); }
                };
                // XXX(rsw) CHECK does this work if the range includes negative numbers?
                let s = self.const_isize_r_(&i.from)?;
                let e = self.const_isize_r_(&i.to)?;
                let v_name = i.index.value.clone();
                self.cvar_enter_scope();
                self.cvar_declare(v_name, &ty)?;
                for j in s..e {
                    self.cvar_enter_scope();
                    self.cvar_assign(&i.index.value, &[][..], ival_cons(j))?;
                    for s in &i.statements {
                        self.const_stmt_(s)?;
                    }
                    self.cvar_exit_scope();
                }
                self.cvar_exit_scope();
                Ok(())
            }
            ast::Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                self.set_lhs_ty_defn::<true>(d);
                let e = self.const_expr_(&d.expression)?;

                if let Some(l) = d.lhs.first() {
                    let ty = e.type_();
                    match l {
                        ast::TypedIdentifierOrAssignee::Assignee(l) => {
                            self.cvar_assign(&l.id.value, l.accesses.as_ref(), e)
                        }
                        ast::TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                            let decl_ty = self.const_type_(&l.ty);
                            if decl_ty != ty {
                                Err(format!(
                                    "Const assignment type mismatch: {} annotated vs {} actual",
                                    decl_ty, ty,
                                ))?;
                            }
                            self.cvar_declare_init(l.identifier.value.clone(), &decl_ty, e)
                        }
                    }
                } else {
                    warn!("Const statement with no LHS!");
                    Ok(())
                }
            }
        }
    }

    fn set_lhs_ty_defn<const IS_CNST: bool>(&self, d: &ast::DefinitionStatement<'ast>) {
        assert!(self.lhs_ty.borrow().is_none());  // starting from nothing...
        if let ast::Expression::Postfix(pfe) = &d.expression {
            if matches!(pfe.accesses.first(), Some(ast::Access::Call(_))) {
                let ty = self.unwrap(
                    d.lhs.first().map(|ty| self.lhs_type::<IS_CNST>(ty)).transpose(),
                    &d.span,
                );
                self.lhs_ty_put(ty);
            }
        }
    }

    fn set_lhs_ty_ret(&self, r: &ast::ReturnStatement<'ast>) {
        assert!(self.lhs_ty.borrow().is_none()); // starting from nothing...
        if let Some(ast::Expression::Postfix(pfe)) = r.expressions.first() {
            if matches!(pfe.accesses.first(), Some(ast::Access::Call(_))) {
                let ty = self.ret_ty_stack_last();
                self.lhs_ty_put(ty);
            }
        }
    }

    fn lhs_type<const IS_CNST: bool>(
        &self,
        tya: &ast::TypedIdentifierOrAssignee<'ast>,
    ) -> Result<Ty, String> {
        use ast::TypedIdentifierOrAssignee::*;
        match tya {
            Assignee(a) => {
                let t = if IS_CNST { self.const_identifier_(&a.id)? } else { self.identifier_(&a.id) };
                a.accesses.iter().fold(Ok(t.type_()), |ty, acc| ty.and_then(|ty| match acc {
                    ast::AssigneeAccess::Select(aa) => match ty {
                        Ty::Array(sz, ity) => match &aa.expression {
                            ast::RangeOrExpression::Expression(_) => Ok(*ity),
                            ast::RangeOrExpression::Range(_) => Ok(Ty::Array(sz, ity)),
                        }
                        ty => Err(format!("Attempted array access on non-Array type {}", ty)),
                    },
                    ast::AssigneeAccess::Member(sa) => match ty {
                        Ty::Struct(nm, mut map) => map.remove(&sa.id.value)
                            .ok_or_else(|| format!("No such member {} of struct {}", &sa.id.value, nm)),
                        ty => Err(format!("Attempted member access on non-Struct type {}", ty)),
                    },
                }))
            }
            TypedIdentifier(t) => Ok(self.type_impl_::<IS_CNST>(&t.ty)),
        }
    }

    fn lhs_ty_put(&self, lhs_ty: Option<Ty>) {
        self.lhs_ty.replace(lhs_ty);
    }

    fn lhs_ty_take(&self) -> Option<Ty> {
        self.lhs_ty.borrow_mut().take()
    }

    fn cvar_enter_scope(&self) {
        assert!(!self.cvars_stack.borrow().is_empty());
        self.cvars_stack.borrow_mut().last_mut().unwrap().push(HashMap::new());
    }

    fn cvar_exit_scope(&self) {
        assert!(!self.cvars_stack.borrow().last().unwrap().is_empty());
        self.cvars_stack.borrow_mut().last_mut().unwrap().pop();
    }

    fn cvar_enter_function(&self) {
        self.cvars_stack.borrow_mut().push(Vec::new());
        self.cvar_enter_scope();
    }

    fn cvar_exit_function(&self) {
        self.cvars_stack.borrow_mut().pop();
    }

    fn cvar_assign(&self, name: &str, accs: &[ast::AssigneeAccess<'ast>], val: T) -> Result<(), String> {
        assert!(!self.cvars_stack.borrow().last().unwrap().is_empty());

        // compute path to updated value before borrowing cvars_stack (because
        // we might need to evaluate expressions while walking the accesses)
        let mut cvmsaccs = Vec::with_capacity(accs.len());
        accs.iter().try_for_each(|acc| match acc {
            ast::AssigneeAccess::Select(a) => match &a.expression {
                ast::RangeOrExpression::Range(_) => Err("cvar_assign cannot assign to Range".to_string()),
                ast::RangeOrExpression::Expression(e) => Ok(cvmsaccs.push(CVMSAcc::Sel(self.const_usize_r_(e)?))),
            },
            ast::AssigneeAccess::Member(a) => Ok(cvmsaccs.push(CVMSAcc::Mem(&a.id.value))),
        })?;

        match self.cvars_stack.borrow_mut().last_mut().unwrap().iter_mut().rev().find_map(|v| v.get_mut(name)) {
            None => Err(format!("Const assign failed: no variable {} in scope", name)),
            Some(mut old_val) => {
                // walk previously computed accesses
                for acc in cvmsaccs.into_iter() {
                    match acc {
                        CVMSAcc::Sel(idx) => {
                            old_val = match old_val {
                                T::Array(_, v) => v.get_mut(idx).ok_or_else(|| format!("Tried to access idx {}, which was out of bounds", idx)),
                                _ => Err(format!("Tried to index into non-Array type {}", old_val.type_())),
                            }?;
                        }
                        CVMSAcc::Mem(name) => {
                            old_val = match old_val {
                                T::Struct(_, m) => m.get_mut(name).ok_or_else(|| format!("No field '{}' accessing const struct", name)),
                                _ => Err(format!("Tried to access member '{}' in non-Struct type", name)),
                            }?;
                        }
                    }
                }
                if old_val.type_() != val.type_() {
                    Err(format!(
                        "Const assign type mismatch: got {}, expected {}",
                        val.type_(),
                        old_val.type_(),
                    ))
                } else {
                    *old_val = val;
                    Ok(())
                }
            }
        }
    }

    fn cvar_declare_init(&self, name: String, ty: &Ty, val: T) -> Result<(), String> {
        assert!(!self.cvars_stack.borrow().last().unwrap().is_empty());
        if val.type_() != *ty {
            Err(format!("Const decl_init: {} type mismatch: expected {}, got {}", name, ty, val.type_()))?;
        }
        self.cvars_stack
            .borrow_mut()
            .last_mut()
            .unwrap()
            .last_mut()
            .unwrap()
            .insert(name, val);
        Ok(())
    }

    fn cvar_declare(&self, name: String, ty: &Ty) -> Result<(), String> {
        self.cvar_declare_init(name, ty, ty.default())
    }

    fn cvar_lookup(&self, name: &str) -> Option<T> {
        if let Some(st) = self.cvars_stack.borrow().last() {
            st.iter().rev().find_map(|v| v.get(name).cloned())
        } else {
            None
        }
    }

    fn ret_ty_stack_push<const IS_CNST: bool>(&self, fn_def: &ast::FunctionDefinition<'ast>) {
        let ty = fn_def.returns.first().map(|ty| self.type_impl_::<IS_CNST>(ty)).unwrap_or(Ty::Bool);
        self.ret_ty_stack.borrow_mut().push(ty);
    }

    fn ret_ty_stack_pop(&self) {
        self.ret_ty_stack.borrow_mut().pop();
    }

    fn ret_ty_stack_last(&self) -> Option<Ty> {
        self.ret_ty_stack.borrow().last().cloned()
    }

    fn crets_push(&self, ret: T) {
        self.crets_stack.borrow_mut().push(ret)
    }

    fn crets_pop(&self) -> T {
        assert!(!self.crets_stack.borrow().is_empty());
        self.crets_stack.borrow_mut().pop().unwrap()
    }

    fn const_decl_(&mut self, c: &mut ast::ConstantDefinition<'ast>) {
        // make sure that this wasn't already an important const name
        if self.cur_import_map()
            .map(|m| m.contains_key(&c.id.value))
            .unwrap_or(false)
        {
            self.err(
                format!("Constant {} clashes with import of same name", &c.id.value),
                &c.span,
            );
        }

        // rewrite literals in the const type decl
        let mut v = ZConstLiteralRewriter::new(None);
        v.visit_type(&mut c.ty)
            .unwrap_or_else(|e| self.err(e.0, &c.span));
        let ctype = self.const_type_(&c.ty);
        // handle literal type inference using declared type
        v.replace(Some(ctype.clone()));
        v.visit_expression(&mut c.expression)
            .unwrap_or_else(|e| self.err(e.0, &c.span));

        // evaluate the expression and check the resulting type
        let value = self
            .const_expr_(&c.expression)
            .unwrap_or_else(|e| self.err(e, c.expression.span()));
        if ctype != value.type_() {
            self.err(format!("Type mismatch in constant definition: expected {:?}, got {:?}", ctype, value.type_()), &c.span);
        }

        // insert into constant map
        if self
            .constants
            .get_mut(self.file_stack.borrow().last().unwrap())
            .unwrap()
            .insert(c.id.value.clone(), (c.ty.clone(), value))
            .is_some()
        {
            self.err(format!("Constant {} redefined", &c.id.value), &c.span);
        }
    }

    fn type_(&self, t: &ast::Type<'ast>) -> Ty {
        debug!("Type: {:?}", t);
        self.type_impl_::<false>(t)
    }

    fn const_type_(&self, t: &ast::Type<'ast>) -> Ty {
        debug!("Const type: {:?}", t);
        self.type_impl_::<true>(t)
    }

    fn type_impl_<const IS_CNST: bool>(&self, t: &ast::Type<'ast>) -> Ty {
        fn lift<'ast>(t: &ast::BasicOrStructType<'ast>) -> ast::Type<'ast> {
            match t {
                ast::BasicOrStructType::Basic(b) => ast::Type::Basic(b.clone()),
                ast::BasicOrStructType::Struct(b) => ast::Type::Struct(b.clone()),
            }
        }
        match t {
            ast::Type::Basic(ast::BasicType::U8(_)) => Ty::Uint(8),
            ast::Type::Basic(ast::BasicType::U16(_)) => Ty::Uint(16),
            ast::Type::Basic(ast::BasicType::U32(_)) => Ty::Uint(32),
            ast::Type::Basic(ast::BasicType::U64(_)) => Ty::Uint(64),
            ast::Type::Basic(ast::BasicType::Boolean(_)) => Ty::Bool,
            ast::Type::Basic(ast::BasicType::Field(_)) => Ty::Field,
            ast::Type::Array(a) => {
                let b = self.type_impl_::<IS_CNST>(&lift(&a.ty));
                let f = if IS_CNST { Self::const_usize_ } else { Self::const_usize };
                a.dimensions
                    .iter()
                    .rev()
                    .map(|d| f(self, d))
                    .fold(b, |b, d| Ty::Array(d as usize, Box::new(b)))
            }
            ast::Type::Struct(s) => {
                let sdef = self.get_struct(&s.id.value).unwrap_or_else(||
                    self.err(format!("No such struct {}", &s.id.value), &s.span)
                ).clone();
                let g_len = sdef.generics.len();
                let generics = self.explicit_generic_values(s.explicit_generics.as_ref(), sdef.generics);
                if generics.len() != g_len {
                    self.err(format!("Struct {} is not monomorphized or wrong number of generic parameters", &s.id.value), &s.span);
                }
                self.generics_stack_push(generics);
                let ty = Ty::Struct(
                    s.id.value.clone(),
                    sdef.fields.into_iter().map(|f| (f.id.value, self.type_impl_::<IS_CNST>(&f.ty))).collect()
                );
                self.generics_stack_pop();
                ty
            }
        }
    }

    fn visit_files(&mut self) {
        // 1. go through includes and return a toposorted visit order for remaining processing
        let files = self.visit_imports();

        // 2. visit constant, struct, and function defs ; infer types and generics
        self.visit_declarations(files);
    }

    fn visit_imports(&mut self) -> Vec<PathBuf> {
        use petgraph::algo::toposort;
        use petgraph::graph::{DefaultIx, DiGraph, NodeIndex};
        let asts = std::mem::take(&mut self.asts);

        // we use the graph to toposort the includes and the map to go from PathBuf to NodeIdx
        let mut ig = DiGraph::<PathBuf, ()>::with_capacity(asts.len(), asts.len());
        let mut gn = HashMap::<PathBuf, NodeIndex<DefaultIx>>::with_capacity(asts.len());

        for (p, f) in asts.iter() {
            self.file_stack_push(p.to_owned());
            let mut imap = HashMap::new();

            if !gn.contains_key(p) {
                gn.insert(p.to_owned(), ig.add_node(p.to_owned()));
            }

            for d in f.declarations.iter() {
                // XXX(opt) retain() declarations instead? if we don't need them, saves allocs
                if let ast::SymbolDeclaration::Import(i) = d {
                    let (src_path, src_names, dst_names, i_span) = match i {
                        ast::ImportDirective::Main(m) => (
                            m.source.value.clone(),
                            vec!["main".to_owned()],
                            vec![m
                                .alias
                                .as_ref()
                                .map(|a| a.value.clone())
                                .unwrap_or_else(|| {
                                    PathBuf::from(m.source.value.clone())
                                        .file_stem()
                                        .unwrap_or_else(|| panic!("Bad import: {}", m.source.value))
                                        .to_string_lossy()
                                        .to_string()
                                })],
                            &m.span,
                        ),
                        ast::ImportDirective::From(m) => (
                            m.source.value.clone(),
                            m.symbols.iter().map(|s| s.id.value.clone()).collect(),
                            m.symbols
                                .iter()
                                .map(|s| {
                                    s.alias
                                        .as_ref()
                                        .map(|a| a.value.clone())
                                        .unwrap_or_else(|| s.id.value.clone())
                                })
                                .collect(),
                            &m.span,
                        ),
                    };
                    assert!(src_names.len() > 0);
                    let abs_src_path = self.stdlib.canonicalize(&self.cur_dir(), src_path.as_str());
                    debug!(
                        "Import of {:?} from {} as {:?}",
                        src_names,
                        abs_src_path.display(),
                        dst_names
                    );
                    src_names
                        .into_iter()
                        .zip(dst_names.into_iter())
                        .for_each(|(sn, dn)| {
                            if imap.contains_key(&dn) {
                                self.err(format!("Import {} redeclared", dn), i_span);
                            }
                            assert!(imap.insert(dn, (abs_src_path.clone(), sn)).is_none());
                        });

                    // add included -> includer edge for later toposort
                    if !gn.contains_key(&abs_src_path) {
                        gn.insert(abs_src_path.clone(), ig.add_node(abs_src_path.clone()));
                    }
                    ig.add_edge(*gn.get(&abs_src_path).unwrap(), *gn.get(p).unwrap(), ());
                }
            }

            let p = self.file_stack_pop().unwrap();
            self.import_map.insert(p, imap);
        }
        self.asts = asts;

        // flatten the import map, i.e., a -> b -> c becomes a -> c
        self.flatten_import_map();

        toposort(&ig, None)
            .unwrap_or_else(|e| {
                use petgraph::dot::{Config, Dot};
                panic!(
                    "Import graph is cyclic!: {:?}\n{:?}\n",
                    e,
                    Dot::with_config(&ig, &[Config::EdgeNoLabel])
                )
            })
            .iter()
            .map(|idx| std::mem::take(ig.node_weight_mut(*idx).unwrap()))
            .filter(|p| self.asts.contains_key(p))
            .collect()
    }

    fn flatten_import_map(&mut self) {
        // create a new map
        let mut new_map = HashMap::with_capacity(self.import_map.len());
        self.import_map.keys().for_each(|k| {
            new_map.insert(k.clone(), HashMap::new());
        });

        let mut visited = Vec::new();
        for (fname, map) in &self.import_map {
            for (iname, (nv, iv)) in map.iter() {
                // unwrap is safe because of new_map's initialization above
                if new_map.get(fname).unwrap().contains_key(iname) {
                    // visited this value already as part of a prior pointer chase
                    continue;
                }

                // chase the pointer, writing down every visited key along the way
                visited.clear();
                visited.push((fname, iname));
                let mut n = nv;
                let mut i = iv;
                while let Some((nn, ii)) = self.import_map.get(n).and_then(|m| m.get(i)) {
                    visited.push((n, i));
                    n = nn;
                    i = ii;
                }

                // map every visited key to the final value in the ptr chase
                visited.iter().for_each(|&(nn, ii)| {
                    new_map
                        .get_mut(nn)
                        .unwrap()
                        .insert(ii.clone(), (n.clone(), i.clone()));
                });
            }
        }

        self.import_map = new_map;
    }

    fn visit_declarations(&mut self, files: Vec<PathBuf>) {
        let mut t = std::mem::take(&mut self.asts);
        let mut clr = ZConstLiteralRewriter::new(None);
        for p in files {
            self.constants.insert(p.clone(), HashMap::new());
            self.structs.insert(p.clone(), HashMap::new());
            self.functions.insert(p.clone(), HashMap::new());
            self.file_stack_push(p.clone());
            for d in t.get_mut(&p).unwrap().declarations.iter_mut() {
                match d {
                    ast::SymbolDeclaration::Constant(c) => {
                        debug!("processing decl: const {} in {}", c.id.value, p.display());
                        self.const_decl_(c);
                    }
                    ast::SymbolDeclaration::Struct(s) => {
                        debug!("processing decl: struct {} in {}", s.id.value, p.display());
                        let mut s_ast = s.clone();

                        // rewrite literals in ArrayTypes
                        clr.visit_struct_definition(&mut s_ast)
                            .unwrap_or_else(|e| self.err(e.0, &s.span));

                        self.structs
                            .get_mut(self.file_stack.borrow().last().unwrap())
                            .unwrap()
                            .insert(s.id.value.clone(), s_ast)
                            .map(|_| self.err(format!("Struct {} redefined", &s.id.value), &s.span));
                    }
                    ast::SymbolDeclaration::Function(f) => {
                        debug!("processing decl: fn {} in {}", f.id.value, p.display());
                        let mut f_ast = f.clone();

                        // rewrite literals in params and returns
                        let mut v = ZConstLiteralRewriter::new(None);
                        f_ast
                            .parameters
                            .iter_mut()
                            .try_for_each(|p| v.visit_parameter(p))
                            .unwrap_or_else(|e| self.err(e.0, &f.span));
                        if f_ast.returns.len() != 1 {
                            // XXX(unimpl) functions MUST return exactly 1 value
                            self.err(
                                format!("Functions must return exactly 1 value; {} returns {}",
                                    &f_ast.id.value,
                                    f_ast.returns.len(),
                                ),
                                &f.span,
                            );
                        }
                        f_ast
                            .returns
                            .iter_mut()
                            .try_for_each(|r| v.visit_type(r))
                            .unwrap_or_else(|e| self.err(e.0, &f.span));

                        // go through stmts typechecking and rewriting literals
                        let mut sw = ZStatementWalker::new(
                            f_ast.parameters.as_ref(),
                            f_ast.returns.as_ref(),
                            f_ast.generics.as_ref(),
                            self,
                        );
                        f_ast
                            .statements
                            .iter_mut()
                            .try_for_each(|s| sw.visit_statement(s))
                            .unwrap_or_else(|e| self.err(e.0, &f.span));

                        self.functions
                            .get_mut(self.file_stack.borrow().last().unwrap())
                            .unwrap()
                            .insert(f.id.value.clone(), f_ast)
                            .map(|_| self.err(format!("Function {} redefined", &f.id.value), &f.span));
                    }
                    ast::SymbolDeclaration::Import(_) => (), // already handled in visit_imports
                }
            }
            self.file_stack_pop();
        }
        self.asts = t;
    }

    fn get_function(&self, fn_id: &str) -> Option<&ast::FunctionDefinition<'ast>> {
        let (f_path, f_name) = self.deref_import(fn_id);
        self.functions.get(&f_path).and_then(|m| m.get(&f_name))
    }

    fn get_struct(&self, struct_id: &str) -> Option<&ast::StructDefinition<'ast>> {
        let (s_path, s_name) = self.deref_import(struct_id);
        self.structs.get(&s_path).and_then(|m| m.get(&s_name))
    }

    /*** circify wrapper functions (hides RefCell) ***/

    fn circ_assert(&self, asrt: Term) {
        self.circ.borrow_mut().assert(asrt)
    }

    fn circ_return_(&self, ret: Option<T>) -> Result<(), CircError> {
        self.circ.borrow_mut().return_(ret)
    }

    fn circ_enter_fn(&self, f_name: String, ret_ty: Option<Ty>) {
        self.circ.borrow_mut().enter_fn(f_name, ret_ty)
    }

    fn circ_exit_fn(&self) -> Option<Val<T>> {
        self.circ.borrow_mut().exit_fn()
    }

    fn circ_enter_scope(&self) {
        self.circ.borrow_mut().enter_scope()
    }

    fn circ_exit_scope(&self) {
        self.circ.borrow_mut().exit_scope()
    }

    fn circ_declare(&self, name: String, ty: &Ty, input: bool, vis: Option<PartyId>) -> Result<(), CircError> {
        self.circ.borrow_mut().declare(name, ty, input, vis)
    }

    fn circ_declare_init(&self, name: String, ty: Ty, val: Val<T>) -> Result<Val<T>, CircError> {
        self.circ.borrow_mut().declare_init(name, ty, val)
    }

    fn circ_get_value(&self, loc: Loc) -> Result<Val<T>, CircError> {
        self.circ.borrow().get_value(loc)
    }

    fn circ_assign(&self, loc: Loc, val: Val<T>) -> Result<Val<T>, CircError> {
        self.circ.borrow_mut().assign(loc, val)
    }

    fn circ_assign_with_assertions(&self, name: String, term: T, ty: &Ty, vis: Option<PartyId>) {
        self.circ.borrow_mut().assign_with_assertions(name, term, ty, vis)
    }
}

fn span_to_string(span: &ast::Span) -> String {
    span.lines().collect::<String>()
}

enum CVMSAcc<'t> {
    Sel(usize),
    Mem(&'t str),
}
