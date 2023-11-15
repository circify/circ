//! The ZoKrates/Z# front-end

mod interp;
mod parser;
mod term;
pub mod zvisit;

use super::{FrontEnd, Mode};
use crate::cfg::cfg;
use crate::circify::{CircError, Circify, Loc, Val};
use crate::front::proof::PROVER_ID;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;

use fxhash::FxHashMap;
use log::{debug, info, trace, warn};
use rug::Integer;
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::fmt::Display;
use std::path::PathBuf;
use std::str::FromStr;
use zokrates_pest_ast as ast;

use term::*;
use zvisit::{ZConstLiteralRewriter, ZGenericInf, ZStatementWalker, ZVisitorMut};

// garbage collection increment for adaptive GC threshold
const GC_INC: usize = 32;

/// Inputs to the Z# compiler
pub struct Inputs {
    /// The file to look for `main` in.
    pub file: PathBuf,
    /// The mode to generate for (MPC or proof). Effects visibility.
    pub mode: Mode,
}

/// The Z# front-end. Implements [FrontEnd].
pub struct ZSharpFE;

impl FrontEnd for ZSharpFE {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computations {
        debug!(
            "Starting Z# front-end, field: {}",
            Sort::Field(cfg().field().clone())
        );
        let loader = parser::ZLoad::new();
        let asts = loader.load(&i.file);
        let mut g = ZGen::new(asts, i.mode, loader.stdlib(), cfg().zsharp.isolate_asserts);
        g.visit_files();
        g.file_stack_push(i.file);
        g.generics_stack_push(HashMap::new());
        g.entry_fn("main");
        g.generics_stack_pop();
        g.file_stack_pop();

        let mut cs = Computations::new();
        let main_comp = std::rc::Rc::try_unwrap(g.into_circify().consume())
            .unwrap_or_else(|rc| (*rc).clone())
            .into_inner();
        cs.comps.insert("main".to_string(), main_comp);
        cs
    }
}

impl ZSharpFE {
    /// Execute the Z# front-end interpreter on the supplied file with the supplied inputs
    pub fn interpret(i: Inputs, input_scalar_values: FxHashMap<String, Value>) -> T {
        let loader = parser::ZLoad::new();
        let asts = loader.load(&i.file);
        let mut g = ZGen::new(asts, i.mode, loader.stdlib(), cfg().zsharp.isolate_asserts);
        g.visit_files();
        g.file_stack_push(i.file);
        g.generics_stack_push(HashMap::new());
        g.const_entry_fn("main", input_scalar_values)
    }
}

struct ZGen<'ast> {
    circ: RefCell<Circify<ZSharp>>,
    stdlib: &'ast parser::ZStdLib,
    asts: HashMap<PathBuf, ast::File<'ast>>,
    file_stack: RefCell<Vec<PathBuf>>,
    generics_stack: RefCell<Vec<HashMap<String, T>>>,
    functions: HashMap<PathBuf, HashMap<String, ast::FunctionDefinition<'ast>>>,
    // We use a single map for both type definitions and structures.
    structs_and_tys: HashMap<
        PathBuf,
        HashMap<String, Result<ast::StructDefinition<'ast>, ast::TypeDefinition<'ast>>>,
    >,
    constants: HashMap<PathBuf, HashMap<String, (ast::Type<'ast>, T)>>,
    import_map: HashMap<PathBuf, HashMap<String, (PathBuf, String)>>,
    mode: Mode,
    cvars_stack: RefCell<Vec<Vec<HashMap<String, T>>>>,
    crets_stack: RefCell<Vec<T>>,
    lhs_ty: RefCell<Option<Ty>>,
    ret_ty_stack: RefCell<Vec<Ty>>,
    gc_depth_estimate: Cell<usize>,
    assertions: RefCell<Vec<Term>>,
    challenge_count: Cell<usize>,
    isolate_asserts: bool,
}

impl<'ast> Drop for ZGen<'ast> {
    fn drop(&mut self) {
        use std::mem::take;

        // drop all fields that contain T or Ty
        drop(self.generics_stack.take());
        drop(take(&mut self.constants));
        drop(self.cvars_stack.take());
        drop(self.crets_stack.take());
        drop(self.lhs_ty.take());
        drop(self.ret_ty_stack.take());

        // force garbage collection
        garbage_collect();
    }
}

enum ZAccess {
    Member(String),
    Idx(T),
}

fn loc_store(struct_: T, loc: &[ZAccess], val: T) -> Result<T, String> {
    match loc.first() {
        None => Ok(val),
        Some(ZAccess::Member(field)) => {
            let inner = field_select(&struct_, field)?;
            let new_inner = loc_store(inner, &loc[1..], val)?;
            field_store(struct_, field, new_inner)
        }
        Some(ZAccess::Idx(idx)) => {
            let old_inner = array_select(struct_.clone(), idx.clone())?;
            let new_inner = loc_store(old_inner, &loc[1..], val)?;
            array_store(struct_, idx.clone(), new_inner)
        }
    }
}

enum ZVis {
    Public,
    Private(u8),
}

enum ArrayParamMetadata {
    Committed,
    Transcript,
}

impl<'ast> ZGen<'ast> {
    fn new(
        asts: HashMap<PathBuf, ast::File<'ast>>,
        mode: Mode,
        stdlib: &'ast parser::ZStdLib,
        isolate_asserts: bool,
    ) -> Self {
        let this = Self {
            circ: RefCell::new(Circify::new(ZSharp::new())),
            asts,
            stdlib,
            file_stack: Default::default(),
            generics_stack: Default::default(),
            functions: HashMap::new(),
            structs_and_tys: HashMap::new(),
            constants: HashMap::new(),
            import_map: HashMap::new(),
            mode,
            cvars_stack: Default::default(),
            crets_stack: Default::default(),
            lhs_ty: Default::default(),
            ret_ty_stack: Default::default(),
            gc_depth_estimate: Cell::new(2 * GC_INC),
            assertions: Default::default(),
            challenge_count: Cell::new(0),
            isolate_asserts,
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

    fn into_circify(self) -> Circify<ZSharp> {
        self.circ.replace(Circify::new(ZSharp::new()))
    }

    /// Unwrap a result with a span-dependent error
    fn err<E: Display>(&self, e: E, s: &ast::Span) -> ! {
        println!("Error: {e}");
        println!("In: {}", self.cur_path().canonicalize().unwrap().display());
        s.lines().for_each(|l| print!("  {l}"));
        std::process::exit(1)
    }

    fn unwrap<T, E: Display>(&self, r: Result<T, E>, s: &ast::Span) -> T {
        r.unwrap_or_else(|e| self.err(e, s))
    }

    fn builtin_call(
        &self,
        f_name: &str,
        mut args: Vec<T>,
        mut generics: Vec<T>,
    ) -> Result<T, String> {
        debug!("Builtin Call: {}", f_name);
        match f_name {
            "u8_to_bits" | "u16_to_bits" | "u32_to_bits" | "u64_to_bits" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/{}, expected 1",
                        args.len(),
                        f_name
                    ))
                } else if !generics.is_empty() {
                    Err(format!(
                        "Got {} generic args to EMBED/{}, expected 0",
                        generics.len(),
                        f_name
                    ))
                } else {
                    uint_to_bits(args.pop().unwrap())
                }
            }
            "u8_from_bits" | "u16_from_bits" | "u32_from_bits" | "u64_from_bits" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/{}, expected 1",
                        args.len(),
                        f_name
                    ))
                } else if !generics.is_empty() {
                    Err(format!(
                        "Got {} generic args to EMBED/{}, expected 0",
                        generics.len(),
                        f_name
                    ))
                } else {
                    uint_from_bits(args.pop().unwrap())
                }
            }
            "u8_to_field" | "u16_to_field" | "u32_to_field" | "u64_to_field" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/{}, expected 1",
                        args.len(),
                        f_name
                    ))
                } else if !generics.is_empty() {
                    Err(format!(
                        "Got {} generic args to EMBED/{}, expected 0",
                        generics.len(),
                        f_name
                    ))
                } else {
                    uint_to_field(args.pop().unwrap())
                }
            }
            "u8_to_u64" | "u16_to_u64" | "u32_to_u64" | "u8_to_u32" | "u16_to_u32"
            | "u8_to_u16" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/{}, expected 1",
                        args.len(),
                        f_name
                    ))
                } else if !generics.is_empty() {
                    Err(format!(
                        "Got {} generic args to EMBED/{}, expected 0",
                        generics.len(),
                        f_name
                    ))
                } else {
                    let len = f_name.len();
                    match &f_name[len - 2..] {
                        "64" => uint_to_uint(args.pop().unwrap(), 64),
                        "32" => uint_to_uint(args.pop().unwrap(), 32),
                        "16" => uint_to_uint(args.pop().unwrap(), 16),
                        _ => unreachable!(),
                    }
                }
            }
            "unpack" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/unpack, expected 1",
                        args.len()
                    ))
                } else if generics.len() != 1 {
                    Err(format!(
                        "Got {} generic args to EMBED/unpack, expected 1",
                        generics.len()
                    ))
                } else {
                    let nbits =
                        const_int(generics.pop().unwrap())?
                            .to_usize()
                            .ok_or_else(|| {
                                "builtin_call failed to convert unpack's N to usize".to_string()
                            })?;
                    field_to_bits(args.pop().unwrap(), nbits)
                }
            }
            "bit_array_le" => {
                if args.len() != 2 {
                    Err(format!(
                        "Got {} args to EMBED/bit_array_le, expected 1",
                        args.len()
                    ))
                } else if generics.len() != 1 {
                    Err(format!(
                        "Got {} generic args to EMBED/bit_array_le, expected 1",
                        generics.len()
                    ))
                } else {
                    let nbits =
                        const_int(generics.pop().unwrap())?
                            .to_usize()
                            .ok_or_else(|| {
                                "builtin_call failed to convert bit_array_le's N to usize"
                                    .to_string()
                            })?;

                    let second_arg = args.pop().unwrap();
                    let first_arg = args.pop().unwrap();
                    bit_array_le(first_arg, second_arg, nbits)
                }
            }
            "get_field_size" => {
                if !args.is_empty() {
                    Err(format!(
                        "Got {} args to EMBED/get_field_size, expected 0",
                        args.len()
                    ))
                } else if !generics.is_empty() {
                    Err(format!(
                        "Got {} generic args to EMBED/get_field_size, expected 0",
                        generics.len()
                    ))
                } else {
                    Ok(uint_lit(cfg().field().modulus().significant_bits(), 32))
                }
            }
            "sample_challenge" => {
                if args.len() != 1 {
                    Err(format!(
                        "Got {} args to EMBED/sample_challenge, expected 1",
                        args.len()
                    ))
                } else if generics.len() != 1 {
                    Err(format!(
                        "Got {} generic args to EMBED/sample_challenge, expected 1",
                        generics.len()
                    ))
                } else {
                    let n = self.challenge_count.get();
                    let t = sample_challenge(args.pop().unwrap(), n)?;
                    self.challenge_count.set(n + 1);
                    Ok(t)
                }
            }
            _ => Err(format!("Unknown or unimplemented builtin '{f_name}'")),
        }
    }

    fn assign_impl_<const IS_CNST: bool>(
        &self,
        name: &str,
        accs: &[ast::AssigneeAccess<'ast>],
        val: T,
        strict: bool,
    ) -> Result<(), String> {
        let zaccs = self.zaccs_impl_::<IS_CNST>(accs)?;
        let old = if IS_CNST {
            self.cvar_lookup(name)
                .ok_or_else(|| format!("Assignment failed: no const variable {name}"))?
        } else {
            self.circ_get_value(Loc::local(name.to_string()))
                .map_err(|e| format!("{e}"))?
                .unwrap_term()
        };
        let new =
            loc_store(old, &zaccs[..], val)
                .and_then(|n| if strict { const_val(n) } else { Ok(n) })?;
        debug!("Assign: {}", name);
        if IS_CNST {
            self.cvar_assign(name, new)
        } else {
            self.circ_assign(Loc::local(name.to_string()), Val::Term(new))
                .map_err(|e| format!("{e}"))
                .map(|_| ())
        }
    }

    fn zaccs_impl_<const IS_CNST: bool>(
        &self,
        accs: &[ast::AssigneeAccess<'ast>],
    ) -> Result<Vec<ZAccess>, String> {
        accs.iter()
            .map(|acc| match acc {
                ast::AssigneeAccess::Member(m) => Ok(ZAccess::Member(m.id.value.clone())),
                ast::AssigneeAccess::Select(m) => match &m.expression {
                    ast::RangeOrExpression::Expression(e) => {
                        self.expr_impl_::<IS_CNST>(e).map(ZAccess::Idx)
                    }
                    _ => Err(format!(
                        "Cannot assign to slice: {}",
                        span_to_string(&m.span)
                    )),
                },
            })
            .collect()
    }

    fn literal_(&self, e: &ast::LiteralExpression<'ast>) -> Result<T, String> {
        match e {
            ast::LiteralExpression::DecimalLiteral(d) => {
                let vstr = &d.value.span.as_str();
                match &d.suffix {
                    Some(ast::DecimalSuffix::U8(_)) => Ok(uint_lit(vstr.parse::<u8>().unwrap(), 8)),
                    Some(ast::DecimalSuffix::U16(_)) => {
                        Ok(uint_lit(vstr.parse::<u16>().unwrap(), 16))
                    }
                    Some(ast::DecimalSuffix::U32(_)) => {
                        Ok(uint_lit(vstr.parse::<u32>().unwrap(), 32))
                    }
                    Some(ast::DecimalSuffix::U64(_)) => {
                        Ok(uint_lit(vstr.parse::<u64>().unwrap(), 64))
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
                ast::HexNumberExpression::U8(h) => {
                    Ok(uint_lit(u8::from_str_radix(&h.value, 16).unwrap(), 8))
                }
                ast::HexNumberExpression::U16(h) => {
                    Ok(uint_lit(u16::from_str_radix(&h.value, 16).unwrap(), 16))
                }
                ast::HexNumberExpression::U32(h) => {
                    Ok(uint_lit(u32::from_str_radix(&h.value, 16).unwrap(), 32))
                }
                ast::HexNumberExpression::U64(h) => {
                    Ok(uint_lit(u64::from_str_radix(&h.value, 16).unwrap(), 64))
                }
            },
        }
        .map_err(|err| format!("{}; context:\n{}", err, span_to_string(e.span())))
    }

    fn unary_op(&self, o: &ast::UnaryOperator) -> fn(T) -> Result<T, String> {
        match o {
            ast::UnaryOperator::Pos(_) => Ok,
            ast::UnaryOperator::Neg(_) => neg,
            ast::UnaryOperator::Not(_) => not,
            ast::UnaryOperator::Strict(_) => const_val,
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

    fn file_stack_depth(&self) -> usize {
        self.file_stack.borrow().len()
    }

    fn generics_stack_push(&self, generics: HashMap<String, T>) {
        self.generics_stack.borrow_mut().push(generics)
    }

    fn generics_stack_pop(&self) {
        self.generics_stack.borrow_mut().pop();
    }

    fn egvs_impl_<const IS_CNST: bool>(
        &self,
        egv: &[ast::ConstantGenericValue<'ast>],
        gens: Vec<ast::IdentifierExpression<'ast>>,
    ) -> Result<HashMap<String, T>, String> {
        egv.iter()
            .map(|cgv| match cgv {
                ast::ConstantGenericValue::Value(l) => self.literal_(l),
                ast::ConstantGenericValue::Identifier(i) => {
                    self.identifier_impl_::<IS_CNST>(i).and_then(const_val)
                }
                ast::ConstantGenericValue::Underscore(_) => Err(
                    "explicit_generic_values got non-monomorphized generic argument".to_string(),
                ),
            })
            .zip(gens)
            .map(|(g, n)| Ok((n.value, g?)))
            .collect()
    }

    fn function_call_impl_<const IS_CNST: bool>(
        &self,
        args: Vec<T>,
        egv: &[ast::ConstantGenericValue<'ast>],
        exp_ty: Option<Ty>,
        f_path: PathBuf,
        f_name: String,
    ) -> Result<T, String> {
        if IS_CNST {
            debug!("Const function call: {} {:?}", f_name, f_path);
        } else {
            debug!("Function call: {} {:?}", f_name, f_path);
        }
        let f = self
            .functions
            .get(&f_path)
            .ok_or_else(|| format!("No file '{:?}' attempting fn call", &f_path))?
            .get(&f_name)
            .ok_or_else(|| format!("No function '{}' attempting fn call", &f_name))?;
        let arg_tys = args.iter().map(|arg| arg.type_().clone());
        let generics = ZGenericInf::<IS_CNST>::new(self, f, &f_path, &f_name)
            .unify_generic(egv, exp_ty, arg_tys)?;

        if self.stdlib.is_embed(&f_path) {
            let mut generics = generics;
            let generics = f
                .generics
                .iter()
                .map(|gid| {
                    generics.remove(&gid.value).ok_or_else(|| {
                        format!(
                            "Failed to find generic argument {} for builtin call {}",
                            &gid.value, &f_name,
                        )
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            self.builtin_call(&f_name, args, generics)
        } else {
            // XXX(unimpl) multi-return unimplemented
            assert!(f.returns.len() <= 1);
            if f.generics.len() != generics.len() {
                return Err(format!(
                    "Wrong number of generic params calling {} (got {}, expected {})",
                    &f.id.value,
                    generics.len(),
                    f.generics.len()
                ));
            }
            if f.parameters.len() != args.len() {
                return Err(format!(
                    "Wrong nimber of arguments calling {} (got {}, expected {})",
                    &f.id.value,
                    args.len(),
                    f.parameters.len()
                ));
            }

            let f = f.clone();
            self.file_stack_push(f_path);
            self.generics_stack_push(generics);
            self.ret_ty_stack_push::<IS_CNST>(&f)?;

            // XXX(unimpl) multi-return unimplemented
            let ret_ty = f
                .returns
                .first()
                .map(|r| self.type_impl_::<IS_CNST>(r))
                .transpose()?;
            let ret_ty = if IS_CNST {
                self.cvar_enter_function();
                ret_ty
            } else {
                self.circ_enter_fn(f_name, ret_ty);
                None
            };

            for (p, a) in f.parameters.into_iter().zip(args) {
                let ty = self.type_impl_::<IS_CNST>(&p.ty)?;
                if IS_CNST {
                    self.cvar_declare_init(p.id.value, &ty, a)?;
                } else {
                    self.circ_declare_init(p.id.value, ty, Val::Term(a))
                        .map_err(|e| format!("{e}"))?;
                }
            }

            for s in &f.statements {
                self.stmt_impl_::<IS_CNST>(s)?;
            }

            let ret = if IS_CNST {
                self.cvar_exit_function();
                self.crets_pop()
            } else {
                self.circ_exit_fn()
                    .map(|a| a.unwrap_term())
                    .unwrap_or_else(|| z_bool_lit(false))
            };

            self.ret_ty_stack_pop();
            self.generics_stack_pop();
            self.file_stack_pop();

            if IS_CNST {
                let ret_ty = ret_ty.unwrap_or(Ty::Bool);
                if ret.type_() != &ret_ty {
                    return Err(format!(
                        "Return type mismatch: expected {}, got {}",
                        ret_ty,
                        ret.type_()
                    ));
                }
            }

            self.maybe_garbage_collect();
            Ok(ret)
        }
    }

    fn maybe_garbage_collect(&self) {
        let est = self.gc_depth_estimate.get();
        let cur = self.file_stack_depth();
        if GC_INC * cur < est {
            if maybe_garbage_collect() {
                // we ran the GC and it did something; increase depth at which we run gc by 1 call
                self.gc_depth_estimate.set(est + GC_INC);
            } else {
                // otherwise, decrease depth at which we run gc by one call
                self.gc_depth_estimate.set(est.saturating_sub(GC_INC));
            }
        } else {
            // we didn't try to run the GC; just gradually increase the depth at which we'll run the gc
            let est_inc = (GC_INC * cur - est) / GC_INC;
            self.gc_depth_estimate.set(est + 1 + est_inc);
        }
    }

    fn const_entry_fn(&self, n: &str, mut input_scalar_values: FxHashMap<String, Value>) -> T {
        debug!("Const entry: {}", n);
        let (f_file, f_name) = self.deref_import(n);
        if let Some(f) = self.functions.get(&f_file).and_then(|m| m.get(&f_name)) {
            if !f.generics.is_empty() {
                panic!("const_entry_fn cannot be called on a generic function")
            }

            let mut args = Vec::new();
            for p in &f.parameters {
                let name = &p.id.value;
                let ty = self.type_(&p.ty);
                let value = interp::extract(name, &ty, &mut input_scalar_values)
                    .unwrap_or_else(|e| self.err(format!("Error: {e}"), &p.span));
                args.push(value);
            }

            if !input_scalar_values.is_empty() {
                let unused_input_list = input_scalar_values
                    .keys()
                    .map(|s| s.as_str())
                    .collect::<Vec<_>>()
                    .as_slice()
                    .join(", ");
                self.err(format!("Ununused inputs {unused_input_list}"), &f.span);
            }

            self.function_call_impl_::<true>(args, &[][..], None, f_file, f_name)
                .unwrap_or_else(|e| panic!("const_entry_fn failed: {}", e))
        } else {
            panic!(
                "No function '{:?}//{}' attempting const_entry_fn",
                &f_file, &f_name
            )
        }
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
        let mut persistent_arrays: Vec<String> = Vec::new();
        for p in f.parameters.iter() {
            let ty = self.type_(&p.ty);
            debug!("Entry param: {}: {}", p.id.value, ty);
            let md = self.interpret_array_md(&p.array_metadata);
            let vis = self.interpret_visibility(&p.visibility);
            let r = self.circ_declare_input(p.id.value.clone(), &ty, vis, None, false, &md);
            let unwrapped = self.unwrap(r, &p.span);
            if let Some(md_some) = md {
                match md_some {
                    ArrayParamMetadata::Committed => {
                        info!(
                            "Input committed array of type {} in {:?}",
                            ty,
                            self.file_stack.borrow().last().unwrap()
                        );
                        persistent_arrays.push(p.id.value.clone());
                    }
                    ArrayParamMetadata::Transcript => {
                        self.mark_array_as_transcript(&p.id.value, unwrapped);
                    }
                }
            }
        }
        for s in &f.statements {
            self.unwrap(self.stmt_impl_::<false>(s), s.span());
        }
        for a in persistent_arrays {
            let term = self
                .circ_get_value(Loc::local(a.clone()))
                .unwrap()
                .unwrap_term()
                .term;
            trace!("End persistent_array {a}, {}", term);
            self.circ.borrow_mut().end_persistent_array(&a, term);
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
                    let ret_val = r.unwrap_term();
                    let ret_var_val = self
                        .circ_declare_input(
                            name,
                            ty,
                            ZVis::Public,
                            Some(ret_val.clone()),
                            false,
                            &None,
                        )
                        .expect("circ_declare return");
                    let ret_eq = eq(ret_val, ret_var_val).unwrap().term;
                    let mut assertions = std::mem::take(&mut *self.assertions.borrow_mut());
                    let to_assert = if assertions.is_empty() {
                        ret_eq
                    } else {
                        assertions.push(ret_eq);
                        term(AND, assertions)
                    };
                    debug!("Assertion: {}", to_assert);
                    self.circ.borrow_mut().assert(to_assert);
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
                    self.circ
                        .borrow()
                        .cir_ctx()
                        .cs
                        .borrow_mut()
                        .outputs
                        .push(cmp);
                }
            }
        }
    }
    fn interpret_array_md(
        &self,
        md: &Option<ast::ArrayParamMetadata<'ast>>,
    ) -> Option<ArrayParamMetadata> {
        match md {
            Some(ast::ArrayParamMetadata::Committed(_)) => Some(ArrayParamMetadata::Committed),
            Some(ast::ArrayParamMetadata::Transcript(_)) => Some(ArrayParamMetadata::Transcript),
            None => None,
        }
    }

    fn interpret_visibility(&self, visibility: &Option<ast::Visibility<'ast>>) -> ZVis {
        match visibility {
            None | Some(ast::Visibility::Public(_)) => ZVis::Public,
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
                    ZVis::Private(PROVER_ID)
                }
                Mode::Mpc(n_parties) => {
                    let num_str = private
                        .number
                        .as_ref()
                        .unwrap_or_else(|| self.err("No party number", &private.span));
                    let num_val = num_str.value[1..num_str.value.len() - 1]
                        .parse::<u8>()
                        .unwrap_or_else(|e| {
                            self.err(format!("Bad party number: {e}"), &private.span)
                        });
                    if num_val <= n_parties {
                        ZVis::Private(num_val - 1)
                    } else {
                        self.err(
                            format!(
                                "Party number {num_val} greater than the number of parties ({n_parties})"
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
        self.import_map
            .get(self.file_stack.borrow().last().unwrap())
    }

    fn deref_import(&self, s: &str) -> (PathBuf, String) {
        // import map is flattened, so we only need to chase through at most one indirection
        self.cur_import_map()
            .and_then(|m| m.get(s))
            .cloned()
            .unwrap_or_else(|| (self.cur_path(), s.to_string()))
    }

    fn generic_lookup_(&self, i: &str) -> Option<T> {
        self.generics_stack
            .borrow()
            .last()
            .and_then(|m| m.get(i))
            .cloned()
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

    fn identifier_impl_<const IS_CNST: bool>(
        &self,
        i: &ast::IdentifierExpression<'ast>,
    ) -> Result<T, String> {
        match self
            .generic_lookup_(&i.value)
            .or_else(|| self.const_lookup_(&i.value).cloned())
        {
            Some(v) => Ok(v),
            None if IS_CNST => self.cvar_lookup(&i.value).ok_or_else(|| {
                format!(
                    "Undefined const identifier {} in {}",
                    &i.value,
                    self.cur_path().canonicalize().unwrap().to_string_lossy()
                )
            }),
            _ => match self
                .circ_get_value(Loc::local(i.value.clone()))
                .map_err(|e| format!("{e}"))?
            {
                Val::Term(t) => Ok(t),
                _ => Err(format!("Non-Term identifier {}", &i.value)),
            },
        }
    }

    fn const_isize_impl_<const IS_CNST: bool>(
        &self,
        e: &ast::Expression<'ast>,
    ) -> Result<isize, String> {
        const_int(self.expr_impl_::<IS_CNST>(e)?)?
            .to_isize()
            .ok_or_else(|| "Constant integer outside isize range".to_string())
    }

    fn const_usize_impl_<const IS_CNST: bool>(
        &self,
        e: &ast::Expression<'ast>,
    ) -> Result<usize, String> {
        const_int(self.expr_impl_::<IS_CNST>(e)?)?
            .to_usize()
            .ok_or_else(|| "Constant integer outside usize range".to_string())
    }

    fn const_usize_(&self, e: &ast::Expression<'ast>) -> Result<usize, String> {
        self.const_usize_impl_::<true>(e)
    }

    fn array_access_impl_<const IS_CNST: bool>(
        &self,
        acc: &ast::ArrayAccess<'ast>,
        val: T,
    ) -> Result<T, String> {
        match &acc.expression {
            ast::RangeOrExpression::Expression(e) => {
                array_select(val, self.expr_impl_::<IS_CNST>(e)?)
            }
            ast::RangeOrExpression::Range(r) => {
                // XXX(unimpl) Range expressions must be constant!
                let s = r
                    .from
                    .as_ref()
                    .map(|s| self.const_usize_impl_::<IS_CNST>(&s.0))
                    .transpose()?;
                let e =
                    r.to.as_ref()
                        .map(|s| self.const_usize_impl_::<IS_CNST>(&s.0))
                        .transpose()?;
                slice(val, s, e)
            }
        }
    }

    // XXX(rsw) make Result<T, (String, Span)> to give more precise error messages?
    fn expr_impl_<const IS_CNST: bool>(&self, e: &ast::Expression<'ast>) -> Result<T, String> {
        if IS_CNST {
            debug!("Const expr: {}", e.span().as_str());
        } else {
            debug!("Expr: {}", e.span().as_str());
        }

        match e {
            ast::Expression::Ternary(u) => {
                match self.expr_impl_::<true>(&u.first).ok().and_then(const_bool) {
                    Some(true) => self.expr_impl_::<IS_CNST>(&u.second),
                    Some(false) => self.expr_impl_::<IS_CNST>(&u.third),
                    None if IS_CNST => Err("ternary condition not const bool".to_string()),
                    _ => {
                        let c = self.expr_impl_::<false>(&u.first)?;
                        let cbool = bool(c.clone())?;
                        self.circ_enter_condition(cbool.clone());
                        let a = self.expr_impl_::<false>(&u.second)?;
                        self.circ_exit_condition();
                        self.circ_enter_condition(term![NOT; cbool]);
                        let b = self.expr_impl_::<false>(&u.third)?;
                        self.circ_exit_condition();
                        cond(c, a, b)
                    }
                }
            }
            ast::Expression::Binary(b) => {
                let left = self.expr_impl_::<IS_CNST>(&b.left)?;
                let right = self.expr_impl_::<IS_CNST>(&b.right)?;
                let op = self.bin_op(&b.op);
                op(left, right)
            }
            ast::Expression::Unary(u) => {
                let arg = self.expr_impl_::<IS_CNST>(&u.expression)?;
                let op = self.unary_op(&u.op);
                op(arg)
            }
            ast::Expression::Identifier(i) => self.identifier_impl_::<IS_CNST>(i),
            ast::Expression::Literal(l) => self.literal_(l),
            ast::Expression::InlineArray(ia) => {
                let mut avals = Vec::with_capacity(ia.expressions.len());
                ia.expressions
                    .iter()
                    .try_for_each::<_, Result<_, String>>(|ee| match ee {
                        ast::SpreadOrExpression::Expression(eee) => {
                            avals.push(self.expr_impl_::<IS_CNST>(eee)?);
                            Ok(())
                        }
                        ast::SpreadOrExpression::Spread(s) => {
                            avals.append(
                                &mut self.expr_impl_::<IS_CNST>(&s.expression)?.unwrap_array()?,
                            );
                            Ok(())
                        }
                    })?;
                T::new_array(avals)
            }
            ast::Expression::ArrayInitializer(ai) => {
                let val = self.expr_impl_::<IS_CNST>(&ai.value)?;
                let num = self.const_usize_impl_::<IS_CNST>(&ai.count)?;
                fill_array(val, num)
            }
            ast::Expression::Postfix(p) => {
                // assume no functions in arrays, etc.
                assert!(!p.accesses.is_empty());
                let (val, accs) = if let Some(ast::Access::Call(c)) = p.accesses.first() {
                    let (f_path, f_name) = self.deref_import(&p.id.value);
                    let exp_ty = self.lhs_ty_take().and_then(|ty| {
                        if p.accesses.len() > 1 {
                            None
                        } else {
                            Some(ty)
                        }
                    });
                    let args = c
                        .arguments
                        .expressions
                        .iter()
                        .map(|e| self.expr_impl_::<IS_CNST>(e))
                        .collect::<Result<Vec<_>, _>>()?;
                    let egv = c
                        .explicit_generics
                        .as_ref()
                        .map(|eg| &eg.values[..])
                        .unwrap_or(&[][..]);
                    let res =
                        self.function_call_impl_::<IS_CNST>(args, egv, exp_ty, f_path, f_name)?;
                    (res, &p.accesses[1..])
                } else {
                    (self.identifier_impl_::<IS_CNST>(&p.id)?, &p.accesses[..])
                };
                accs.iter().try_fold(val, |v, acc| match acc {
                    ast::Access::Call(_) => {
                        Err("Function call in non-first-access position in expr".to_string())
                    }
                    ast::Access::Member(a) => field_select(&v, &a.id.value),
                    ast::Access::Select(s) => self.array_access_impl_::<IS_CNST>(s, v),
                })
            }
            ast::Expression::InlineStruct(u) => u
                .members
                .iter()
                .map(|m| {
                    self.expr_impl_::<IS_CNST>(&m.expression)
                        .map(|m_expr| (m.id.value.clone(), m_expr))
                })
                .collect::<Result<Vec<_>, String>>()
                .and_then(|members| Ok(T::new_struct(self.canon_struct(&u.ty.value)?, members))),
        }
        .and_then(|res| if IS_CNST { const_val(res) } else { Ok(res) })
        .map_err(|err| format!("{}; context:\n{}", err, span_to_string(e.span())))
    }

    fn canon_struct(&self, id: &str) -> Result<String, String> {
        match self
            .get_struct_or_type(id)
            .ok_or_else(|| format!("No such struct or type {id} canonicalizing InlineStruct"))?
            .0
        {
            Ok(_) => Ok(id.to_string()),
            Err(t) => match &t.ty {
                ast::Type::Struct(s) => self.canon_struct(&s.id.value),
                _ => Err(format!("Found non-Struct canonicalizing struct {id}")),
            },
        }
    }

    fn ret_impl_<const IS_CNST: bool>(&self, ret: Option<T>) -> Result<(), CircError> {
        if IS_CNST {
            self.crets_push(ret.unwrap_or_else(|| z_bool_lit(false)));
            Ok(())
        } else {
            self.circ_return_(ret)
        }
    }

    fn decl_impl_<const IS_CNST: bool>(&self, name: String, ty: &Ty) -> Result<(), String> {
        if IS_CNST {
            self.cvar_declare(name, ty)
        } else {
            self.circ
                .borrow_mut()
                .declare_uninit(name, ty)
                .map_err(|e| format!("{e}"))
        }
    }

    fn declare_init_impl_<const IS_CNST: bool>(
        &self,
        name: String,
        ty: Ty,
        val: T,
    ) -> Result<(), String> {
        if IS_CNST {
            self.cvar_declare_init(name, &ty, val)
        } else {
            self.circ_declare_init(name, ty, Val::Term(val))
                .map(|_| ())
                .map_err(|e| format!("{e}"))
        }
    }

    fn stmt_impl_<const IS_CNST: bool>(&self, s: &ast::Statement<'ast>) -> Result<(), String> {
        if IS_CNST {
            debug!("Const stmt: {}", s.span().as_str());
        } else {
            debug!("Stmt: {}", s.span().as_str());
        }

        match s {
            ast::Statement::Return(r) => {
                // XXX(unimpl) multi-return unimplemented
                assert!(r.expressions.len() <= 1);
                if let Some(e) = r.expressions.first() {
                    self.set_lhs_ty_ret(r);
                    let ret = self.expr_impl_::<IS_CNST>(e)?;
                    self.ret_impl_::<IS_CNST>(Some(ret))
                } else {
                    self.ret_impl_::<IS_CNST>(None)
                }
                .map_err(|e| format!("{e}"))
            }
            ast::Statement::Assertion(e) => {
                match self.expr_impl_::<true>(&e.expression).and_then(|v| {
                    const_bool(v)
                        .ok_or_else(|| "interpreting expr as const bool failed".to_string())
                }) {
                    Ok(true) => Ok(()),
                    Ok(false) => Err(format!(
                        "Const assert failed: {} at\n{}",
                        e.message
                            .as_ref()
                            .map(|m| m.value.as_ref())
                            .unwrap_or("(no error message given)"),
                        span_to_string(e.expression.span()),
                    )),
                    Err(err) if IS_CNST => Err(format!(
                        "Const assert expression eval failed {} at\n{}",
                        err,
                        span_to_string(e.expression.span()),
                    )),
                    _ => {
                        let b = bool(self.expr_impl_::<false>(&e.expression)?)?;
                        self.assert(b);
                        Ok(())
                    }
                }
            }
            ast::Statement::CondStore(e) => {
                if IS_CNST {
                    return Err("cannot evaluate a const CondStore".into());
                }
                let a = self.identifier_impl_::<IS_CNST>(&e.array)?;
                let i = self.expr_impl_::<IS_CNST>(&e.index)?;
                let v = self.expr_impl_::<IS_CNST>(&e.value)?;
                let c = self.expr_impl_::<IS_CNST>(&e.condition)?;
                let cbool = bool(c)?;
                let new = mut_array_store(a, i, v, cbool)?;
                trace!("Cond store: {} to {}", e.array.value, new);
                self.circ_assign(Loc::local(e.array.value.clone()), Val::Term(new))
                    .map_err(|e| format!("{e}"))?;
                Ok(())
            }
            ast::Statement::Iteration(i) => {
                let ty = self.type_impl_::<IS_CNST>(&i.ty)?;
                let ival_cons = match ty {
                    Ty::Field => T::new_field,
                    Ty::Uint(8) => T::new_u8,
                    Ty::Uint(16) => T::new_u16,
                    Ty::Uint(32) => T::new_u32,
                    Ty::Uint(64) => T::new_u64,
                    _ => {
                        return Err(format!(
                            "Iteration variable must be Field or Uint, got {ty}"
                        ));
                    }
                };
                // XXX(rsw) CHECK does this work if the range includes negative numbers?
                let s = self.const_isize_impl_::<IS_CNST>(&i.from)?;
                let e = self.const_isize_impl_::<IS_CNST>(&i.to)?;
                let v_name = i.index.value.clone();
                self.enter_scope_impl_::<IS_CNST>();
                self.decl_impl_::<IS_CNST>(v_name, &ty)?;
                for j in s..e {
                    self.enter_scope_impl_::<IS_CNST>();
                    self.assign_impl_::<IS_CNST>(&i.index.value, &[][..], ival_cons(j), false)?;
                    for s in &i.statements {
                        self.stmt_impl_::<IS_CNST>(s)?;
                    }
                    self.exit_scope_impl_::<IS_CNST>();
                }
                self.exit_scope_impl_::<IS_CNST>();
                Ok(())
            }
            ast::Statement::Definition(d) => {
                // XXX(unimpl) multi-assignment unimplemented
                assert!(d.lhs.len() <= 1);

                self.set_lhs_ty_defn::<IS_CNST>(d)?;
                let e = self.expr_impl_::<IS_CNST>(&d.expression)?;

                if let Some(l) = d.lhs.first() {
                    match l {
                        ast::TypedIdentifierOrAssignee::Assignee(l) => {
                            let strict = match &d.expression {
                                ast::Expression::Unary(u) => {
                                    matches!(&u.op, ast::UnaryOperator::Strict(_))
                                }
                                _ => false,
                            };
                            self.assign_impl_::<IS_CNST>(&l.id.value, &l.accesses[..], e, strict)
                        }
                        ast::TypedIdentifierOrAssignee::TypedIdentifier(l) => {
                            let decl_ty = self.type_impl_::<IS_CNST>(&l.ty)?;
                            let ty = e.type_();
                            if &decl_ty != ty {
                                return Err(format!(
                                    "Assignment type mismatch: {decl_ty} annotated vs {ty} actual",
                                ));
                            }
                            self.declare_init_impl_::<IS_CNST>(
                                l.identifier.value.clone(),
                                decl_ty,
                                e,
                            )?;
                            let md = self.interpret_array_md(&l.array_metadata);
                            if let Some(ArrayParamMetadata::Transcript) = md {
                                let value = self
                                    .circ_get_value(Loc::local(l.identifier.value.clone()))
                                    .map_err(|e| format!("{e}"))?
                                    .unwrap_term();
                                self.mark_array_as_transcript(&l.identifier.value, value);
                            }
                            Ok(())
                        }
                    }
                } else {
                    warn!("Statement with no LHS!");
                    Ok(())
                }
            }
        }
        .map_err(|err| format!("{}; context:\n{}", err, span_to_string(s.span())))
    }

    fn set_lhs_ty_defn<const IS_CNST: bool>(
        &self,
        d: &ast::DefinitionStatement<'ast>,
    ) -> Result<(), String> {
        assert!(self.lhs_ty.borrow().is_none()); // starting from nothing...
        if let ast::Expression::Postfix(pfe) = &d.expression {
            if matches!(pfe.accesses.first(), Some(ast::Access::Call(_))) {
                let ty = d
                    .lhs
                    .first()
                    .map(|ty| self.lhs_type::<IS_CNST>(ty))
                    .transpose()?;
                self.lhs_ty_put(ty);
            }
        }
        Ok(())
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
                let t = self.identifier_impl_::<IS_CNST>(&a.id)?;
                a.accesses.iter().try_fold(t.ty, |ty, acc| match acc {
                    ast::AssigneeAccess::Select(aa) => match ty {
                        Ty::Array(sz, ity) => match &aa.expression {
                            ast::RangeOrExpression::Expression(_) => Ok(*ity),
                            ast::RangeOrExpression::Range(_) => Ok(Ty::Array(sz, ity)),
                        },
                        ty => Err(format!("Attempted array access on non-Array type {ty}")),
                    },
                    ast::AssigneeAccess::Member(sa) => match ty {
                        Ty::Struct(nm, map) => map
                            .search(&sa.id.value)
                            .map(|r| r.1.clone())
                            .ok_or_else(|| {
                                format!("No such member {} of struct {nm}", &sa.id.value)
                            }),
                        ty => Err(format!("Attempted member access on non-Struct type {ty}")),
                    },
                })
            }
            TypedIdentifier(t) => self.type_impl_::<IS_CNST>(&t.ty),
        }
    }

    fn lhs_ty_put(&self, lhs_ty: Option<Ty>) {
        self.lhs_ty.replace(lhs_ty);
    }

    fn lhs_ty_take(&self) -> Option<Ty> {
        self.lhs_ty.borrow_mut().take()
    }

    fn enter_scope_impl_<const IS_CNST: bool>(&self) {
        if IS_CNST {
            self.cvar_enter_scope()
        } else {
            self.circ_enter_scope()
        }
    }

    fn cvar_enter_scope(&self) {
        assert!(!self.cvars_stack.borrow().is_empty());
        self.cvars_stack
            .borrow_mut()
            .last_mut()
            .unwrap()
            .push(HashMap::new());
    }

    fn exit_scope_impl_<const IS_CNST: bool>(&self) {
        if IS_CNST {
            self.cvar_exit_scope()
        } else {
            self.circ_exit_scope()
        }
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

    fn cvar_assign(&self, name: &str, val: T) -> Result<(), String> {
        assert!(!self.cvars_stack.borrow().last().unwrap().is_empty());
        self.cvars_stack
            .borrow_mut()
            .last_mut()
            .unwrap()
            .iter_mut()
            .rev()
            .find_map(|v| v.get_mut(name))
            .map(|old_val| {
                *old_val = val;
            })
            .ok_or_else(|| format!("Const assign failed: no variable {name} in scope"))
    }

    fn cvar_declare_init(&self, name: String, ty: &Ty, val: T) -> Result<(), String> {
        assert!(!self.cvars_stack.borrow().last().unwrap().is_empty());
        if val.type_() != ty {
            return Err(format!(
                "Const decl_init: {} type mismatch: expected {}, got {}",
                name,
                ty,
                val.type_()
            ));
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

    fn ret_ty_stack_push<const IS_CNST: bool>(
        &self,
        fn_def: &ast::FunctionDefinition<'ast>,
    ) -> Result<(), String> {
        let ty = fn_def
            .returns
            .first()
            .map(|ty| self.type_impl_::<IS_CNST>(ty))
            .transpose()?
            .unwrap_or(Ty::Bool);
        self.ret_ty_stack.borrow_mut().push(ty);
        Ok(())
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
        if self
            .cur_import_map()
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
        let ctype = self.unwrap(self.type_impl_::<true>(&c.ty), type_span(&c.ty));
        // handle literal type inference using declared type
        v.replace(Some(ctype));
        v.visit_expression(&mut c.expression)
            .unwrap_or_else(|e| self.err(e.0, &c.span));

        // evaluate the expression and check the resulting type
        let value = self
            .expr_impl_::<true>(&c.expression)
            .unwrap_or_else(|e| self.err(e, c.expression.span()));
        let ctype = v.replace(None).unwrap();
        if &ctype != value.type_() {
            self.err(
                format!(
                    "Type mismatch in constant definition: expected {:?}, got {:?}",
                    ctype,
                    value.type_()
                ),
                &c.span,
            );
        }

        if let Some(ast::ArrayParamMetadata::Transcript(_)) = &c.array_metadata {
            if !value.type_().is_array() {
                self.err(format!("Non-array transcript {}", &c.id.value), &c.span);
            }
            self.mark_array_as_transcript(&c.id.value, value.clone());
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
        self.unwrap(self.type_impl_::<false>(t), type_span(t))
    }

    fn type_impl_<const IS_CNST: bool>(&self, t: &ast::Type<'ast>) -> Result<Ty, String> {
        if IS_CNST {
            debug!("Const type: {:?}", t);
        } else {
            debug!("Type: {:?}", t);
        }
        fn lift<'ast>(t: &ast::BasicOrStructType<'ast>) -> ast::Type<'ast> {
            match t {
                ast::BasicOrStructType::Basic(b) => ast::Type::Basic(b.clone()),
                ast::BasicOrStructType::Struct(b) => ast::Type::Struct(b.clone()),
            }
        }
        match t {
            ast::Type::Basic(ast::BasicType::U8(_)) => Ok(Ty::Uint(8)),
            ast::Type::Basic(ast::BasicType::U16(_)) => Ok(Ty::Uint(16)),
            ast::Type::Basic(ast::BasicType::U32(_)) => Ok(Ty::Uint(32)),
            ast::Type::Basic(ast::BasicType::U64(_)) => Ok(Ty::Uint(64)),
            ast::Type::Basic(ast::BasicType::Boolean(_)) => Ok(Ty::Bool),
            ast::Type::Basic(ast::BasicType::Field(_)) => Ok(Ty::Field),
            ast::Type::Array(a) => {
                let b = self.type_impl_::<IS_CNST>(&lift(&a.ty));
                a.dimensions
                    .iter()
                    .rev()
                    .map(|d| self.const_usize_impl_::<IS_CNST>(d))
                    .fold(b, |b, d| Ok(Ty::Array(d?, Box::new(b?))))
            }
            ast::Type::Struct(s) => {
                let (def, path) = self.get_struct_or_type(&s.id.value).ok_or_else(|| {
                    format!(
                        "No such struct {} (did you bring it into scope?)",
                        &s.id.value
                    )
                })?;
                let generics = match def {
                    Ok(sdef) => &sdef.generics,
                    Err(tdef) => &tdef.generics,
                };
                let g_len = generics.len();
                let egv = s
                    .explicit_generics
                    .as_ref()
                    .map(|eg| eg.values.as_ref())
                    .unwrap_or(&[][..]);
                let generics = self.egvs_impl_::<IS_CNST>(egv, generics.clone())?;
                if generics.len() != g_len {
                    return Err(format!(
                        "Struct {} is not monomorphized or wrong number of generic parameters",
                        &s.id.value
                    ));
                }
                self.file_stack_push(path);
                self.generics_stack_push(generics);
                let ty = match def {
                    Ok(sdef) => Ty::new_struct(
                        sdef.id.value.clone(),
                        sdef.fields
                            .iter()
                            .map::<Result<_, String>, _>(|f| {
                                Ok((f.id.value.clone(), self.type_impl_::<IS_CNST>(&f.ty)?))
                            })
                            .collect::<Result<Vec<_>, _>>()?,
                    ),
                    Err(tdef) => self.type_impl_::<IS_CNST>(&tdef.ty)?,
                };
                self.generics_stack_pop();
                self.file_stack_pop();
                Ok(ty)
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
                    assert!(!src_names.is_empty());
                    let abs_src_path = self.stdlib.canonicalize(&self.cur_dir(), src_path.as_str());
                    debug!(
                        "Import of {:?} from {} as {:?}",
                        src_names,
                        abs_src_path.display(),
                        dst_names
                    );
                    src_names.into_iter().zip(dst_names).for_each(|(sn, dn)| {
                        if imap.contains_key(&dn) {
                            self.err(format!("Import {dn} redeclared"), i_span);
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
            self.structs_and_tys.insert(p.clone(), HashMap::new());
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

                        if self
                            .structs_and_tys
                            .get_mut(self.file_stack.borrow().last().unwrap())
                            .unwrap()
                            .insert(s.id.value.clone(), Ok(s_ast))
                            .is_some()
                        {
                            self.err(
                                format!("Struct {} defined over existing name", &s.id.value),
                                &s.span,
                            );
                        }
                    }
                    ast::SymbolDeclaration::Type(t) => {
                        debug!(
                            "processing decl: type definition {} in {}",
                            t.id.value,
                            p.display()
                        );
                        let mut t_ast = t.clone();

                        // rewrite literals in ArrayTypes
                        clr.visit_type_definition(&mut t_ast)
                            .unwrap_or_else(|e| self.err(e.0, &t.span));

                        if self
                            .structs_and_tys
                            .get_mut(self.file_stack.borrow().last().unwrap())
                            .unwrap()
                            .insert(t.id.value.clone(), Err(t_ast))
                            .is_some()
                        {
                            self.err(
                                format!("Type {} defined over existing name", &t.id.value),
                                &t.span,
                            );
                        }
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
                                format!(
                                    "Functions must return exactly 1 value; {} returns {}",
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

                        if self
                            .functions
                            .get_mut(self.file_stack.borrow().last().unwrap())
                            .unwrap()
                            .insert(f.id.value.clone(), f_ast)
                            .is_some()
                        {
                            self.err(format!("Function {} redefined", &f.id.value), &f.span);
                        }
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

    fn get_struct_or_type(
        &self,
        struct_id: &str,
    ) -> Option<(
        Result<&ast::StructDefinition<'ast>, &ast::TypeDefinition<'ast>>,
        PathBuf,
    )> {
        let (s_path, s_name) = self.deref_import(struct_id);
        self.structs_and_tys
            .get(&s_path)
            .and_then(|m| m.get(&s_name))
            .map(|m| (m.as_ref(), s_path))
    }

    fn assert(&self, asrt: Term) {
        debug_assert!(matches!(check(&asrt), Sort::Bool));
        if self.isolate_asserts {
            let path = self.circ_condition();
            self.assertions
                .borrow_mut()
                .push(term![IMPLIES; path, asrt]);
        } else {
            self.assertions.borrow_mut().push(asrt);
        }
    }

    fn mark_array_as_transcript(&self, name: &str, array: T) {
        info!(
            "Transcript array {} of type {} in {:?}",
            name,
            array.ty,
            self.file_stack.borrow().last().unwrap()
        );
        self.circ
            .borrow()
            .cir_ctx()
            .cs
            .borrow_mut()
            .ram_arrays
            .insert(array.term);
    }

    /*** circify wrapper functions (hides RefCell) ***/

    fn circ_enter_condition(&self, cond: Term) {
        if self.isolate_asserts {
            self.circ.borrow_mut().enter_condition(cond).unwrap();
        }
    }

    fn circ_exit_condition(&self) {
        if self.isolate_asserts {
            self.circ.borrow_mut().exit_condition()
        }
    }

    fn circ_condition(&self) -> Term {
        self.circ.borrow().condition()
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

    fn circ_declare_input(
        &self,
        name: String,
        ty: &Ty,
        vis: ZVis,
        precomputed_value: Option<T>,
        mangle_name: bool,
        md: &Option<ArrayParamMetadata>,
    ) -> Result<T, CircError> {
        if let Some(ArrayParamMetadata::Committed) = md {
            let size = match ty {
                Ty::Array(size, _) => *size,
                _ => panic!(),
            };
            Ok(self.circ.borrow_mut().start_persistent_array(
                &name,
                size,
                default_field(),
                crate::front::proof::PROVER_ID,
            ))
        } else {
            self.circ.borrow_mut().declare_input(
                name,
                ty,
                match vis {
                    ZVis::Public => None,
                    ZVis::Private(i) => Some(i),
                },
                precomputed_value,
                mangle_name,
            )
        }
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
}

fn span_to_string(span: &ast::Span) -> String {
    span.lines().collect::<String>()
}

fn type_span<'ast, 'a>(ty: &'a ast::Type<'ast>) -> &'a ast::Span<'ast> {
    use ast::BasicType::*;
    use ast::Type::*;
    match ty {
        Array(a) => &a.span,
        Struct(s) => &s.span,
        Basic(b) => match b {
            Field(f) => &f.span,
            Boolean(b) => &b.span,
            U8(u) => &u.span,
            U16(u) => &u.span,
            U32(u) => &u.span,
            U64(u) => &u.span,
        },
    }
}
