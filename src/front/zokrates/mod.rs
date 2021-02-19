pub mod parser;
pub mod term;

use super::FrontEnd;
use crate::circify::{Circify, Loc};
use crate::ir::term::*;
use log::debug;
use rug::Integer;
use std::collections::HashMap;
use std::fmt::Display;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use zokrates_pest_ast as ast;

use term::*;

pub struct Inputs {
    pub file: PathBuf,
    pub inputs: Option<PathBuf>,
}

pub struct Zokrates;

impl FrontEnd for Zokrates {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Constraints {
        let loader = parser::ZLoad::new();
        let asts = loader.load(&i.file);
        let mut g = ZGen::new(i.inputs, asts);
        g.visit_files();
        unimplemented!()
    }
}

pub struct ZGen<'ast> {
    circ: Circify<ZoKrates>,
    stdlib: parser::ZStdLib,
    asts: HashMap<PathBuf, ast::File<'ast>>,
    file_stack: Vec<PathBuf>,
    functions: HashMap<(PathBuf, String), ast::Function<'ast>>,
    import_map: HashMap<(PathBuf, String), (PathBuf, String)>,
}

enum ZLoc {
    Var(Loc),
    Member(Box<ZLoc>, String),
    Idx(Box<ZLoc>, T),
}

fn unwrap_sp<T, E: Display>(r: Result<T, E>, s: &ast::Span) -> T {
    r.unwrap_or_else(|e| {
        println!("Error: {}\nAt:\n{}", e, s.as_str());
        panic!("Error")
    })
}

impl<'ast> ZGen<'ast> {
    fn new(inputs: Option<PathBuf>, asts: HashMap<PathBuf, ast::File<'ast>>) -> Self {
        Self {
            circ: Circify::new(ZoKrates::new(inputs.map(|i| parser::parse_inputs(i)))),
            asts,
            stdlib: parser::ZStdLib::new(),
            file_stack: vec![],
            functions: HashMap::new(),
            import_map: HashMap::new(),
        }
    }

    fn builtin_call(fn_name: &str, mut args: Vec<T>) -> Result<T, String> {
        match fn_name {
            "to_bits" if args.len() == 1 => u32_to_bits(args.pop().unwrap()),
            "from_bits" if args.len() == 1 => u32_from_bits(args.pop().unwrap()),
            "unpack" if args.len() == 1 => field_to_bits(args.pop().unwrap()),
            _ => Err(format!("Unknown builtin '{}'", fn_name)),
        }
    }

    fn stmt(&mut self, s: &ast::Statement<'ast>) {
        unimplemented!()
    }
    fn const_(&mut self, e: &ast::ConstantExpression<'ast>) -> T {
        match e {
            ast::ConstantExpression::U8(u) => T::Uint(8, bv_lit(u8::from_str_radix(&u.value[2..], 16).unwrap(), 8)),
            ast::ConstantExpression::U16(u) => T::Uint(16, bv_lit(u16::from_str_radix(&u.value[2..], 16).unwrap(), 16)),
            ast::ConstantExpression::U32(u) => T::Uint(32, bv_lit(u32::from_str_radix(&u.value[2..], 16).unwrap(), 32)),
            ast::ConstantExpression::DecimalNumber(u) => T::Field(pf_lit(Integer::from_str_radix(&u.value, 10).unwrap())),
            ast::ConstantExpression::BooleanLiteral(u) => T::Bool(leaf_term(Op::Const(Value::Bool(bool::from_str(&u.value).unwrap())))),
        }

    }
    fn expr(&mut self, e: &ast::Expression<'ast>) -> T {
        match e {
            ast::Expression::Constant(c) => self.const_(c),
            _ => unimplemented!(),
        }
    }
    fn array_lit_elem(&mut self, e: &ast::Expression<'ast>) -> Vec<T> {
        unimplemented!()
    }
    fn entry_fn(&mut self, f: &ast::Function<'ast>) {}
    fn cur_path(&self) -> &Path {
        self.file_stack.last().unwrap()
    }

    fn struct_(&mut self, s: &ast::StructDefinition<'ast>) {}

    fn const_int(&mut self, e: &ast::Expression<'ast>) -> Integer {
        unwrap_sp(const_int(self.expr(e)), e.span())
    }

    fn type_(&mut self, t: &ast::Type<'ast>) -> Ty {
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
            ast::Type::Basic(ast::BasicType::Boolean(_)) => Ty::Bool,
            ast::Type::Basic(ast::BasicType::Field(_)) => Ty::Field,
            ast::Type::Array(a) => {
                let b = self.type_(&lift(&a.ty));
                a.dimensions
                    .iter()
                    .map(|d| self.const_int(d).to_usize().unwrap())
                    .fold(b, |b, d| Ty::Array(d, Box::new(b)))
            }
            ast::Type::Struct(s) => self.circ.get_type(&s.id.value).clone(),
        }
    }

    fn visit_files(&mut self) {
        let t = std::mem::take(&mut self.asts);
        for (p, f) in &t {
            self.file_stack.push(p.to_owned());
            for func in &f.functions {
                debug!("fn {} in {}", func.id.value, self.cur_path().display());
                self.functions.insert(
                    (self.cur_path().to_owned(), func.id.value.clone()),
                    func.clone(),
                );
            }
            for i in &f.imports {
                let (src_path, src_name, dst_name_opt) = match i {
                    ast::ImportDirective::Main(m) => (
                        m.source.value.clone(),
                        "main".to_owned(),
                        m.alias.as_ref().map(|a| a.value.clone()),
                    ),
                    ast::ImportDirective::From(m) => (
                        m.source.value.clone(),
                        m.symbol.value.clone(),
                        m.alias.as_ref().map(|a| a.value.clone()),
                    ),
                };
                let dst_name = dst_name_opt.unwrap_or_else(|| src_name.clone());
                let abs_src_path = self.stdlib.canonicalize(self.cur_path(), src_path.as_str());
                debug!(
                    "Import of {} from {} as {}",
                    src_name,
                    abs_src_path.display(),
                    dst_name
                );
                self.import_map.insert(
                    (self.cur_path().to_path_buf(), dst_name),
                    (abs_src_path, src_name),
                );
            }
            for s in &f.structs {
                let ty = Ty::Struct(
                    s.id.value.clone(),
                    s.fields
                        .clone()
                        .iter()
                        .map(|f| (f.id.value.clone(), self.type_(&f.ty)))
                        .collect(),
                );
                debug!("struct {}", s.id.value);
                self.circ.def_type(&s.id.value, ty);
            }
            self.file_stack.pop();
        }
        self.asts = t;
    }
}
