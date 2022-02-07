use crate::front::c::types::Ty;
use crate::front::c::Expression::Identifier;
use lang_c::ast::*;
use lang_c::span::Node;
use std::fmt::{self, Display, Formatter};

#[derive(Clone)]
pub struct FnInfo {
    pub name: String,
    pub ret_ty: Option<Ty>,
    pub args: Vec<ParameterDeclaration>,
    pub body: Statement,
}

pub struct DeclInfo {
    pub name: String,
    pub ty: Ty,
}

pub struct ConstIteration {
    pub val: i32,
}

impl Display for FnInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "name: {},\nargs: {:#?},\nbody: {:#?}",
            self.name, self.args, self.body
        )
    }
}

pub fn name_from_expr(node: Node<Expression>) -> String {
    if let Identifier(i) = node.node {
        i.node.name.clone()
    } else {
        panic!("Expression is not an identifier '{:#?}'", node.node);
    }
}

pub fn name_from_decl(decl: &Declarator) -> String {
    match decl.kind.node {
        DeclaratorKind::Identifier(ref id) => id.node.name.clone(),
        _ => panic!("Identifier not found: {:?}", decl),
    }
}

pub fn d_type_(ds: Vec<Node<DeclarationSpecifier>>) -> Option<Ty> {
    assert!(!ds.is_empty());
    let res: Vec<Option<Ty>> = ds
        .iter()
        .map(|d| match &d.node {
            DeclarationSpecifier::TypeSpecifier(t) => type_(t.node.clone()),
            _ => unimplemented!("Unimplemented declaration type: {:#?}", d),
        })
        .collect();
    compress_type(res)
}

pub fn s_type_(ss: Vec<Node<SpecifierQualifier>>) -> Option<Ty> {
    assert!(!ss.is_empty());
    let res: Vec<Option<Ty>> = ss
        .iter()
        .map(|s| match &s.node {
            SpecifierQualifier::TypeSpecifier(t) => type_(t.node.clone()),
            _ => unimplemented!("Unimplemented specifier type: {:#?}", s),
        })
        .collect();
    compress_type(res)
}

fn compress_type(ts: Vec<Option<Ty>>) -> Option<Ty> {
    if ts.len() == 1 {
        return ts.first().unwrap().clone();
    } else {
        let mut signed: bool = true;
        let mut _void: bool = false;
        let mut bit_len: usize = 0;
        for (i, t) in ts.iter().enumerate() {
            // TODO: void pointers?
            match t.as_ref().unwrap() {
                Ty::Int(s, w) => {
                    if !*s && i > 0 {
                        panic!("unsigned type defined later: {:#?}", ts);
                    }
                    signed &= *s;
                    if !*s {
                        bit_len += *w;
                    }
                }
                _ => unimplemented!("Current type not supported: {:#?}", ts),
            }
        }
        Some(Ty::Int(signed, bit_len))
    }
}

fn type_(t: TypeSpecifier) -> Option<Ty> {
    return match t {
        TypeSpecifier::Int => Some(Ty::Int(true, 32)),
        TypeSpecifier::Unsigned => Some(Ty::Int(false, 32)), // Some(Ty::Int(false, 32)),
        TypeSpecifier::Bool => Some(Ty::Bool),
        TypeSpecifier::Void => None,
        _ => unimplemented!("Type {:#?} not implemented yet.", t),
    };
}

pub fn get_decl_info(decl: Declaration) -> DeclInfo {
    // TODO: support more than 1 declaration
    let ty = d_type_(decl.specifiers).unwrap();
    assert!(decl.declarators.len() == 1);
    let decls = decl.declarators.first().unwrap().node.clone();
    let name = name_from_decl(&decls.declarator.node);
    DeclInfo { name, ty }
}

pub fn get_fn_info(fn_def: &FunctionDefinition) -> FnInfo {
    let name = name_from_func(fn_def);
    let ret_ty = ret_ty_from_func(fn_def);
    let args = args_from_func(fn_def).unwrap();
    let body = body_from_func(fn_def);

    FnInfo {
        name,
        ret_ty,
        args: args.to_vec(),
        body,
    }
}

fn name_from_func(fn_def: &FunctionDefinition) -> String {
    let decl = &fn_def.declarator.node;
    name_from_decl(decl)
}

fn ret_ty_from_func(fn_def: &FunctionDefinition) -> Option<Ty> {
    d_type_(fn_def.specifiers.clone())
}

fn args_from_func(fn_def: &FunctionDefinition) -> Option<Vec<ParameterDeclaration>> {
    let dec = &fn_def.declarator.node;
    dec.derived.iter().find_map(|d| match d.node {
        DerivedDeclarator::Function(ref fn_dec) => {
            let args = fn_dec
                .node
                .parameters
                .iter()
                .map(|a| a.node.clone())
                .collect::<Vec<ParameterDeclaration>>();
            Some(args)
        }
        _ => None,
    })
}

fn body_from_func(fn_def: &FunctionDefinition) -> Statement {
    fn_def.statement.node.clone()
}
