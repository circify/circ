use crate::front::c::Expression::Identifier;
use crate::front::{c::types::Ty, field_list::FieldList};
use lang_c::ast::*;
use lang_c::span::Node;
use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};

#[derive(Clone)]
pub struct FnInfo {
    pub name: String,
    pub ret_ty: Option<Ty>,
    pub args: Vec<ParameterDeclaration>,
    pub body: Statement,
}

#[derive(Clone)]
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

pub fn d_type_(ds: Vec<Node<DeclarationSpecifier>>, structs: &HashMap<String, Ty>) -> Option<Ty> {
    assert!(!ds.is_empty());
    let res: Vec<Option<Ty>> = ds
        .iter()
        .map(|d| match &d.node {
            DeclarationSpecifier::TypeSpecifier(t) => type_(t.node.clone(), structs),
            _ => unimplemented!("Unimplemented declaration type: {:#?}", d),
        })
        .collect();
    compress_type(res)
}

pub fn s_type_(ss: Vec<Node<SpecifierQualifier>>, structs: &HashMap<String, Ty>) -> Option<Ty> {
    assert!(!ss.is_empty());
    let res: Vec<Option<Ty>> = ss
        .iter()
        .map(|s| match &s.node {
            SpecifierQualifier::TypeSpecifier(t) => type_(t.node.clone(), structs),
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

fn type_(t: TypeSpecifier, structs: &HashMap<String, Ty>) -> Option<Ty> {
    return match t {
        TypeSpecifier::Int => Some(Ty::Int(true, 32)),
        TypeSpecifier::Unsigned => Some(Ty::Int(false, 32)), // Some(Ty::Int(false, 32)),
        TypeSpecifier::Bool => Some(Ty::Bool),
        TypeSpecifier::Void => None,
        TypeSpecifier::Struct(s) => {
            let StructType {
                kind: _kind,
                identifier,
                declarations,
            } = s.node;
            let name = identifier.unwrap().node.name;
            let mut fs: Vec<(String, Ty)> = Vec::new();
            match declarations {
                Some(decls) => {
                    for d in decls.into_iter() {
                        match d.node {
                            StructDeclaration::Field(f) => {
                                let field_type = s_type_(f.node.specifiers.clone(), structs);
                                let names = f.node.declarators.iter().map(|d| {
                                    name_from_decl(&d.node.declarator.clone().unwrap().node)
                                });
                                fs.extend(names.zip(field_type));
                            }
                            StructDeclaration::StaticAssert(_a) => {
                                unimplemented!("Struct static assert not implemented!");
                            }
                        }
                    }
                }
                None => {}
            }
            Some(Ty::Struct(name, FieldList::new(fs)))
        }
        _ => unimplemented!("Type {:#?} not implemented yet.", t),
    };
}

pub fn get_decl_info(decl: Declaration, structs: &mut HashMap<String, Ty>) -> Vec<DeclInfo> {
    let ty = d_type_(decl.specifiers, structs).unwrap();

    // Save struct declarations to the cache
    let new_ty: Ty = match ty.clone() {
        Ty::Struct(name, fs) => {
            if fs.clone().len() > 0 {
                structs.insert(name.to_string(), ty.clone());
                ty
            } else {
                structs.get(&name).unwrap().clone()
            }
        }
        _ => ty,
    };

    let mut res: Vec<DeclInfo> = Vec::new();
    for node in decl.declarators.into_iter() {
        let name = name_from_decl(&node.node.declarator.node);
        let d = DeclInfo {
            name,
            ty: new_ty.clone(),
        };
        res.push(d);
    }
    res
}

pub fn get_fn_info(fn_def: &FunctionDefinition, structs: &HashMap<String, Ty>) -> FnInfo {
    let name = name_from_func(fn_def);
    let ret_ty = ret_ty_from_func(fn_def, structs);
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

fn ret_ty_from_func(fn_def: &FunctionDefinition, structs: &HashMap<String, Ty>) -> Option<Ty> {
    d_type_(fn_def.specifiers.clone(), structs)
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
