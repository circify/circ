use crate::front::c::types::Ty;
use crate::front::c::Expression::Identifier;
use lang_c::ast::*;
use std::fmt::{self, Display, Formatter};

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

impl Display for FnInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "name: {},\nargs: {:#?},\nbody: {:#?}",
            self.name, self.args, self.body
        )
    }
}

pub fn name_from_decl(decl: &Declarator) -> String {
    match decl.kind.node {
        DeclaratorKind::Identifier(ref id) => id.node.name.clone(),
        _ => panic!("Identifier not found: {:?}", decl),
    }
}

pub fn name_from_ident(ident: &Expression) -> String {
    match ident {
        Identifier(i) => i.node.name.clone(),
        _ => panic!("Identifier not found: {:?}", ident),
    }
}

pub fn d_type_(d: DeclarationSpecifier) -> Option<Ty> {
    match d {
        DeclarationSpecifier::TypeSpecifier(t) => type_(t.node),
        _ => unimplemented!("Unimplemented declaration type: {:#?}", d)
    }
}

pub fn s_type_(s: SpecifierQualifier) -> Option<Ty> {
    match s {
        SpecifierQualifier::TypeSpecifier(t) => type_(t.node),
        _ => unimplemented!("Unimplemented Specifier type: {:#?}", s)
    }
}

fn type_(t: TypeSpecifier) -> Option<Ty> {
    return match t {
        TypeSpecifier::Int => Some(Ty::Int(true, 32)),
        TypeSpecifier::Bool => Some(Ty::Bool),
        TypeSpecifier::Void => None,
        _ => unimplemented!("Type {:#?} not implemented yet.", t),
    };
}

pub fn get_decl_info(decl: Declaration) -> DeclInfo {
    let spec = &decl.specifiers;
    assert!(spec.len() == 1);
    let ty = d_type_(spec.first().unwrap().node.clone()).unwrap();
    assert!(decl.declarators.len() == 1);
    let decls = decl.declarators.first().unwrap().node.clone();
    let name = name_from_decl(&decls.declarator.node);
    DeclInfo { name: name, ty: ty }
}

pub fn cast_type(ty_name: TypeName) -> Option<Ty> {
    let spec = &ty_name.specifiers;
    assert!(spec.len() == 1);
    s_type_(spec.first().unwrap().node.clone())
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
        body: body,
    }
}

fn name_from_func(fn_def: &FunctionDefinition) -> String {
    let decl = &fn_def.declarator.node;
    name_from_decl(decl)
}

fn ret_ty_from_func(fn_def: &FunctionDefinition) -> Option<Ty> {
    let spec = &fn_def.specifiers;
    assert!(spec.len() == 1);
    d_type_(spec.first().unwrap().node.clone())
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
