use crate::front::c::term::CTerm;
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

impl FnInfo {
    fn new(
        name: String,
        ret_ty: Option<Ty>,
        args: Vec<ParameterDeclaration>,
        body: Statement,
    ) -> Self {
        Self {
            name,
            ret_ty,
            args,
            body,
        }
    }
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

pub fn type_(t: &DeclarationSpecifier) -> Option<Ty> {
    if let DeclarationSpecifier::TypeSpecifier(ty) = t {
        return match ty.node {
            TypeSpecifier::Int => Some(Ty::Uint(32)),
            TypeSpecifier::Bool => Some(Ty::Bool),
            TypeSpecifier::Void => None,
            _ => unimplemented!("Type {:#?} not implemented yet.", ty),
        };
    }
    panic!(
        "DeclarationSpecifier does not contain TypeSpecifier: {:#?}",
        t
    );
}

pub fn get_decl_info(decl: Declaration) -> DeclInfo {
    let spec = &decl.specifiers;
    assert!(spec.len() == 1);
    let ty = type_(&spec.first().unwrap().node).unwrap();

    assert!(decl.declarators.len() == 1);
    let decls = decl.declarators.first().unwrap().node.clone();
    let name = name_from_decl(&decls.declarator.node);

    DeclInfo { name: name, ty: ty }
}

pub fn s_type_(t: &SpecifierQualifier) -> Option<Ty> {
    if let SpecifierQualifier::TypeSpecifier(ty) = t {
        return match ty.node {
            TypeSpecifier::Int => Some(Ty::Uint(32)),
            TypeSpecifier::Bool => Some(Ty::Bool),
            TypeSpecifier::Void => None,
            _ => unimplemented!("Type {:#?} not implemented yet.", ty),
        };
    }
    panic!(
        "SpecifierQualifier does not contain TypeSpecifier: {:#?}",
        t
    );
}

pub fn cast_type(ty_name: TypeName) -> Option<Ty> {
    let spec = &ty_name.specifiers;
    assert!(spec.len() == 1);
    s_type_(&spec.first().unwrap().node)
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
    type_(&spec.first().unwrap().node)
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
