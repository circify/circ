use lang_c::ast::{
    BlockItem,
    DeclaratorKind, 
    DerivedDeclarator,
    FunctionDefinition, 
    ParameterDeclaration, 
    Statement
};
use lang_c::span::Node;

use std::fmt::{self, Display, Formatter};


pub struct FnInfo {
    name: String, 
    args: Vec<ParameterDeclaration>,
    body: Statement,
}       

impl FnInfo {
    fn new(name: String, args: Vec<ParameterDeclaration>, body: Statement) -> Self {
        Self { name, args, body }
    }
}

impl Display for FnInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "name: {},\nargs: {:#?},\nbody: {:#?}", self.name, self.args, self.body)
    }
}

pub fn get_fn_info(fn_def: &FunctionDefinition) -> FnInfo {
    let name = name_from_func(fn_def);
    let args = args_from_func(fn_def).unwrap();
    let body = body_from_func(fn_def);

    FnInfo {
        name,
        args: args.to_vec(),
        body: body,
    }
}


fn name_from_func(fn_def: &FunctionDefinition) -> String {
    let dec = &fn_def.declarator.node;
    match dec.kind.node {
        DeclaratorKind::Identifier(ref id) => id.node.name.clone(),
        _ => panic!("Function name not found: {:?}", dec),
    }
}

fn args_from_func(fn_def: &FunctionDefinition) -> Option<Vec<ParameterDeclaration>> {
    let dec = &fn_def.declarator.node;
    dec.derived.iter().find_map(|d| match d.node {
        DerivedDeclarator::Function(ref fn_dec) => {
            let args = fn_dec.node.parameters.iter().map(|a| {
                a.node.clone()
            }).collect::<Vec<ParameterDeclaration>>();
            Some(args)
        }
        _ => None
    })
}

fn body_from_func(fn_def: &FunctionDefinition) -> Statement {
    fn_def.statement.node.clone()
}