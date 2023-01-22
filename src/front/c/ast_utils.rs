use crate::front::c::types::Ty;
use crate::front::c::Expression::Identifier;
use lang_c::ast::*;
use std::fmt::{self, Display, Formatter};

use crate::front::Mode;
use crate::front::PartyId;
use crate::front::PROVER_VIS;
use crate::front::PUBLIC_VIS;

#[derive(Clone)]
pub struct FnInfo {
    pub name: String,
    pub ret_ty: Option<Ty>,
    pub params: Vec<ParamInfo>,
    pub body: Statement,
}

#[derive(Clone)]
pub struct DeclInfo {
    pub name: String,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct ParamInfo {
    pub name: String,
    pub ty: Ty,
    pub vis: Option<PartyId>,
}

pub struct ConstIteration {
    pub val: i32,
}

impl Display for FnInfo {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "name: {},\nargs: {:#?},\nbody: {:#?}",
            self.name, self.params, self.body
        )
    }
}

pub fn name_from_expr(expr: &Expression) -> String {
    match &expr {
        Identifier(i) => i.node.name.to_string(),
        _ => {
            panic!("Expression is not an identifier '{:#?}'", expr);
        }
    }
}

pub fn name_from_decl(decl: &Declarator) -> String {
    match decl.kind.node {
        DeclaratorKind::Identifier(ref id) => id.node.name.to_string(),
        _ => panic!("Identifier not found: {:?}", decl),
    }
}

pub fn compress_type(ts: Vec<Option<Ty>>) -> Option<Ty> {
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

pub fn name_from_func(fn_def: &FunctionDefinition) -> String {
    let decl = &fn_def.declarator.node;
    name_from_decl(decl)
}

pub fn args_from_func(fn_def: &FunctionDefinition) -> Option<Vec<ParameterDeclaration>> {
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

pub fn body_from_func(fn_def: &FunctionDefinition) -> Statement {
    fn_def.statement.node.clone()
}

pub fn flatten_inits(init: &Initializer) -> Vec<&Initializer> {
    let mut inits: Vec<&Initializer> = Vec::new();
    match init {
        Initializer::List(l) => {
            for li in l {
                let inner_inits = flatten_inits(&li.node.initializer.node);
                inits.extend(inner_inits.iter().cloned());
            }
        }
        _ => inits.push(init),
    }
    inits
}

/// Interpret the party association of input parameters
pub fn interpret_visibility(ext: &DeclarationSpecifier, mode: Mode) -> Option<PartyId> {
    if let DeclarationSpecifier::Extension(nodes) = ext {
        assert!(nodes.len() == 1);
        let node = nodes.first().unwrap();
        if let Extension::Attribute(attr) = &node.node {
            let name = &attr.name;
            return match name.node.as_str() {
                "public" => PUBLIC_VIS,
                "private" => match mode {
                    Mode::Mpc(n_parties) => {
                        assert!(attr.arguments.len() == 1);
                        let arg = attr.arguments.first().unwrap();
                        let mut num_val: u8 = u8::MAX;
                        if let Expression::Constant(num) = &arg.node {
                            if let Constant::Integer(i) = &num.node {
                                num_val = i.number.parse::<u8>().unwrap();
                            }
                        }
                        if num_val <= n_parties {
                            Some(num_val)
                        } else {
                            panic!(
                                "Party number {} greater than the number of parties ({})",
                                num_val, n_parties
                            )
                        }
                    }
                    Mode::Proof => PROVER_VIS,
                    _ => unimplemented!("Mode {} is not supported.", mode),
                },
                _ => panic!("Unknown visibility: {:#?}", name),
            };
        }
    }
    panic!("Bad visibility declaration.");
}
