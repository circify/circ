//! The C front-end

mod ast_utils;
mod parser;
mod term;
mod types;

use super::FrontEnd;
use crate::circify::{Circify, Loc, Val};
use crate::circify::mem::AllocId;
use crate::front::c::ast_utils::*;
use crate::front::c::term::*;
use crate::front::c::types::*;
use crate::ir::proof::ConstraintMetadata;
use crate::ir::term::*;
use lang_c::ast::*;
use lang_c::span::Node;
use log::debug;

// use std::collections::HashMap;
use std::fmt::{self, Display, Formatter};
use std::path::PathBuf;

const PUBLIC_VIS: Option<PartyId> = None;

/// Inputs to the C compiler
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
}

impl Display for Mode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            &Mode::Mpc(n) => write!(f, "{}-pc", n),
            &Mode::Proof => write!(f, "proof"),
            &Mode::Opt => write!(f, "opt"),
        }
    }
}

/// The C front-end. Implements [FrontEnd].
pub struct C;

impl FrontEnd for C {
    type Inputs = Inputs;
    fn gen(i: Inputs) -> Computation {
        let parser = parser::CParser::new();
        let p = parser.parse_file(&i.file).unwrap();
        let mut g = CGen::new(i.inputs, i.mode, p.unit);
        g.gen();
        g.circ.consume().borrow().clone()
    }
}

struct CGen {
    circ: Circify<Ct>,
    mode: Mode,
    tu: TranslationUnit,
}

enum CLoc {
    Var(Loc),
    Idx(Box<CLoc>, CTerm),
}

impl CLoc {
    fn loc(&self) -> &Loc {
        match self {
            CLoc::Var(l) => l,
            CLoc::Idx(i, _) => i.loc(),
        }
    }
}

impl CGen {
    fn new(inputs: Option<PathBuf>, mode: Mode, tu: TranslationUnit) -> Self {
        let this = Self {
            circ: Circify::new(Ct::new(inputs.map(|i| parser::parse_inputs(i)))),
            mode,
            tu,
        };
        this.circ
            .cir_ctx()
            .cs
            .borrow_mut()
            .metadata
            .add_prover_and_verifier();
        this
    }

    /// Unwrap a result of an error and abort
    fn err<E: Display>(&self, e: E) -> ! {
        println!("Error: {}", e);
        std::process::exit(1)
    }

    /// Unwrap result of a computation
    fn unwrap<CTerm, E: Display>(&self, r: Result<CTerm, E>) -> CTerm {
        r.unwrap_or_else(|e| self.err(e))
    }

    // fn apply_lval_mod(&mut self, base: CTerm, loc: CLoc, val: CTerm) -> Result<CTerm, String> {
    //     match loc {
    //         CLoc::Var(_) => Ok(val),
    //         CLoc::Idx(inner_loc, idx) => {
    //             let old_inner = array_select(base.clone(), idx.clone())?;
    //             let new_inner = self.apply_lval_mod(old_inner, *inner_loc, val)?;
    //             array_store(base, idx, new_inner)
    //         }
    //     }
    // }

    // fn mod_lval(&mut self, l: CLoc, t: CTerm) -> Result<(), String> {
    //     let var = l.loc().clone();
    //     let old = self
    //         .circ
    //         .get_value(var.clone())
    //         .map_err(|e| format!("{}", e))?
    //         .unwrap_term();
    //     let new = self.apply_lval_mod(old, l, t)?;
    //     self.circ
    //         .assign(var, Val::Term(new))
    //         .map_err(|e| format!("{}", e))
    //         .map(|_| ())
    // }

    // fn lval(&mut self, expr: Box<Node<Expression>>) -> CLoc {
    //     match expr.node {
    //         Expression::Identifier(_) => {
    //             let base_name = name_from_ident(&expr.node);
    //             CLoc::Var(Loc::local(base_name))
    //         }
    //         Expression::BinaryOperator(node) => {
    //             let bin_op = node.node;
    //             match bin_op.operator.node {
    //                 BinaryOperator::Index => {
    //                     let base_name = name_from_ident(&bin_op.lhs.node);
    //                     let idx = self.gen_expr(bin_op.rhs.node);
    //                     CLoc::Idx(Box::new(CLoc::Var(Loc::local(base_name))), idx)
    //                 }
    //                 _ => unimplemented!("Invalid left hand value"),
    //             }
    //         }
    //         _ => unimplemented!("Invalid left hand value"),
    //     }
    // }

    /// Interpret the party association of input parameters 
    pub fn interpret_visibility(&mut self, ext: &DeclarationSpecifier) -> Option<PartyId> {
        if let DeclarationSpecifier::Extension(nodes) = ext {
            assert!(nodes.len() == 1);
            let node = nodes.first().unwrap();
            if let Extension::Attribute(attr) = &node.node {
                let name = &attr.name;
                return match name.node.as_str() {
                    "public" => PUBLIC_VIS.clone(),
                    "private" => match self.mode {
                        Mode::Mpc(n_parties) => {
                            assert!(attr.arguments.len() == 1);
                            let arg = attr.arguments.first().unwrap();
                            let cons = self.gen_expr(arg.node.clone());
                            let num_val = const_int(cons).ok()?;
                            if num_val <= n_parties {
                                Some(num_val.to_u8()?)
                            } else {
                                self.err(format!(
                                    "Party number {} greater than the number of parties ({})",
                                    num_val, n_parties
                                ))
                            }
                        }
                        _ => unimplemented!("Mode {} is not supported.", self.mode),
                    },
                    _ => panic!("Unknown visibility: {:#?}", name),
                };
            }
        }
        panic!("Bad visibility declaration.");
    }

    fn const_(&self, c: Constant) -> CTerm {
        match c {
            // TODO: move const integer function out to separate function
            Constant::Integer(i) => CTerm {
                term: CTermData::CInt(true, 32, bv_lit(i.number.parse::<i32>().unwrap(), 32)),
                udef: false,
            },
            _ => unimplemented!("Constant {:#?} hasn't been implemented", c),
        }
    }

    fn get_bin_op(&self, op: BinaryOperator) -> fn(CTerm, CTerm) -> Result<CTerm, String> {
        match op {
            BinaryOperator::Plus => add,
            BinaryOperator::Minus => sub,
            BinaryOperator::Multiply => mul,
            BinaryOperator::Equals => eq,
            BinaryOperator::Greater => ugt,
            BinaryOperator::GreaterOrEqual => uge,
            BinaryOperator::Less => ult,
            BinaryOperator::LessOrEqual => ule,
            BinaryOperator::BitwiseAnd => bitand,
            BinaryOperator::BitwiseOr => bitor,
            BinaryOperator::BitwiseXor => bitxor,
            BinaryOperator::LogicalAnd => and,
            BinaryOperator::LogicalOr => or,
            // BinaryOperator::Index => array_select,
            _ => unimplemented!("BinaryOperator {:#?} hasn't been implemented", op),
        }
    }

    fn gen_expr(&mut self, expr: Expression) -> CTerm {
        let res = match expr.clone() {
            Expression::Identifier(node) => Ok(self
                .unwrap(self.circ.get_value(Loc::local(node.node.name.clone())))
                .unwrap_term()),
            Expression::Constant(node) => Ok(self.const_(node.node)),
            Expression::BinaryOperator(node) => {
                let bin_op = node.node;
                match bin_op.operator.node {
                    BinaryOperator::Assign => {
                        unimplemented!()
                        // let e = self.gen_expr(bin_op.rhs.node);
                        // let lval = self.lval(bin_op.lhs);
                        // let mod_res = self.mod_lval(lval, e.clone());
                        // self.unwrap(mod_res);
                        // Ok(e)
                    }
                    _ => {
                        let f = self.get_bin_op(bin_op.operator.node);
                        let a = self.gen_expr(bin_op.lhs.node);
                        let b = self.gen_expr(bin_op.rhs.node);
                        f(a, b)
                    }
                }
            }
            Expression::Cast(node) => {
                let CastExpression {
                    type_name,
                    expression,
                } = node.node;
                let to_ty = s_type_(type_name.node.specifiers);
                let expr = self.gen_expr(expression.node);
                Ok(cast(to_ty, expr))
            }
            _ => unimplemented!("Expr {:#?} hasn't been implemented", expr),
        };
        self.unwrap(res)
    }

    fn gen_init(&mut self, derived_ty: Ty, init: Initializer) -> CTerm {
        match init {
            Initializer::Expression(e) => self.gen_expr(e.node),
            Initializer::List(l) => {
                // TODO: check length of values to initialized number
                let mut values: Vec<CTerm> = Vec::new();

                for li in l.clone() {
                    let expr = self.gen_init(inner_ty(derived_ty.clone()), li.node.initializer.node);
                    println!("expr: {:#?}", expr);
                    values.push(expr)
                }
                let mut mem = self.circ.cir_ctx().mem.borrow_mut();
                let id = mem.zero_allocate(values.len(), 32, num_bits(derived_ty.clone()));

                // println!("alloc id: {}", id);
                // println!("value type: {}", values.first().unwrap().term.type_());
                // println!("derived type: {}", derived_ty);

                // TODO: place values in AllocID location
                // CALL STORE! 


                // let arr = new_array(id, values);
                // arr.unwrap()

                // HASKELL CODE:
                // (Array _ innerTy, CInitList is _) -> do
                // values <- forM is $ \(_, i) -> genInit innerTy i
                // let cvals = map (ssaValAsTerm "Cannot put refs in arrays") values
                // liftMem $ Base <$> cArrayLit innerTy cvals

                // cArrayLit :: Type.Type -> [CTerm] -> Mem CTerm
                // cArrayLit ty vals = do
                // forM_ vals $ \v -> unless (cType v == ty) $ error $ unwords
                //     ["Type mismatch in cArrayLit:", show ty, "vs", show $ cType v]
                // let bvs = map (serialize . term) vals
                // id <- Mem.stackAllocCons 32 bvs
                // return $ mkCTerm (CArray (Type.Array (Just $ length vals) ty) id)
                //    (Ty.BoolLit False)

                unimplemented!();

                CTerm {
                    term: CTermData::CArray(derived_ty, id), 
                    udef: false,
                }
            }
        }
    }

    fn gen_decl(&mut self, decl: Declaration) {
        let decl_info = get_decl_info(decl.clone());
        let d = decl.declarators.first().unwrap().node.clone();
        let base_ty: Ty = decl_info.ty;
        let derived = &d.declarator.node.derived;
        let derived_ty = derived_type_(base_ty, derived.to_vec());
        let expr: CTerm;
        if let Some(init) = d.initializer {
            expr = self.gen_init(derived_ty.clone(), init.node);
        } else {
            expr = derived_ty.default();
        }

        let res = self.circ.declare_init(
            decl_info.name,
            derived_ty.clone(),
            Val::Term(cast(Some(derived_ty.clone()), expr)),
        );
        self.unwrap(res);
    }
   

    fn gen_stmt(&mut self, stmt: Statement) {
        match stmt {
            Statement::Compound(nodes) => {
                for node in nodes {
                    match node.node {
                        BlockItem::Declaration(decl) => {
                            self.gen_decl(decl.node);
                        }
                        BlockItem::Statement(stmt) => {
                            self.gen_stmt(stmt.node);
                        }
                        BlockItem::StaticAssert(_sa) => {
                            unimplemented!("Static Assert not supported yet")
                        }
                    }
                }
            }
            Statement::If(node) => {
                let cond = self.gen_expr(node.node.condition.node);
                // TODO Cast to boolean for condition ;
                let t_res = self.circ.enter_condition(cond.term.term());
                self.unwrap(t_res);
                self.gen_stmt(node.node.then_statement.node);
                self.circ.exit_condition();

                if let Some(f_cond) = node.node.else_statement {
                    let f_res = self.circ.enter_condition(term!(Op::Not; cond.term.term()));
                    self.unwrap(f_res);
                    self.gen_stmt(f_cond.node);
                    self.circ.exit_condition();
                }
            }
            Statement::Return(ret) => {
                match ret {
                    Some(expr) => {
                        let ret = self.gen_expr(expr.node);
                        let ret_res = self.circ.return_(Some(ret));
                        self.unwrap(ret_res);
                    }
                    None => {
                        let ret_res = self.circ.return_(None);
                        self.unwrap(ret_res);
                    }
                };
            }
            Statement::Expression(expr) => {
                let e = expr.unwrap().node;
                self.gen_expr(e);
            }
            _ => unimplemented!("Statement {:#?} hasn't been implemented", stmt),
        }
    }

    fn gen(&mut self) {
        let TranslationUnit(nodes) = self.tu.clone();
        for n in nodes.iter() {
            match n.node {
                ExternalDeclaration::Declaration(ref decl) => {
                    debug!("{:#?}", decl);
                }
                ExternalDeclaration::FunctionDefinition(ref fn_def) => {
                    debug!("{:#?}", fn_def.node.clone());
                    println!("{:#?}", fn_def.node.clone());
                    let fn_info = ast_utils::get_fn_info(&fn_def.node);
                    self.circ.enter_fn(fn_info.name.to_owned(), fn_info.ret_ty);
                    for arg in fn_info.args.iter() {
                        let p = &arg.specifiers[0];
                        let vis = self.interpret_visibility(&p.node);
                        let ty = d_type_(arg.specifiers[1..].to_vec());
                        let d = &arg.declarator.as_ref().unwrap().node;
                        let name = name_from_decl(d);
                        let r = self.circ.declare(name.clone(), &ty.unwrap(), true, vis);
                        self.unwrap(r);
                    }
                    self.gen_stmt(fn_info.body.clone());
                    if let Some(r) = self.circ.exit_fn() {
                        let ret_term = r.unwrap_term();
                        let ret_terms = ret_term.term.terms();
                        self.circ
                            .cir_ctx()
                            .cs
                            .borrow_mut()
                            .outputs
                            .extend(ret_terms);
                    }
                }
                _ => unimplemented!("Haven't implemented node: {:?}", n.node),
            }
        }
    }
}
