//! Datalog parser
#![allow(missing_docs)]
#![allow(clippy::clone_on_copy)]

use pest::error::Error;
use pest::Parser;
use pest_derive::Parser;

// Issue with the proc macro
/// Pest parser for our datalog
#[derive(Parser)]
#[grammar = "front/datalog/grammar.pest"] // relative to src
struct MyParser;

pub mod ast {
    use super::Rule;
    use from_pest::ConversionError;
    use from_pest::FromPest;
    use from_pest::Void;
    use lazy_static::lazy_static;
    use pest::iterators::{Pair, Pairs};
    use pest::pratt_parser::{Assoc, Op, PrattParser};
    pub use pest::Span;
    use pest_ast::FromPest;

    fn span_into_str(span: Span) -> &str {
        span.as_str()
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decimal_literal))]
    pub struct DecimalLiteral<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::boolean_literal))]
    pub struct BooleanLiteral<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::hex_literal))]
    pub struct HexLiteral<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::bin_literal))]
    pub struct BinLiteral<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::literal))]
    pub enum Literal<'ast> {
        DecimalLiteral(DecimalLiteral<'ast>),
        BooleanLiteral(BooleanLiteral<'ast>),
        BinLiteral(BinLiteral<'ast>),
        HexLiteral(HexLiteral<'ast>),
    }

    impl<'ast> Literal<'ast> {
        pub fn span(&self) -> &Span<'ast> {
            match self {
                Literal::DecimalLiteral(n) => &n.span,
                Literal::BooleanLiteral(c) => &c.span,
                Literal::BinLiteral(c) => &c.span,
                Literal::HexLiteral(c) => &c.span,
            }
        }
    }

    #[derive(Debug, PartialEq, Eq, FromPest, Clone)]
    #[pest_ast(rule(Rule::un_op))]
    pub enum UnaryOperator<'ast> {
        Not(Not<'ast>),
        BitNot(BitNot<'ast>),
        Neg(Neg<'ast>),
    }

    #[derive(Debug, PartialEq, Eq, FromPest, Clone)]
    #[pest_ast(rule(Rule::not))]
    pub struct Not<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }
    #[derive(Debug, PartialEq, Eq, FromPest, Clone)]
    #[pest_ast(rule(Rule::bitnot))]
    pub struct BitNot<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }
    #[derive(Debug, PartialEq, Eq, FromPest, Clone)]
    #[pest_ast(rule(Rule::neg))]
    pub struct Neg<'ast> {
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum BinaryOperator {
        BitXor,
        BitAnd,
        BitOr,
        RightShift,
        LeftShift,
        Or,
        And,
        Add,
        Sub,
        Mul,
        Div,
        Rem,
        Eq,
        Lt,
        Gt,
        Lte,
        Gte,
    }

    lazy_static! {
        static ref PREC_CLIMBER: PrattParser<Rule> = build_precedence_climber();
    }

    // based on https://docs.python.org/3/reference/expressions.html#operator-precedence
    fn build_precedence_climber() -> PrattParser<Rule> {
        PrattParser::new()
            .op(Op::infix(Rule::or, Assoc::Left))
            .op(Op::infix(Rule::and, Assoc::Left))
            .op(Op::infix(Rule::lt, Assoc::Left)
                | Op::infix(Rule::lte, Assoc::Left)
                | Op::infix(Rule::gt, Assoc::Left)
                | Op::infix(Rule::gte, Assoc::Left)
                | Op::infix(Rule::eq, Assoc::Left))
            .op(Op::infix(Rule::bitor, Assoc::Left))
            .op(Op::infix(Rule::bitxor, Assoc::Left))
            .op(Op::infix(Rule::bitand, Assoc::Left))
            .op(Op::infix(Rule::shl, Assoc::Left) | Op::infix(Rule::shr, Assoc::Left))
            .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
            .op(Op::infix(Rule::mul, Assoc::Left)
                | Op::infix(Rule::div, Assoc::Left)
                | Op::infix(Rule::urem, Assoc::Left))
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub enum Expression<'ast> {
        Binary(BinaryExpression<'ast>),
        Identifier(Ident<'ast>),
        Literal(Literal<'ast>),
        Call(CallExpression<'ast>),
        Access(AccessExpression<'ast>),
        Unary(UnaryExpression<'ast>),
        Paren(Box<Expression<'ast>>, Span<'ast>),
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::identifier))]
    pub struct Ident<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub value: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::call_expr))]
    pub struct CallExpression<'ast> {
        pub fn_name: Ident<'ast>,
        pub args: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::access_expr))]
    pub struct AccessExpression<'ast> {
        pub arr: Ident<'ast>,
        pub idxs: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, PartialEq, Eq, Clone)]
    pub struct BinaryExpression<'ast> {
        pub op: BinaryOperator,
        pub left: Box<Expression<'ast>>,
        pub right: Box<Expression<'ast>>,
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::unary_expression))]
    pub struct UnaryExpression<'ast> {
        pub op: UnaryOperator<'ast>,
        pub expression: Box<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    impl<'ast> Expression<'ast> {
        pub fn binary(
            op: BinaryOperator,
            left: Box<Expression<'ast>>,
            right: Box<Expression<'ast>>,
            span: Span<'ast>,
        ) -> Self {
            Expression::Binary(BinaryExpression {
                op,
                left,
                right,
                span,
            })
        }

        pub fn span(&self) -> &Span<'ast> {
            match self {
                Expression::Binary(b) => &b.span,
                Expression::Identifier(i) => &i.span,
                Expression::Literal(c) => c.span(),
                Expression::Unary(u) => &u.span,
                Expression::Call(u) => &u.span,
                Expression::Access(u) => &u.span,
                Expression::Paren(_, s) => s,
            }
        }
    }

    impl<'ast> FromPest<'ast> for Expression<'ast> {
        type Rule = Rule;
        type FatalError = Void;

        // We implement AST creation manually here for Expression
        // `pest` should yield an `expression` which we can generate AST with, based on precedence rules
        fn from_pest(pest: &mut Pairs<'ast, Rule>) -> Result<Self, ConversionError<Void>> {
            // get a clone to "try" to match
            let mut clone = pest.clone();
            // advance by one pair in the clone, if none error out, `pest` is still the original
            let pair = clone.next().ok_or(::from_pest::ConversionError::NoMatch)?;
            // this should be an expression
            match pair.as_rule() {
                Rule::expr => {
                    // we can replace `pest` with the clone we tried with and got pairs from to create the AST
                    *pest = clone;
                    Ok(*climb(pair))
                }
                _ => Err(ConversionError::NoMatch),
            }
        }
    }

    // Create an Expression from left and right terms and an operator
    // Precondition: `pair` MUST be a binary operator
    fn infix_rule<'ast>(
        lhs: Box<Expression<'ast>>,
        pair: Pair<'ast, Rule>,
        rhs: Box<Expression<'ast>>,
    ) -> Box<Expression<'ast>> {
        // a + b spans from the start of a to the end of b
        let (start, _) = lhs.span().clone().split();
        let (_, end) = rhs.span().clone().split();
        let span = start.span(&end);

        Box::new(match pair.as_rule() {
            Rule::add => Expression::binary(BinaryOperator::Add, lhs, rhs, span),
            Rule::sub => Expression::binary(BinaryOperator::Sub, lhs, rhs, span),
            Rule::mul => Expression::binary(BinaryOperator::Mul, lhs, rhs, span),
            Rule::div => Expression::binary(BinaryOperator::Div, lhs, rhs, span),
            Rule::urem => Expression::binary(BinaryOperator::Rem, lhs, rhs, span),
            Rule::eq => Expression::binary(BinaryOperator::Eq, lhs, rhs, span),
            Rule::lte => Expression::binary(BinaryOperator::Lte, lhs, rhs, span),
            Rule::lt => Expression::binary(BinaryOperator::Lt, lhs, rhs, span),
            Rule::gte => Expression::binary(BinaryOperator::Gte, lhs, rhs, span),
            Rule::gt => Expression::binary(BinaryOperator::Gt, lhs, rhs, span),
            Rule::or => Expression::binary(BinaryOperator::Or, lhs, rhs, span),
            Rule::and => Expression::binary(BinaryOperator::And, lhs, rhs, span),
            Rule::bitxor => Expression::binary(BinaryOperator::BitXor, lhs, rhs, span),
            Rule::bitand => Expression::binary(BinaryOperator::BitAnd, lhs, rhs, span),
            Rule::bitor => Expression::binary(BinaryOperator::BitOr, lhs, rhs, span),
            Rule::shr => Expression::binary(BinaryOperator::RightShift, lhs, rhs, span),
            Rule::shl => Expression::binary(BinaryOperator::LeftShift, lhs, rhs, span),
            _ => unreachable!(),
        })
    }

    // Create an Expression from an `expression`. `build_factor` turns each term into an `Expression` and `infix_rule` turns each (Expression, operator, Expression) into an Expression
    pub fn climb(pair: Pair<Rule>) -> Box<Expression> {
        PREC_CLIMBER
            .map_primary(build_factor)
            .map_infix(infix_rule)
            .parse(pair.into_inner())
    }

    // Create an Expression from a `term`.
    // Precondition: `pair` MUST be a term
    fn build_factor(pair: Pair<Rule>) -> Box<Expression> {
        //println!("pairs: {:#?}", pair);
        Box::new(match pair.as_rule() {
            Rule::term => {
                // clone the pair to peek into what we should create
                let clone = pair.clone();
                // define the child pair
                let next = clone.into_inner().next().unwrap();
                match next.as_rule() {
                    // this happens when we have an expression in parentheses: it needs to be processed as another sequence of terms and operators
                    Rule::paren_expr => Expression::Paren(
                        Box::new(
                            Expression::from_pest(
                                &mut pair.into_inner().next().unwrap().into_inner(),
                            )
                            .unwrap(),
                        ),
                        next.as_span(),
                    ),
                    Rule::literal => {
                        Expression::Literal(Literal::from_pest(&mut pair.into_inner()).unwrap())
                    }
                    Rule::identifier => {
                        Expression::Identifier(Ident::from_pest(&mut pair.into_inner()).unwrap())
                    }
                    Rule::unary_expression => {
                        let span = next.as_span();
                        let mut inner = next.into_inner();
                        let op = match inner.next().unwrap().as_rule() {
                            Rule::un_op => UnaryOperator::from_pest(
                                &mut pair.into_inner().next().unwrap().into_inner(),
                            )
                            .unwrap(),
                            r => unreachable!(
                                "`unary_expression` should yield `un_op`, found {:#?}",
                                r
                            ),
                        };
                        let expression = build_factor(inner.next().unwrap());
                        Expression::Unary(UnaryExpression {
                            op,
                            expression,
                            span,
                        })
                    }
                    Rule::call_expr => {
                        Expression::Call(CallExpression::from_pest(&mut pair.into_inner()).unwrap())
                    }
                    Rule::access_expr => Expression::Access(
                        AccessExpression::from_pest(&mut pair.into_inner()).unwrap(),
                    ),
                    r => unreachable!("expected `term`, found {:#?}", r),
                }
            }
            r => unreachable!(
                "`build_factor` can only be called on `term`, found {:#?}",
                r
            ),
        })
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_uint))]
    pub struct TypeUint<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub type_name: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_bool))]
    pub struct TypeBool<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub type_name: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty_field))]
    pub struct TypeField<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub type_name: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::base_ty))]
    pub enum BaseType<'ast> {
        Uint(TypeUint<'ast>),
        Field(TypeField<'ast>),
        Bool(TypeBool<'ast>),
    }

    impl<'ast> BaseType<'ast> {
        pub fn span(&self) -> &Span<'ast> {
            match self {
                BaseType::Uint(p) => &p.span,
                BaseType::Field(p) => &p.span,
                BaseType::Bool(p) => &p.span,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::ty))]
    pub struct Type<'ast> {
        pub base: BaseType<'ast>,
        pub array_sizes: Vec<DecimalLiteral<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::vis_public))]
    pub struct Public<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub type_name: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::vis_private))]
    pub struct Private<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub type_name: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::vis))]
    pub enum Visibility<'ast> {
        Public(Public<'ast>),
        Private(Private<'ast>),
    }

    impl<'ast> Visibility<'ast> {
        pub fn span(&self) -> &Span<'ast> {
            match self {
                Visibility::Private(p) => &p.span,
                Visibility::Public(p) => &p.span,
            }
        }
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::qual_ty))]
    pub struct QualType<'ast> {
        pub qualifier: Option<Visibility<'ast>>,
        pub ty: Type<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::decl))]
    pub struct Declaration<'ast> {
        pub ident: Ident<'ast>,
        pub ty: QualType<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::dec))]
    pub struct Decreasing<'ast> {
        #[pest_ast(outer(with(span_into_str)))]
        pub tok: &'ast str,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::fn_arg_decl))]
    pub struct ArgDeclaration<'ast> {
        pub dec: Option<Decreasing<'ast>>,
        pub ident: Ident<'ast>,
        pub ty: QualType<'ast>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::exist_prefix))]
    pub struct Existential<'ast> {
        pub declarations: Vec<Declaration<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::condition))]
    pub struct Condition<'ast> {
        pub existential: Option<Existential<'ast>>,
        pub exprs: Vec<Expression<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::rule))]
    pub struct Rule_<'ast> {
        pub name: Ident<'ast>,
        pub args: Vec<ArgDeclaration<'ast>>,
        pub conds: Vec<Condition<'ast>>,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::program))]
    pub struct Program<'ast> {
        pub rules: Vec<Rule_<'ast>>,
        pub eoi: EOI,
        #[pest_ast(outer())]
        pub span: Span<'ast>,
    }

    #[derive(Debug, FromPest, PartialEq, Eq, Clone)]
    #[pest_ast(rule(Rule::EOI))]
    pub struct EOI;
}

#[allow(clippy::result_large_err)]
pub fn parse(file_string: &str) -> Result<ast::Program, Error<Rule>> {
    let mut pest_pairs = MyParser::parse(Rule::program, file_string)?;
    use from_pest::FromPest;
    Ok(ast::Program::from_pest(&mut pest_pairs).expect("bug in AST construction"))
}
