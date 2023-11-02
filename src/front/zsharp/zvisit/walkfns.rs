//! AST Walker for zokrates_pest_ast

use super::{ZVisitorMut, ZVisitorResult};
use zokrates_pest_ast as ast;

pub fn walk_file<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    file: &mut ast::File<'ast>,
) -> ZVisitorResult {
    if let Some(p) = &mut file.pragma {
        visitor.visit_pragma(p)?;
    }
    file.declarations
        .iter_mut()
        .try_for_each(|d| visitor.visit_symbol_declaration(d))?;
    visitor.visit_eoi(&mut file.eoi)?;
    visitor.visit_span(&mut file.span)
}

pub fn walk_pragma<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    pragma: &mut ast::Pragma<'ast>,
) -> ZVisitorResult {
    visitor.visit_curve(&mut pragma.curve)?;
    visitor.visit_span(&mut pragma.span)
}

pub fn walk_curve<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    curve: &mut ast::Curve<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut curve.span)
}

pub fn walk_symbol_declaration<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    sd: &mut ast::SymbolDeclaration<'ast>,
) -> ZVisitorResult {
    use ast::SymbolDeclaration::*;
    match sd {
        Import(i) => visitor.visit_import_directive(i),
        Constant(c) => visitor.visit_constant_definition(c),
        Struct(s) => visitor.visit_struct_definition(s),
        Type(t) => visitor.visit_type_definition(t),
        Function(f) => visitor.visit_function_definition(f),
    }
}

pub fn walk_import_directive<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    import: &mut ast::ImportDirective<'ast>,
) -> ZVisitorResult {
    use ast::ImportDirective::*;
    match import {
        Main(m) => visitor.visit_main_import_directive(m),
        From(f) => visitor.visit_from_import_directive(f),
    }
}

pub fn walk_main_import_directive<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    mimport: &mut ast::MainImportDirective<'ast>,
) -> ZVisitorResult {
    visitor.visit_any_string(&mut mimport.source)?;
    if let Some(ie) = &mut mimport.alias {
        visitor.visit_identifier_expression(ie)?;
    }
    visitor.visit_span(&mut mimport.span)
}

pub fn walk_from_import_directive<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    fimport: &mut ast::FromImportDirective<'ast>,
) -> ZVisitorResult {
    visitor.visit_any_string(&mut fimport.source)?;
    fimport
        .symbols
        .iter_mut()
        .try_for_each(|s| visitor.visit_import_symbol(s))?;
    visitor.visit_span(&mut fimport.span)
}

pub fn walk_any_string<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    is: &mut ast::AnyString<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut is.span)
}

pub fn walk_identifier_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ie: &mut ast::IdentifierExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut ie.span)
}

pub fn walk_import_symbol<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    is: &mut ast::ImportSymbol<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut is.id)?;
    if let Some(ie) = &mut is.alias {
        visitor.visit_identifier_expression(ie)?;
    }
    visitor.visit_span(&mut is.span)
}

pub fn walk_constant_definition<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    cnstdef: &mut ast::ConstantDefinition<'ast>,
) -> ZVisitorResult {
    visitor.visit_type(&mut cnstdef.ty)?;
    visitor.visit_identifier_expression(&mut cnstdef.id)?;
    visitor.visit_expression(&mut cnstdef.expression)?;
    visitor.visit_span(&mut cnstdef.span)
}

pub fn walk_struct_definition<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    structdef: &mut ast::StructDefinition<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut structdef.id)?;
    structdef
        .generics
        .iter_mut()
        .try_for_each(|g| visitor.visit_identifier_expression(g))?;
    structdef
        .fields
        .iter_mut()
        .try_for_each(|f| visitor.visit_struct_field(f))?;
    visitor.visit_span(&mut structdef.span)
}

pub fn walk_type_definition<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    structdef: &mut ast::TypeDefinition<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut structdef.id)?;
    structdef
        .generics
        .iter_mut()
        .try_for_each(|g| visitor.visit_identifier_expression(g))?;
    visitor.visit_type(&mut structdef.ty)?;
    visitor.visit_span(&mut structdef.span)
}

pub fn walk_struct_field<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    structfield: &mut ast::StructField<'ast>,
) -> ZVisitorResult {
    visitor.visit_type(&mut structfield.ty)?;
    visitor.visit_identifier_expression(&mut structfield.id)?;
    visitor.visit_span(&mut structfield.span)
}

pub fn walk_function_definition<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    fundef: &mut ast::FunctionDefinition<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut fundef.id)?;
    fundef
        .generics
        .iter_mut()
        .try_for_each(|g| visitor.visit_identifier_expression(g))?;
    fundef
        .parameters
        .iter_mut()
        .try_for_each(|p| visitor.visit_parameter(p))?;
    fundef
        .returns
        .iter_mut()
        .try_for_each(|r| visitor.visit_type(r))?;
    fundef
        .statements
        .iter_mut()
        .try_for_each(|s| visitor.visit_statement(s))?;
    visitor.visit_span(&mut fundef.span)
}

pub fn walk_parameter<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    param: &mut ast::Parameter<'ast>,
) -> ZVisitorResult {
    if let Some(v) = &mut param.visibility {
        visitor.visit_visibility(v)?;
    }
    visitor.visit_type(&mut param.ty)?;
    visitor.visit_identifier_expression(&mut param.id)?;
    visitor.visit_span(&mut param.span)
}

pub fn walk_array_param_metadata<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    vis: &mut ast::ArrayParamMetadata<'ast>,
) -> ZVisitorResult {
    use ast::ArrayParamMetadata::*;
    match vis {
        Committed(x) => visitor.visit_array_committed(x),
        Transcript(x) => visitor.visit_array_transcript(x),
    }
}

pub fn walk_visibility<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    vis: &mut ast::Visibility<'ast>,
) -> ZVisitorResult {
    use ast::Visibility::*;
    match vis {
        Public(pu) => visitor.visit_public_visibility(pu),
        Private(pr) => visitor.visit_private_visibility(pr),
    }
}

pub fn walk_private_visibility<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    prv: &mut ast::PrivateVisibility<'ast>,
) -> ZVisitorResult {
    if let Some(pn) = &mut prv.number {
        visitor.visit_private_number(pn)?;
    }
    visitor.visit_span(&mut prv.span)
}

pub fn walk_private_number<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    pn: &mut ast::PrivateNumber<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut pn.span)
}

pub fn walk_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ty: &mut ast::Type<'ast>,
) -> ZVisitorResult {
    use ast::Type::*;
    match ty {
        Basic(b) => visitor.visit_basic_type(b),
        Array(a) => visitor.visit_array_type(a),
        Struct(s) => visitor.visit_struct_type(s),
    }
}

pub fn walk_basic_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    bty: &mut ast::BasicType<'ast>,
) -> ZVisitorResult {
    use ast::BasicType::*;
    match bty {
        Field(f) => visitor.visit_field_type(f),
        Boolean(b) => visitor.visit_boolean_type(b),
        U8(u) => visitor.visit_u8_type(u),
        U16(u) => visitor.visit_u16_type(u),
        U32(u) => visitor.visit_u32_type(u),
        U64(u) => visitor.visit_u64_type(u),
    }
}

pub fn walk_field_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    fty: &mut ast::FieldType<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut fty.span)
}

pub fn walk_boolean_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    bty: &mut ast::BooleanType<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut bty.span)
}

pub fn walk_u8_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u8ty: &mut ast::U8Type<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u8ty.span)
}

pub fn walk_u16_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u16ty: &mut ast::U16Type<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u16ty.span)
}

pub fn walk_u32_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u32ty: &mut ast::U32Type<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u32ty.span)
}

pub fn walk_u64_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u64ty: &mut ast::U64Type<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u64ty.span)
}

pub fn walk_array_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    aty: &mut ast::ArrayType<'ast>,
) -> ZVisitorResult {
    visitor.visit_basic_or_struct_type(&mut aty.ty)?;
    aty.dimensions
        .iter_mut()
        .try_for_each(|d| visitor.visit_expression(d))?;
    visitor.visit_span(&mut aty.span)
}

pub fn walk_basic_or_struct_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    bsty: &mut ast::BasicOrStructType<'ast>,
) -> ZVisitorResult {
    use ast::BasicOrStructType::*;
    match bsty {
        Struct(s) => visitor.visit_struct_type(s),
        Basic(b) => visitor.visit_basic_type(b),
    }
}

pub fn walk_struct_type<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    sty: &mut ast::StructType<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut sty.id)?;
    if let Some(eg) = &mut sty.explicit_generics {
        visitor.visit_explicit_generics(eg)?;
    }
    visitor.visit_span(&mut sty.span)
}

pub fn walk_explicit_generics<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    eg: &mut ast::ExplicitGenerics<'ast>,
) -> ZVisitorResult {
    eg.values
        .iter_mut()
        .try_for_each(|v| visitor.visit_constant_generic_value(v))?;
    visitor.visit_span(&mut eg.span)
}

pub fn walk_constant_generic_value<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    cgv: &mut ast::ConstantGenericValue<'ast>,
) -> ZVisitorResult {
    use ast::ConstantGenericValue::*;
    match cgv {
        Value(l) => visitor.visit_literal_expression(l),
        Identifier(i) => visitor.visit_identifier_expression(i),
        Underscore(u) => visitor.visit_underscore(u),
    }
}

pub fn walk_literal_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    lexpr: &mut ast::LiteralExpression<'ast>,
) -> ZVisitorResult {
    use ast::LiteralExpression::*;
    match lexpr {
        DecimalLiteral(d) => visitor.visit_decimal_literal_expression(d),
        BooleanLiteral(b) => visitor.visit_boolean_literal_expression(b),
        HexLiteral(h) => visitor.visit_hex_literal_expression(h),
    }
}

pub fn walk_decimal_literal_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    dle: &mut ast::DecimalLiteralExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_decimal_number(&mut dle.value)?;
    if let Some(s) = &mut dle.suffix {
        visitor.visit_decimal_suffix(s)?;
    }
    visitor.visit_span(&mut dle.span)
}

pub fn walk_decimal_number<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    dn: &mut ast::DecimalNumber<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut dn.span)
}

pub fn walk_decimal_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ds: &mut ast::DecimalSuffix<'ast>,
) -> ZVisitorResult {
    use ast::DecimalSuffix::*;
    match ds {
        U8(u8s) => visitor.visit_u8_suffix(u8s),
        U16(u16s) => visitor.visit_u16_suffix(u16s),
        U32(u32s) => visitor.visit_u32_suffix(u32s),
        U64(u64s) => visitor.visit_u64_suffix(u64s),
        Field(fs) => visitor.visit_field_suffix(fs),
    }
}

pub fn walk_u8_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u8s: &mut ast::U8Suffix<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u8s.span)
}

pub fn walk_u16_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u16s: &mut ast::U16Suffix<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u16s.span)
}

pub fn walk_u32_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u32s: &mut ast::U32Suffix<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u32s.span)
}

pub fn walk_u64_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u64s: &mut ast::U64Suffix<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u64s.span)
}

pub fn walk_field_suffix<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    fs: &mut ast::FieldSuffix<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut fs.span)
}

pub fn walk_boolean_literal_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ble: &mut ast::BooleanLiteralExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut ble.span)
}

pub fn walk_hex_literal_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    hle: &mut ast::HexLiteralExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_hex_number_expression(&mut hle.value)?;
    visitor.visit_span(&mut hle.span)
}

pub fn walk_hex_number_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    hne: &mut ast::HexNumberExpression<'ast>,
) -> ZVisitorResult {
    use ast::HexNumberExpression::*;
    match hne {
        U8(u8e) => visitor.visit_u8_number_expression(u8e),
        U16(u16e) => visitor.visit_u16_number_expression(u16e),
        U32(u32e) => visitor.visit_u32_number_expression(u32e),
        U64(u64e) => visitor.visit_u64_number_expression(u64e),
    }
}

pub fn walk_u8_number_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u8e: &mut ast::U8NumberExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u8e.span)
}

pub fn walk_u16_number_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u16e: &mut ast::U16NumberExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u16e.span)
}

pub fn walk_u32_number_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u32e: &mut ast::U32NumberExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u32e.span)
}

pub fn walk_u64_number_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u64e: &mut ast::U64NumberExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u64e.span)
}

pub fn walk_underscore<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    u: &mut ast::Underscore<'ast>,
) -> ZVisitorResult {
    visitor.visit_span(&mut u.span)
}

pub fn walk_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    expr: &mut ast::Expression<'ast>,
) -> ZVisitorResult {
    use ast::Expression::*;
    match expr {
        Ternary(te) => visitor.visit_ternary_expression(te),
        Binary(be) => visitor.visit_binary_expression(be),
        Unary(ue) => visitor.visit_unary_expression(ue),
        Postfix(pe) => visitor.visit_postfix_expression(pe),
        Identifier(ie) => visitor.visit_identifier_expression(ie),
        Literal(le) => visitor.visit_literal_expression(le),
        InlineArray(iae) => visitor.visit_inline_array_expression(iae),
        InlineStruct(ise) => visitor.visit_inline_struct_expression(ise),
        ArrayInitializer(aie) => visitor.visit_array_initializer_expression(aie),
    }
}

pub fn walk_ternary_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    te: &mut ast::TernaryExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut te.first)?;
    visitor.visit_expression(&mut te.second)?;
    visitor.visit_expression(&mut te.third)?;
    visitor.visit_span(&mut te.span)
}

pub fn walk_binary_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    be: &mut ast::BinaryExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_binary_operator(&mut be.op)?;
    visitor.visit_expression(&mut be.left)?;
    visitor.visit_expression(&mut be.right)?;
    visitor.visit_span(&mut be.span)
}

pub fn walk_unary_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ue: &mut ast::UnaryExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_unary_operator(&mut ue.op)?;
    visitor.visit_expression(&mut ue.expression)?;
    visitor.visit_span(&mut ue.span)
}

pub fn walk_unary_operator<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    uo: &mut ast::UnaryOperator,
) -> ZVisitorResult {
    use ast::UnaryOperator::*;
    match uo {
        Pos(po) => visitor.visit_pos_operator(po),
        Neg(ne) => visitor.visit_neg_operator(ne),
        Not(no) => visitor.visit_not_operator(no),
        Strict(so) => visitor.visit_strict_operator(so),
    }
}

pub fn walk_postfix_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    pe: &mut ast::PostfixExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut pe.id)?;
    pe.accesses
        .iter_mut()
        .try_for_each(|a| visitor.visit_access(a))?;
    visitor.visit_span(&mut pe.span)
}

pub fn walk_access<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    acc: &mut ast::Access<'ast>,
) -> ZVisitorResult {
    use ast::Access::*;
    match acc {
        Call(ca) => visitor.visit_call_access(ca),
        Select(aa) => visitor.visit_array_access(aa),
        Member(ma) => visitor.visit_member_access(ma),
    }
}

pub fn walk_call_access<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ca: &mut ast::CallAccess<'ast>,
) -> ZVisitorResult {
    if let Some(eg) = &mut ca.explicit_generics {
        visitor.visit_explicit_generics(eg)?;
    }
    visitor.visit_arguments(&mut ca.arguments)?;
    visitor.visit_span(&mut ca.span)
}

pub fn walk_arguments<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    args: &mut ast::Arguments<'ast>,
) -> ZVisitorResult {
    args.expressions
        .iter_mut()
        .try_for_each(|e| visitor.visit_expression(e))?;
    visitor.visit_span(&mut args.span)
}

pub fn walk_array_access<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    aa: &mut ast::ArrayAccess<'ast>,
) -> ZVisitorResult {
    visitor.visit_range_or_expression(&mut aa.expression)?;
    visitor.visit_span(&mut aa.span)
}

pub fn walk_range_or_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    roe: &mut ast::RangeOrExpression<'ast>,
) -> ZVisitorResult {
    use ast::RangeOrExpression::*;
    match roe {
        Range(r) => visitor.visit_range(r),
        Expression(e) => visitor.visit_expression(e),
    }
}

pub fn walk_range<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    rng: &mut ast::Range<'ast>,
) -> ZVisitorResult {
    if let Some(f) = &mut rng.from {
        visitor.visit_from_expression(f)?;
    }
    if let Some(t) = &mut rng.to {
        visitor.visit_to_expression(t)?;
    }
    visitor.visit_span(&mut rng.span)
}

pub fn walk_from_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    from: &mut ast::FromExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut from.0)
}

pub fn walk_to_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    to: &mut ast::ToExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut to.0)
}

pub fn walk_member_access<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ma: &mut ast::MemberAccess<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut ma.id)?;
    visitor.visit_span(&mut ma.span)
}

pub fn walk_inline_array_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    iae: &mut ast::InlineArrayExpression<'ast>,
) -> ZVisitorResult {
    iae.expressions
        .iter_mut()
        .try_for_each(|e| visitor.visit_spread_or_expression(e))?;
    visitor.visit_span(&mut iae.span)
}

pub fn walk_spread_or_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    soe: &mut ast::SpreadOrExpression<'ast>,
) -> ZVisitorResult {
    use ast::SpreadOrExpression::*;
    match soe {
        Spread(s) => visitor.visit_spread(s),
        Expression(e) => visitor.visit_expression(e),
    }
}

pub fn walk_spread<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    spread: &mut ast::Spread<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut spread.expression)?;
    visitor.visit_span(&mut spread.span)
}

pub fn walk_inline_struct_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ise: &mut ast::InlineStructExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut ise.ty)?;
    ise.members
        .iter_mut()
        .try_for_each(|m| visitor.visit_inline_struct_member(m))?;
    visitor.visit_span(&mut ise.span)
}

pub fn walk_inline_struct_member<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ism: &mut ast::InlineStructMember<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut ism.id)?;
    visitor.visit_expression(&mut ism.expression)?;
    visitor.visit_span(&mut ism.span)
}

pub fn walk_array_initializer_expression<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    aie: &mut ast::ArrayInitializerExpression<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut aie.value)?;
    visitor.visit_expression(&mut aie.count)?;
    visitor.visit_span(&mut aie.span)
}

pub fn walk_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    stmt: &mut ast::Statement<'ast>,
) -> ZVisitorResult {
    use ast::Statement::*;
    match stmt {
        Return(r) => visitor.visit_return_statement(r),
        Definition(d) => visitor.visit_definition_statement(d),
        Assertion(a) => visitor.visit_assertion_statement(a),
        CondStore(a) => visitor.visit_cond_store_statement(a),
        Iteration(i) => visitor.visit_iteration_statement(i),
    }
}

pub fn walk_return_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    ret: &mut ast::ReturnStatement<'ast>,
) -> ZVisitorResult {
    ret.expressions
        .iter_mut()
        .try_for_each(|e| visitor.visit_expression(e))?;
    visitor.visit_span(&mut ret.span)
}

pub fn walk_definition_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    def: &mut ast::DefinitionStatement<'ast>,
) -> ZVisitorResult {
    def.lhs
        .iter_mut()
        .try_for_each(|l| visitor.visit_typed_identifier_or_assignee(l))?;
    visitor.visit_expression(&mut def.expression)?;
    visitor.visit_span(&mut def.span)
}

pub fn walk_typed_identifier_or_assignee<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    tioa: &mut ast::TypedIdentifierOrAssignee<'ast>,
) -> ZVisitorResult {
    use ast::TypedIdentifierOrAssignee::*;
    match tioa {
        Assignee(a) => visitor.visit_assignee(a),
        TypedIdentifier(ti) => visitor.visit_typed_identifier(ti),
    }
}

pub fn walk_typed_identifier<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    tid: &mut ast::TypedIdentifier<'ast>,
) -> ZVisitorResult {
    visitor.visit_type(&mut tid.ty)?;
    visitor.visit_identifier_expression(&mut tid.identifier)?;
    visitor.visit_span(&mut tid.span)
}

pub fn walk_assignee<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    asgn: &mut ast::Assignee<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut asgn.id)?;
    asgn.accesses
        .iter_mut()
        .try_for_each(|a| visitor.visit_assignee_access(a))?;
    visitor.visit_span(&mut asgn.span)
}

pub fn walk_assignee_access<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    acc: &mut ast::AssigneeAccess<'ast>,
) -> ZVisitorResult {
    use ast::AssigneeAccess::*;
    match acc {
        Select(aa) => visitor.visit_array_access(aa),
        Member(ma) => visitor.visit_member_access(ma),
    }
}

pub fn walk_assertion_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    asrt: &mut ast::AssertionStatement<'ast>,
) -> ZVisitorResult {
    visitor.visit_expression(&mut asrt.expression)?;
    if let Some(s) = &mut asrt.message {
        visitor.visit_any_string(s)?;
    }
    visitor.visit_span(&mut asrt.span)
}

pub fn walk_cond_store_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    s: &mut ast::CondStoreStatement<'ast>,
) -> ZVisitorResult {
    visitor.visit_identifier_expression(&mut s.array)?;
    visitor.visit_array_index_expression(&mut s.index)?;
    visitor.visit_expression(&mut s.value)?;
    visitor.visit_expression(&mut s.condition)?;
    visitor.visit_span(&mut s.span)
}

pub fn walk_iteration_statement<'ast, Z: ZVisitorMut<'ast>>(
    visitor: &mut Z,
    iter: &mut ast::IterationStatement<'ast>,
) -> ZVisitorResult {
    visitor.visit_type(&mut iter.ty)?;
    visitor.visit_identifier_expression(&mut iter.index)?;
    visitor.visit_expression(&mut iter.from)?;
    visitor.visit_expression(&mut iter.to)?;
    iter.statements
        .iter_mut()
        .try_for_each(|s| visitor.visit_statement(s))?;
    visitor.visit_span(&mut iter.span)
}
