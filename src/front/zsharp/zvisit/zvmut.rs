//! AST Walker for zokrates_pest_ast

use super::walkfns::*;
use super::ZVisitorResult;

use zokrates_pest_ast as ast;

pub trait ZVisitorMut<'ast>: Sized {
    fn visit_file(&mut self, file: &mut ast::File<'ast>) -> ZVisitorResult {
        walk_file(self, file)
    }

    fn visit_pragma(&mut self, pragma: &mut ast::Pragma<'ast>) -> ZVisitorResult {
        walk_pragma(self, pragma)
    }

    fn visit_curve(&mut self, curve: &mut ast::Curve<'ast>) -> ZVisitorResult {
        walk_curve(self, curve)
    }

    fn visit_span(&mut self, _span: &mut ast::Span<'ast>) -> ZVisitorResult {
        Ok(())
    }

    fn visit_symbol_declaration(
        &mut self,
        sd: &mut ast::SymbolDeclaration<'ast>,
    ) -> ZVisitorResult {
        walk_symbol_declaration(self, sd)
    }

    fn visit_eoi(&mut self, _eoi: &mut ast::EOI) -> ZVisitorResult {
        Ok(())
    }

    fn visit_import_directive(
        &mut self,
        import: &mut ast::ImportDirective<'ast>,
    ) -> ZVisitorResult {
        walk_import_directive(self, import)
    }

    fn visit_main_import_directive(
        &mut self,
        mimport: &mut ast::MainImportDirective<'ast>,
    ) -> ZVisitorResult {
        walk_main_import_directive(self, mimport)
    }

    fn visit_from_import_directive(
        &mut self,
        fimport: &mut ast::FromImportDirective<'ast>,
    ) -> ZVisitorResult {
        walk_from_import_directive(self, fimport)
    }

    fn visit_any_string(&mut self, is: &mut ast::AnyString<'ast>) -> ZVisitorResult {
        walk_any_string(self, is)
    }

    fn visit_import_symbol(&mut self, is: &mut ast::ImportSymbol<'ast>) -> ZVisitorResult {
        walk_import_symbol(self, is)
    }

    fn visit_identifier_expression(
        &mut self,
        ie: &mut ast::IdentifierExpression<'ast>,
    ) -> ZVisitorResult {
        walk_identifier_expression(self, ie)
    }

    fn visit_constant_definition(
        &mut self,
        cnstdef: &mut ast::ConstantDefinition<'ast>,
    ) -> ZVisitorResult {
        walk_constant_definition(self, cnstdef)
    }

    fn visit_struct_definition(
        &mut self,
        structdef: &mut ast::StructDefinition<'ast>,
    ) -> ZVisitorResult {
        walk_struct_definition(self, structdef)
    }

    fn visit_type_definition(
        &mut self,
        structdef: &mut ast::TypeDefinition<'ast>,
    ) -> ZVisitorResult {
        walk_type_definition(self, structdef)
    }

    fn visit_struct_field(&mut self, structfield: &mut ast::StructField<'ast>) -> ZVisitorResult {
        walk_struct_field(self, structfield)
    }

    fn visit_function_definition(
        &mut self,
        fundef: &mut ast::FunctionDefinition<'ast>,
    ) -> ZVisitorResult {
        walk_function_definition(self, fundef)
    }

    fn visit_parameter(&mut self, param: &mut ast::Parameter<'ast>) -> ZVisitorResult {
        walk_parameter(self, param)
    }

    fn visit_visibility(&mut self, vis: &mut ast::Visibility<'ast>) -> ZVisitorResult {
        walk_visibility(self, vis)
    }

    fn visit_public_visibility(&mut self, _pu: &mut ast::PublicVisibility) -> ZVisitorResult {
        Ok(())
    }

    fn visit_array_param_metadata(
        &mut self,
        vis: &mut ast::ArrayParamMetadata<'ast>,
    ) -> ZVisitorResult {
        walk_array_param_metadata(self, vis)
    }

    fn visit_array_committed(&mut self, _c: &mut ast::ArrayCommitted<'ast>) -> ZVisitorResult {
        Ok(())
    }

    fn visit_array_transcript(&mut self, _c: &mut ast::ArrayTranscript<'ast>) -> ZVisitorResult {
        Ok(())
    }

    fn visit_private_visibility(
        &mut self,
        pr: &mut ast::PrivateVisibility<'ast>,
    ) -> ZVisitorResult {
        walk_private_visibility(self, pr)
    }

    fn visit_private_number(&mut self, pn: &mut ast::PrivateNumber<'ast>) -> ZVisitorResult {
        walk_private_number(self, pn)
    }

    fn visit_type(&mut self, ty: &mut ast::Type<'ast>) -> ZVisitorResult {
        walk_type(self, ty)
    }

    fn visit_basic_type(&mut self, bty: &mut ast::BasicType<'ast>) -> ZVisitorResult {
        walk_basic_type(self, bty)
    }

    fn visit_field_type(&mut self, fty: &mut ast::FieldType<'ast>) -> ZVisitorResult {
        walk_field_type(self, fty)
    }

    fn visit_boolean_type(&mut self, bty: &mut ast::BooleanType<'ast>) -> ZVisitorResult {
        walk_boolean_type(self, bty)
    }

    fn visit_u8_type(&mut self, u8ty: &mut ast::U8Type<'ast>) -> ZVisitorResult {
        walk_u8_type(self, u8ty)
    }

    fn visit_u16_type(&mut self, u16ty: &mut ast::U16Type<'ast>) -> ZVisitorResult {
        walk_u16_type(self, u16ty)
    }

    fn visit_u32_type(&mut self, u32ty: &mut ast::U32Type<'ast>) -> ZVisitorResult {
        walk_u32_type(self, u32ty)
    }

    fn visit_u64_type(&mut self, u64ty: &mut ast::U64Type<'ast>) -> ZVisitorResult {
        walk_u64_type(self, u64ty)
    }

    fn visit_array_type(&mut self, aty: &mut ast::ArrayType<'ast>) -> ZVisitorResult {
        walk_array_type(self, aty)
    }

    fn visit_basic_or_struct_type(
        &mut self,
        bsty: &mut ast::BasicOrStructType<'ast>,
    ) -> ZVisitorResult {
        walk_basic_or_struct_type(self, bsty)
    }

    fn visit_struct_type(&mut self, sty: &mut ast::StructType<'ast>) -> ZVisitorResult {
        walk_struct_type(self, sty)
    }

    fn visit_explicit_generics(&mut self, eg: &mut ast::ExplicitGenerics<'ast>) -> ZVisitorResult {
        walk_explicit_generics(self, eg)
    }

    fn visit_constant_generic_value(
        &mut self,
        cgv: &mut ast::ConstantGenericValue<'ast>,
    ) -> ZVisitorResult {
        walk_constant_generic_value(self, cgv)
    }

    fn visit_literal_expression(
        &mut self,
        lexpr: &mut ast::LiteralExpression<'ast>,
    ) -> ZVisitorResult {
        walk_literal_expression(self, lexpr)
    }

    fn visit_decimal_literal_expression(
        &mut self,
        dle: &mut ast::DecimalLiteralExpression<'ast>,
    ) -> ZVisitorResult {
        walk_decimal_literal_expression(self, dle)
    }

    fn visit_decimal_number(&mut self, dn: &mut ast::DecimalNumber<'ast>) -> ZVisitorResult {
        walk_decimal_number(self, dn)
    }

    fn visit_decimal_suffix(&mut self, ds: &mut ast::DecimalSuffix<'ast>) -> ZVisitorResult {
        walk_decimal_suffix(self, ds)
    }

    fn visit_u8_suffix(&mut self, u8s: &mut ast::U8Suffix<'ast>) -> ZVisitorResult {
        walk_u8_suffix(self, u8s)
    }

    fn visit_u16_suffix(&mut self, u16s: &mut ast::U16Suffix<'ast>) -> ZVisitorResult {
        walk_u16_suffix(self, u16s)
    }

    fn visit_u32_suffix(&mut self, u32s: &mut ast::U32Suffix<'ast>) -> ZVisitorResult {
        walk_u32_suffix(self, u32s)
    }

    fn visit_u64_suffix(&mut self, u64s: &mut ast::U64Suffix<'ast>) -> ZVisitorResult {
        walk_u64_suffix(self, u64s)
    }

    fn visit_field_suffix(&mut self, fs: &mut ast::FieldSuffix<'ast>) -> ZVisitorResult {
        walk_field_suffix(self, fs)
    }

    fn visit_boolean_literal_expression(
        &mut self,
        ble: &mut ast::BooleanLiteralExpression<'ast>,
    ) -> ZVisitorResult {
        walk_boolean_literal_expression(self, ble)
    }

    fn visit_hex_literal_expression(
        &mut self,
        hle: &mut ast::HexLiteralExpression<'ast>,
    ) -> ZVisitorResult {
        walk_hex_literal_expression(self, hle)
    }

    fn visit_hex_number_expression(
        &mut self,
        hne: &mut ast::HexNumberExpression<'ast>,
    ) -> ZVisitorResult {
        walk_hex_number_expression(self, hne)
    }

    fn visit_u8_number_expression(
        &mut self,
        u8e: &mut ast::U8NumberExpression<'ast>,
    ) -> ZVisitorResult {
        walk_u8_number_expression(self, u8e)
    }

    fn visit_u16_number_expression(
        &mut self,
        u16e: &mut ast::U16NumberExpression<'ast>,
    ) -> ZVisitorResult {
        walk_u16_number_expression(self, u16e)
    }

    fn visit_u32_number_expression(
        &mut self,
        u32e: &mut ast::U32NumberExpression<'ast>,
    ) -> ZVisitorResult {
        walk_u32_number_expression(self, u32e)
    }

    fn visit_u64_number_expression(
        &mut self,
        u64e: &mut ast::U64NumberExpression<'ast>,
    ) -> ZVisitorResult {
        walk_u64_number_expression(self, u64e)
    }

    fn visit_underscore(&mut self, u: &mut ast::Underscore<'ast>) -> ZVisitorResult {
        walk_underscore(self, u)
    }

    fn visit_expression(&mut self, expr: &mut ast::Expression<'ast>) -> ZVisitorResult {
        walk_expression(self, expr)
    }

    fn visit_ternary_expression(
        &mut self,
        te: &mut ast::TernaryExpression<'ast>,
    ) -> ZVisitorResult {
        walk_ternary_expression(self, te)
    }

    fn visit_binary_expression(&mut self, be: &mut ast::BinaryExpression<'ast>) -> ZVisitorResult {
        walk_binary_expression(self, be)
    }

    fn visit_binary_operator(&mut self, _bo: &mut ast::BinaryOperator) -> ZVisitorResult {
        Ok(())
    }

    fn visit_unary_expression(&mut self, ue: &mut ast::UnaryExpression<'ast>) -> ZVisitorResult {
        walk_unary_expression(self, ue)
    }

    fn visit_unary_operator(&mut self, uo: &mut ast::UnaryOperator) -> ZVisitorResult {
        walk_unary_operator(self, uo)
    }

    fn visit_pos_operator(&mut self, _po: &mut ast::PosOperator) -> ZVisitorResult {
        Ok(())
    }

    fn visit_neg_operator(&mut self, _po: &mut ast::NegOperator) -> ZVisitorResult {
        Ok(())
    }

    fn visit_not_operator(&mut self, _po: &mut ast::NotOperator) -> ZVisitorResult {
        Ok(())
    }

    fn visit_strict_operator(&mut self, _so: &mut ast::StrOperator) -> ZVisitorResult {
        Ok(())
    }

    fn visit_postfix_expression(
        &mut self,
        pe: &mut ast::PostfixExpression<'ast>,
    ) -> ZVisitorResult {
        walk_postfix_expression(self, pe)
    }

    fn visit_access(&mut self, acc: &mut ast::Access<'ast>) -> ZVisitorResult {
        walk_access(self, acc)
    }

    fn visit_call_access(&mut self, ca: &mut ast::CallAccess<'ast>) -> ZVisitorResult {
        walk_call_access(self, ca)
    }

    fn visit_arguments(&mut self, args: &mut ast::Arguments<'ast>) -> ZVisitorResult {
        walk_arguments(self, args)
    }

    fn visit_array_access(&mut self, aa: &mut ast::ArrayAccess<'ast>) -> ZVisitorResult {
        walk_array_access(self, aa)
    }

    fn visit_array_index_expression(
        &mut self,
        index: &mut ast::Expression<'ast>,
    ) -> ZVisitorResult {
        walk_expression(self, index)
    }

    fn visit_range_or_expression(
        &mut self,
        roe: &mut ast::RangeOrExpression<'ast>,
    ) -> ZVisitorResult {
        walk_range_or_expression(self, roe)
    }

    fn visit_range(&mut self, rng: &mut ast::Range<'ast>) -> ZVisitorResult {
        walk_range(self, rng)
    }

    fn visit_from_expression(&mut self, from: &mut ast::FromExpression<'ast>) -> ZVisitorResult {
        walk_from_expression(self, from)
    }

    fn visit_to_expression(&mut self, to: &mut ast::ToExpression<'ast>) -> ZVisitorResult {
        walk_to_expression(self, to)
    }

    fn visit_member_access(&mut self, ma: &mut ast::MemberAccess<'ast>) -> ZVisitorResult {
        walk_member_access(self, ma)
    }

    fn visit_inline_array_expression(
        &mut self,
        iae: &mut ast::InlineArrayExpression<'ast>,
    ) -> ZVisitorResult {
        walk_inline_array_expression(self, iae)
    }

    fn visit_spread_or_expression(
        &mut self,
        soe: &mut ast::SpreadOrExpression<'ast>,
    ) -> ZVisitorResult {
        walk_spread_or_expression(self, soe)
    }

    fn visit_spread(&mut self, spread: &mut ast::Spread<'ast>) -> ZVisitorResult {
        walk_spread(self, spread)
    }

    fn visit_inline_struct_expression(
        &mut self,
        ise: &mut ast::InlineStructExpression<'ast>,
    ) -> ZVisitorResult {
        walk_inline_struct_expression(self, ise)
    }

    fn visit_inline_struct_member(
        &mut self,
        ism: &mut ast::InlineStructMember<'ast>,
    ) -> ZVisitorResult {
        walk_inline_struct_member(self, ism)
    }

    fn visit_array_initializer_expression(
        &mut self,
        aie: &mut ast::ArrayInitializerExpression<'ast>,
    ) -> ZVisitorResult {
        walk_array_initializer_expression(self, aie)
    }

    fn visit_statement(&mut self, stmt: &mut ast::Statement<'ast>) -> ZVisitorResult {
        walk_statement(self, stmt)
    }

    fn visit_return_statement(&mut self, ret: &mut ast::ReturnStatement<'ast>) -> ZVisitorResult {
        walk_return_statement(self, ret)
    }

    fn visit_definition_statement(
        &mut self,
        def: &mut ast::DefinitionStatement<'ast>,
    ) -> ZVisitorResult {
        walk_definition_statement(self, def)
    }

    fn visit_typed_identifier_or_assignee(
        &mut self,
        tioa: &mut ast::TypedIdentifierOrAssignee<'ast>,
    ) -> ZVisitorResult {
        walk_typed_identifier_or_assignee(self, tioa)
    }

    fn visit_typed_identifier(&mut self, ti: &mut ast::TypedIdentifier<'ast>) -> ZVisitorResult {
        walk_typed_identifier(self, ti)
    }

    fn visit_assignee(&mut self, asgn: &mut ast::Assignee<'ast>) -> ZVisitorResult {
        walk_assignee(self, asgn)
    }

    fn visit_assignee_access(&mut self, acc: &mut ast::AssigneeAccess<'ast>) -> ZVisitorResult {
        walk_assignee_access(self, acc)
    }

    fn visit_assertion_statement(
        &mut self,
        asrt: &mut ast::AssertionStatement<'ast>,
    ) -> ZVisitorResult {
        walk_assertion_statement(self, asrt)
    }

    fn visit_cond_store_statement(
        &mut self,
        s: &mut ast::CondStoreStatement<'ast>,
    ) -> ZVisitorResult {
        walk_cond_store_statement(self, s)
    }

    fn visit_iteration_statement(
        &mut self,
        iter: &mut ast::IterationStatement<'ast>,
    ) -> ZVisitorResult {
        walk_iteration_statement(self, iter)
    }
}
