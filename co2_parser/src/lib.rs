mod exp;
mod parser;

pub(crate) use co2_ast::{
    CompoundStatement, Expression, Token, TranslationUnit, TypeResolver, print_errors_and_terminate,
};

pub(crate) use co2_ast::{Span, Spanned};

fn eoi_span_for_tokens(tokens: &[Spanned<Token>], fallback: Span) -> Span {
    tokens.last().map_or(fallback, |(_, span)| {
        Span::from_parts(span.data().context, span.data().end..span.data().end)
    })
}

pub fn parse_translation_unit<R: TypeResolver>(
    filename: &str,
    preprocessed: &co2_preprocessor::PreprocessedSource,
    resolver: R,
) -> Spanned<TranslationUnit<R>> {
    let src: &'static str = Box::leak(preprocessed.raw_src.to_string().into_boxed_str());
    let end_span = eoi_span_for_tokens(
        &preprocessed.tokens,
        Span::from_parts(preprocessed.main_file_idx, src.len()..src.len()),
    );
    parse_translation_unit_from_tokens(&preprocessed.tokens, filename, src, end_span, resolver)
}

/// Parse a translation unit from an already-tokenised slice.
/// Used for inline modules whose tokens were captured during parent-file parsing.
pub fn parse_translation_unit_from_tokens<R: TypeResolver>(
    tokens: &[Spanned<Token>],
    filename: &str,
    src: &'static str,
    end_span: Span,
    resolver: R,
) -> Spanned<TranslationUnit<R>> {
    let end_span = eoi_span_for_tokens(tokens, end_span);
    match parser::parse_tu(tokens, end_span, resolver) {
        Ok(tu) => tu,
        Err(e) => {
            co2_ast::emit_errors(vec![
                co2_ast::Rich::custom(e.span, e.msg).map_token(|tok: Token| tok.to_string()),
            ]);
            print_errors_and_terminate(filename, src, Vec::new());
        }
    }
}

pub fn parse_compound_statement<R: TypeResolver>(
    tokens: &[Spanned<Token>],
    _filename: &str,
    _src: &str,
    end_span: Span,
    resolver: R,
) -> Spanned<CompoundStatement<R>> {
    let end_span = eoi_span_for_tokens(tokens, end_span);
    match parser::try_parse_compound(tokens, end_span, resolver) {
        Ok(body) => body,
        Err((span, msg)) => {
            co2_ast::emit_errors_and_terminate(vec![
                co2_ast::Rich::custom(span, msg).map_token(|tok: Token| tok.to_string()),
            ]);
        }
    }
}

pub fn parse_expression_tokens<R: TypeResolver>(
    tokens: &[Spanned<Token>],
    end_span: Span,
    resolver: R,
) -> Spanned<Expression<R>> {
    let end_span = eoi_span_for_tokens(tokens, end_span);
    match parser::try_parse_expr_full(tokens, end_span, resolver) {
        Ok(expr) => expr,
        Err((span, msg)) => {
            co2_ast::emit_errors_and_terminate(vec![
                co2_ast::Rich::custom(span, msg).map_token(|tok: Token| tok.to_string()),
            ]);
        }
    }
}
