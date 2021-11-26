use crate::ast::prelude::*;

/// A literal expression.
#[derive(Debug, Clone, PartialEq, Eq, Parse, ToTokens, Spanned)]
#[rune(parse = "meta_only")]
#[non_exhaustive]
pub struct ExprLit {
    /// Attributes associated with the literal expression.
    #[rune(iter, meta)]
    pub attributes: Vec<ast::Attribute>,
    /// The literal in the expression.
    pub lit: ast::Lit,
}

expr_parse!(Lit, ExprLit, "literal expression");
