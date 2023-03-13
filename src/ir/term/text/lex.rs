//! IR Lexer

use logos::{self, Logos};

#[derive(Logos, Debug, PartialEq, Eq, Clone, Copy)]
pub enum Token {
    // Program constructs
    #[token(b"(")]
    Open,
    #[token(b")")]
    Close,

    // Literals
    #[regex(br"-?[0-9]+", priority = 2)]
    Int,
    #[regex(br"#x[0-9a-fA-F]+")]
    Hex,
    #[regex(br"#b[01]+")]
    Bin,
    #[regex(br"#f-?[0-9]+(m[0-9]+)?")]
    Field,
    // TODO: Float

    // Identifiers
    #[regex(br"#t|#a|#l|[^()0-9#; \t\n\f][^(); \t\n\f#]*")]
    Ident,

    // Logos requires one token variant to handle errors,
    // it can be named anything you wish.
    // We can also use this variant to define whitespace,
    // or any other matches we wish to skip.
    #[error]
    // Skip space
    #[regex(br"[ \t\n\f]+", logos::skip)]
    // Skip comments
    #[regex(br";[^\n]*\n", logos::skip)]
    Error,
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn all_tokens() {
        let l = Token::lexer(b"(let ((a true)(b true)) (add (sub #b01 #xFf) (div 15 -16)))");
        let tokens: Vec<_> = l.into_iter().collect();
        assert_eq!(
            &tokens,
            &[
                Token::Open,
                Token::Ident,
                Token::Open,
                Token::Open,
                Token::Ident,
                Token::Ident,
                Token::Close,
                Token::Open,
                Token::Ident,
                Token::Ident,
                Token::Close,
                Token::Close,
                Token::Open,
                Token::Ident,
                Token::Open,
                Token::Ident,
                Token::Bin,
                Token::Hex,
                Token::Close,
                Token::Open,
                Token::Ident,
                Token::Int,
                Token::Int,
                Token::Close,
                Token::Close,
                Token::Close,
            ]
        )
    }
}
