#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Elem<'a> {
    String(&'a str),
    Symbol(&'a str),
    List(Vec<Elem<'a>>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Toplevel(pub Vec<AST>);

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Ident(pub String);

impl From<&str> for Ident {
    fn from(str: &str) -> Ident {
        match str {
            "fn" | "macro" | "quote" | "unquote" | "let" | "++" | "-" | "/" | "+" | "*" => panic!(
                "Special form encountered where an identifier was expected: {}",
                str
            ),
            _ => Ident(str.into()),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Lit {
    I64(i64),
    String(String),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AST {
    Func(Ident, Vec<AST>, Box<AST>),
    Call(Ident, Vec<AST>),
    Macro(Ident, Vec<AST>, Box<AST>),
    Lit(Lit),
    Symbol(Ident),
    Quote(Vec<AST>),
    Unquote(Vec<AST>),
    Let(Ident, Box<AST>, Box<AST>),
    Concat(Box<AST>, Box<AST>),
    Add(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mult(Box<AST>, Box<AST>),
}
