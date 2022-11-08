#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Elem<'a> {
    String(&'a str),
    Symbol(&'a str),
    List(Vec<Elem<'a>>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Toplevel(pub Vec<AST>);

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Ident(String);

impl From<&str> for Ident {
    fn from(str: &str) -> Ident {
        Ident(str.to_string())
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Value {
    I64(i64),
    String(String),
    Symbol(Ident),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AST {
    Func(Ident, Vec<AST>, Box<AST>),
    Call(Ident, Vec<AST>),
    Macro(Ident, Vec<AST>, Box<AST>),
    Value(Value),
    Quote(Vec<AST>),
    Unquote(Vec<AST>),
    Let(Ident, Box<AST>, Box<AST>),
    Concat(Box<AST>, Box<AST>),
    Add(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mult(Box<AST>, Box<AST>),
}
