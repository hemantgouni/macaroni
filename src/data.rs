#[derive(Debug, Clone)]
pub struct Attrs<A> {
    bindings: Vec<(String, A)>,
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Elem<'a> {
    String(&'a str),
    Symbol(&'a str),
    List(Vec<Elem<'a>>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Ident(pub String);

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Value {
    I64(i64),
    String(String),
    Symbol(String),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AST {
    Value(Value),
    Let(Ident, Box<AST>, Box<AST>),
    Concat(Box<AST>, Box<AST>),
    Add(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mult(Box<AST>, Box<AST>),
}
