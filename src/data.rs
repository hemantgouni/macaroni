#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Elem<'a> {
    String(&'a str),
    Symbol(&'a str),
    List(Vec<Elem<'a>>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub struct Toplevel(pub Vec<AST>);

#[derive(Debug, Eq, PartialEq, Clone, Hash)]
pub struct Ident(pub String);

impl From<&str> for Ident {
    fn from(str: &str) -> Ident {
        match str {
            "%" | "&&" | "*" | "+" | "++" | "-" | "/" | "<" | "==" | ">" | "||" | "car" | "cdr"
            | "cons" | "empty?" | "fn" | "if" | "let" | "list" | "macro" | "quote" | "unquote" => {
                panic!(
                    "Special form encountered where an identifier was expected: {}",
                    str
                )
            }
            _ => Ident(str.into()),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Lit {
    I64(i64),
    Bool(bool),
    String(String),
    List(Vec<Lit>),
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AST {
    Func(Ident, Vec<Ident>, Box<AST>),
    Call(Ident, Vec<AST>),
    Macro(Ident, Vec<Ident>, Box<AST>),
    Lit(Lit),
    Symbol(Ident),
    // consider a different abstractification procedure for when we're in quote
    Quote(Vec<AST>),
    List(Vec<AST>),
    Cons(Box<AST>, Box<AST>),
    Car(Box<AST>),
    Cdr(Box<AST>),
    Emptyp(Box<AST>),
    Let(Ident, Box<AST>, Box<AST>),
    Ite(Box<AST>, Box<AST>, Box<AST>),
    And(Box<AST>, Box<AST>),
    Or(Box<AST>, Box<AST>),
    Eq(Box<AST>, Box<AST>),
    Lt(Box<AST>, Box<AST>),
    Gt(Box<AST>, Box<AST>),
    Concat(Box<AST>, Box<AST>),
    Add(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mult(Box<AST>, Box<AST>),
    Mod(Box<AST>, Box<AST>),
}
