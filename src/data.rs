#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Elem<A> {
    String(A),
    Symbol(A),
    List(Vec<Elem<A>>),
}

impl<A> Elem<A> {
    pub fn map<B>(&self, func: &impl Fn(&A) -> B) -> Elem<B> {
        match self {
            Elem::String(str) => Elem::String(func(str)),
            Elem::Symbol(str) => Elem::Symbol(func(str)),
            Elem::List(elems) => Elem::List(elems.iter().map(|elem| elem.map(func)).collect()),
        }
    }
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
                panic!("Special form used incorrectly: {}", str)
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
    Symbol(String),
    List(Vec<Lit>),
}

impl Lit {
    pub fn to_elem(&self) -> Elem<String> {
        match self {
            Lit::I64(num) => Elem::Symbol(num.to_string()),
            Lit::Bool(bool) => Elem::Symbol(bool.to_string()),
            Lit::String(string) => Elem::String(string.to_string()),
            Lit::Symbol(string) => Elem::Symbol(string.to_string()),
            Lit::List(lits) => Elem::List(lits.iter().map(|lit| lit.to_elem()).collect()),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum AST {
    Func(Ident, Vec<Ident>, Box<AST>),
    Call(Ident, Vec<AST>),
    Macro(Ident, Vec<Ident>, Box<AST>),
    Lit(Lit),
    Ident(Ident),
    // consider a different abstractification procedure for when we're in quote
    Eval(Box<AST>),
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
