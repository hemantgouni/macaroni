use crate::check::Type;
use std::collections::HashMap;

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
    Type(Type, Box<AST>),
    Func(Ident, Vec<Ident>, Box<AST>),
    Call(Ident, Vec<AST>),
    Macro(Ident, Vec<Ident>, Box<AST>),
    MacroCall(Ident, Vec<Lit>),
    Lit(Lit),
    Var(Ident),
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
    // formulate this as a macro?
    Add(Box<AST>, Box<AST>),
    Div(Box<AST>, Box<AST>),
    Sub(Box<AST>, Box<AST>),
    Mult(Box<AST>, Box<AST>),
    Mod(Box<AST>, Box<AST>),
    // use this to latently introduce typing information from macros?
    Rewrite(Box<AST>, fn(AST) -> AST),
}

impl AST {
    pub fn rewrite(self) -> AST {
        match self {
            AST::Type(typ, expr) => AST::Type(typ, Box::new(Self::rewrite(*expr))),
            AST::Func(name, args, body) => AST::Func(name, args, Box::new(Self::rewrite(*body))),
            AST::Macro(name, args, body) => AST::Macro(name, args, Box::new(Self::rewrite(*body))),
            AST::Call(name, args) => AST::Call(
                name,
                args.iter()
                    .map(|arg| Self::rewrite(arg.to_owned()))
                    .collect(),
            ),
            AST::MacroCall(name, args) => AST::MacroCall(name, args),
            AST::Lit(lit) => AST::Lit(lit),
            AST::Var(ident) => AST::Var(ident),
            AST::Eval(expr) => AST::Eval(Box::new(Self::rewrite(*expr))),
            AST::List(exprs) => AST::List(
                exprs
                    .iter()
                    .map(|expr| Self::rewrite(expr.to_owned()))
                    .collect(),
            ),
            AST::Cons(expr1, expr2) => AST::Cons(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Car(expr) => AST::Car(Box::new(Self::rewrite(*expr))),
            AST::Cdr(expr) => AST::Cdr(Box::new(Self::rewrite(*expr))),
            AST::Emptyp(expr) => AST::Emptyp(Box::new(Self::rewrite(*expr))),
            AST::Let(var, expr1, expr2) => AST::Let(
                var,
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Ite(guard, expr1, expr2) => AST::Ite(
                Box::new(Self::rewrite(*guard)),
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::And(expr1, expr2) => AST::And(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Or(expr1, expr2) => AST::Or(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Eq(expr1, expr2) => AST::Eq(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Lt(expr1, expr2) => AST::Lt(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Gt(expr1, expr2) => AST::Gt(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Concat(expr1, expr2) => AST::Concat(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Add(expr1, expr2) => AST::Add(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Div(expr1, expr2) => AST::Div(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Sub(expr1, expr2) => AST::Sub(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Mult(expr1, expr2) => AST::Mult(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Mod(expr1, expr2) => AST::Mod(
                Box::new(Self::rewrite(*expr1)),
                Box::new(Self::rewrite(*expr2)),
            ),
            AST::Rewrite(expr, func) => func(*expr),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Env<A>(HashMap<Ident, A>);

// This type is worked with immutably
impl<A: Clone> Env<A> {
    pub fn new() -> Self {
        Env(HashMap::new())
    }

    pub fn insert(&mut self, ident: Ident, elem: A) -> Self {
        match self {
            Env(map) => {
                map.insert(ident, elem);
                Env(map.clone())
            }
        }
    }

    pub fn lookup(&self, ident: &Ident) -> Result<A, String> {
        match self {
            Env(map) => map
                .get(ident)
                .cloned()
                .ok_or(format!("No binding found: {:?}", ident)),
        }
    }
}
