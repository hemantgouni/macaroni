use std::convert::From;

pub struct SyntaxObject {
    inherited: Vec<Box<dyn Attr>>,
    synthesized: Vec<Box<dyn Attr>>,
    syntax: syn::Stmt,
    children: Vec<SyntaxObject>,
}

// make a buncha traits for each type? and convert the types using unique trait methods for that
// type

pub enum AttrName {
    Value,
    Binding,
}

pub trait Attr {
    // We need to use a Box of dyn Attrs here because we don't know the size of dyn trait objects
    // at compile time
    fn name(&self) -> AttrName;
    fn dependencies(&self) -> Vec<Box<dyn Attr>>;
}

struct Value {
    value: syn::ExprLit,
}

impl Attr for Value {
    fn name(&self) -> AttrName {
        AttrName::Value
    }
    fn dependencies(&self) -> Vec<Box<dyn Attr>> {
        Vec::new()
    }
}

impl From<syn::Stmt> for SyntaxObject {
    fn from(stmt: syn::Stmt) -> Self {
        match stmt {
            syn::Stmt::Expr(ref expr) => SyntaxObject {
                inherited: Vec::new(),
                synthesized: Vec::new(),
                syntax: stmt.clone(),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.clone().into());
                    child_vec
                },
            },
            _ => panic!("Not yet implemented"),
        }
    }
}

impl From<syn::Expr> for SyntaxObject {
    fn from(expr: syn::Expr) -> Self {
        match expr {
            syn::Expr::If(ref expr) => SyntaxObject {
                inherited: Vec::new(),
                synthesized: Vec::new(),
                syntax: syn::Stmt::Expr(syn::Expr::If(expr.clone())),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.clone().into());
                    child_vec
                },
            },
            _ => panic!("Not yet implemented!"),
        }
    }
}

impl From<syn::ExprIf> for SyntaxObject {
    fn from(expr: syn::ExprIf) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: syn::Stmt::Expr(syn::Expr::If(expr.clone())),
            children: {
               let child_vec = Vec::new();
               child_vec
            },
        }
    }
}

impl From<syn::Block> for SyntaxObject {
    fn from(expr: syn::Block) -> Self {
    }
}

fn main() {}
