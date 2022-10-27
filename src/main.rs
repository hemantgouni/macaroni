use std::fmt::{Debug, Error, Formatter};
use std::result::Result;

use std::convert::From;

#[allow(dead_code)]
#[derive(Debug)]
pub struct SyntaxObject {
    inherited: Vec<Box<dyn Attr>>,
    synthesized: Vec<Box<dyn Attr>>,
    syntax: Syntax,
    children: Vec<SyntaxObject>,
}

#[derive(Debug)]
pub enum Syntax {
    Block(syn::Block),
    Stmt(syn::Stmt),
    Expr(syn::Expr),
    ExprIf(syn::ExprIf),
    ExprLit(syn::ExprLit),
    Lit(syn::Lit),
    LitStr(syn::LitStr),
    LitByteStr(syn::LitByteStr),
    LitByte(syn::LitByte),
    LitChar(syn::LitChar),
    LitInt(syn::LitInt),
    LitFloat(syn::LitFloat),
    LitBool(syn::LitBool),
    Local(syn::Local),
}

// make a buncha traits for each type? and convert the types using unique trait methods for that
// type

#[derive(Debug)]
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

impl Debug for dyn Attr {
    fn fmt(&self, _f: &mut Formatter<'_>) -> Result<(), Error> {
        Ok(println!("Attr {:?}", self.name()))
    }
}

#[allow(dead_code)]
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
                syntax: Syntax::Stmt(stmt.clone()),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.clone().into());
                    child_vec
                },
            },
            syn::Stmt::Local(local) => {
                
                let pat = local.pat.clone();

                SyntaxObject {
                    inherited: Vec::new(),
                    synthesized: Vec::new(),
                    syntax: Syntax::Local(local.clone()),
                    children: Vec::new(),
                }
            },
            other => panic!("Not yet implemented: {:?}", other),
        }
    }
}

impl From<syn::Expr> for SyntaxObject {
    fn from(expr: syn::Expr) -> Self {
        match expr {
            syn::Expr::If(ref expr) => SyntaxObject {
                inherited: Vec::new(),
                synthesized: Vec::new(),
                syntax: Syntax::Expr(syn::Expr::If(expr.clone())),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.clone().into());
                    child_vec
                },
            },
            syn::Expr::Lit(expr) => SyntaxObject {
                inherited: Vec::new(),
                synthesized: Vec::new(),
                syntax: Syntax::Expr(syn::Expr::Lit(expr.clone())),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.into());
                    child_vec
                },
            },
            syn::Expr::Block(expr) => SyntaxObject {
                inherited: Vec::new(),
                synthesized: Vec::new(),
                syntax: Syntax::Expr(syn::Expr::Block(expr.clone())),
                children: {
                    let mut child_vec = Vec::new();
                    child_vec.push(expr.block.into());
                    child_vec
                },
            },
            other => panic!("Not yet implemented: {:?}", other),
        }
    }
}

impl From<syn::ExprIf> for SyntaxObject {
    fn from(expr: syn::ExprIf) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::ExprIf(expr.clone()),
            children: {
                let mut child_vec = Vec::new();
                let cond: syn::Expr = *expr.cond.clone();
                let then_branch: syn::Block = expr.then_branch.clone();
                let else_branch = match expr.else_branch {
                    Some((_, expr)) => *expr,
                    None => panic!("Not yet implemented: {:?}", expr.else_branch),
                };

                child_vec.push(cond.into());
                child_vec.push(then_branch.into());
                child_vec.push(else_branch.into());
                child_vec
            },
        }
    }
}

impl From<syn::Block> for SyntaxObject {
    fn from(expr: syn::Block) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::Block(expr.clone()),
            children: {
                let child_vec: Vec<SyntaxObject> = expr
                    .stmts
                    .iter()
                    .map(|stmt| stmt.to_owned().into())
                    .collect();
                child_vec
            },
        }
    }
}

impl From<syn::ExprLit> for SyntaxObject {
    fn from(expr_lit: syn::ExprLit) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::ExprLit(expr_lit.clone()),
            children: {
                let mut child_vec = Vec::new();
                child_vec.push(expr_lit.lit.into());
                child_vec
            },
        }
    }
}

impl From<syn::Lit> for SyntaxObject {
    fn from(lit: syn::Lit) -> Self {
        let mut child_vec = Vec::new();
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::Lit(lit.clone()),
            children: {
                match lit {
                    syn::Lit::Str(lit_str) => {
                        child_vec.push(lit_str.into());
                    }
                    syn::Lit::ByteStr(lit_byte_str) => {
                        child_vec.push(lit_byte_str.into());
                    }
                    syn::Lit::Byte(lit_byte) => {
                        child_vec.push(lit_byte.into());
                    }
                    syn::Lit::Char(lit_char) => {
                        child_vec.push(lit_char.into());
                    }
                    syn::Lit::Int(lit_int) => {
                        child_vec.push(lit_int.into());
                    }
                    syn::Lit::Float(lit_float) => {
                        child_vec.push(lit_float.into());
                    }
                    syn::Lit::Bool(lit_bool) => child_vec.push(lit_bool.into()),
                    other => panic!("Not yet implemented: {:?}", other),
                };
                child_vec
            },
        }
    }
}

impl From<syn::LitStr> for SyntaxObject {
    fn from(lit_str: syn::LitStr) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitStr(lit_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitByteStr> for SyntaxObject {
    fn from(lit_byte_str: syn::LitByteStr) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitByteStr(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitByte> for SyntaxObject {
    fn from(lit_byte_str: syn::LitByte) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitByte(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitChar> for SyntaxObject {
    fn from(lit_byte_str: syn::LitChar) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitChar(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitInt> for SyntaxObject {
    fn from(lit_byte_str: syn::LitInt) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitInt(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitFloat> for SyntaxObject {
    fn from(lit_byte_str: syn::LitFloat) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitFloat(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::LitBool> for SyntaxObject {
    fn from(lit_byte_str: syn::LitBool) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::LitBool(lit_byte_str.clone()),
            children: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test() -> Result<(), syn::Error> {
        let _a = if true { 1 } else { 2 };

        let ast_nodes = syn::parse_str::<syn::Expr>("{ let a = 1; if true { 1 } else { a } }")?;

        let _stx_obj: SyntaxObject = ast_nodes.into();

        let _output =
      r"SyntaxObject {
            inherited: [],
            synthesized: [],
            syntax: Expr(Lit(ExprLit { attrs: [], lit: Int(LitInt { token: 1 }) })),
            children: [
                SyntaxObject {
                    inherited: [],
                    synthesized: [],
                    syntax: ExprLit(ExprLit { attrs: [] , lit: Int(LitInt { token: 1 }) }),
                    children: [
                        SyntaxObject {
                            inherited: [],
                            synthesized: [],
                            syntax: Lit(Int(LitInt { token: 1 })),
                            children: [
                                SyntaxObject {
                                    inherited: [],
                                    synthesized: [],
                                    syntax: LitInt(LitInt { token: 1 }),
                                    children: []
                                }
                            ]
                        }
                    ]
                }
            ]
        }";

        Ok(())
    }
}

fn main() {
}
