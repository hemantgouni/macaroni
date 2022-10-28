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
    Pat(syn::Pat),
    PatBox(syn::PatBox),
    PatIdent(syn::PatIdent),
    PatLit(syn::PatLit),
    PatMacro(syn::PatMacro),
    PatOr(syn::PatOr),
    PatPath(syn::PatPath),
    PatRange(syn::PatRange),
    PatReference(syn::PatReference),
    PatRest(syn::PatRest),
    PatSlide(syn::PatSlice),
    PatStruct(syn::PatStruct),
    PatTuple(syn::PatTuple),
    PatTupleStruct(syn::PatTupleStruct),
    PatType(syn::PatType),
    PatWild(syn::PatWild),
    Type(syn::Type),
    TypeArray(syn::TypeArray),
    TypeBareFn(syn::TypeBareFn),
    TypeGroup(syn::TypeGroup),
    TypeImplTrait(syn::TypeImplTrait),
    TypeInfer(syn::TypeInfer),
    TypeMacro(syn::TypeMacro),
    TypeNever(syn::TypeNever),
    TypeParen(syn::TypeParen),
    TypePath(syn::TypePath),
    TypePtr(syn::TypePtr),
    TypeReference(syn::TypeReference),
    TypeSlice(syn::TypeSlice),
    TypeTraitObject(syn::TypeTraitObject),
    TypeTuple(syn::TypeTuple),
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
            }
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
                child_vec.push(cond.into());
                child_vec.push(then_branch.into());
                match expr.else_branch {
                    Some((_, expr)) => child_vec.push((*expr).into()),
                    None => (),
                };
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

impl From<syn::Pat> for SyntaxObject {
    fn from(pat: syn::Pat) -> Self {
        panic!();
    }
}

impl From<syn::PatBox> for SyntaxObject {
    fn from(pat: syn::PatBox) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatBox(pat.clone()),
            children: {
                let mut child_vec = Vec::new();
                let pat_inner: syn::Pat = *pat.pat;
                child_vec.push(pat_inner.into());
                child_vec
            },
        }
    }
}

impl From<syn::PatIdent> for SyntaxObject {
    fn from(pat: syn::PatIdent) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatIdent(pat.clone()),
            children: {
                let mut child_vec = Vec::new();
                match pat.subpat {
                    Some((_, box_pat)) => child_vec.push((*box_pat).into()),
                    None => (),
                };
                child_vec
            },
        }
    }
}

impl From<syn::PatLit> for SyntaxObject {
    fn from(pat: syn::PatLit) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatLit(pat.clone()),
            children: {
                let mut child_vec = Vec::new();
                child_vec.push((*pat.expr).into());
                child_vec
            },
        }
    }
}

impl From<syn::PatMacro> for SyntaxObject {
    fn from(pat: syn::PatMacro) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatMacro(pat.clone()),
            children: Vec::new(),
        }
    }
}

impl From<syn::PatOr> for SyntaxObject {
    fn from(pat: syn::PatOr) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatOr(pat.clone()),
            children: { pat.cases.iter().map(|pat| pat.to_owned().into()).collect() },
        }
    }
}

impl From<syn::PatPath> for SyntaxObject {
    fn from(pat: syn::PatPath) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::PatPath(pat.clone()),
            children: {
                // handle qself!
                panic!();
                Vec::new()
            },
        }
    }
}

impl From<syn::Type> for SyntaxObject {
    fn from(typ: syn::Type) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::Type(typ.clone()),
            children: {
                panic!();
                Vec::new()
            },
        }
    }
}

impl From<syn::TypeArray> for SyntaxObject {
    fn from(typ: syn::TypeArray) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::TypeArray(typ.clone()),
            children: {
                let mut child_vec = Vec::new();
                child_vec.push((*typ.elem).into());
                child_vec
            },
        }
    }
}

impl From<syn::TypeBareFn> for SyntaxObject {
    fn from(typ: syn::TypeBareFn) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::TypeBareFn(typ.clone()),
            children: {
                let mut child_vec: Vec<SyntaxObject> = Vec::from(
                    typ.inputs
                        .iter()
                        .map(|fn_arg| fn_arg.ty.to_owned().into())
                        .collect::<Vec<SyntaxObject>>(),
                );
                match typ.output {
                    syn::ReturnType::Default => (),
                    syn::ReturnType::Type(_, box_typ) => child_vec.push((*box_typ).into()),
                }
                child_vec
            },
        }
    }
}

impl From<syn::TypeGroup> for SyntaxObject {
    fn from(typ: syn::TypeGroup) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::TypeGroup(typ.clone()),
            children: {
                let mut child_vec = Vec::new();
                child_vec.push((*typ.elem).into());
                child_vec
            },
        }
    }
}

impl From<syn::TypeImplTrait> for SyntaxObject {
    fn from(typ: syn::TypeImplTrait) -> Self {
        SyntaxObject {
            inherited: Vec::new(),
            synthesized: Vec::new(),
            syntax: Syntax::TypeImplTrait(typ.clone()),
            children: {
                let child_vec = Vec::new();
                child_vec
            },
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn cond_exp_single() -> Result<(), syn::Error> {
        let ast_nodes = syn::parse_str::<syn::Expr>("if true { 1 }")?;

        let _stx_obj: SyntaxObject = ast_nodes.into();

        Ok(())
    }

    #[test]
    fn cond_exp_lit() -> Result<(), syn::Error> {
        let ast_nodes = syn::parse_str::<syn::Expr>("if true { 1 } else { 2 }")?;

        let _stx_obj: SyntaxObject = ast_nodes.into();

        // Output for `1`
        //
        // SyntaxObject {
        //     inherited: [],
        //     synthesized: [],
        //     syntax: Expr(Lit(ExprLit { attrs: [], lit: Int(LitInt { token: 1 }) })),
        //     children: [
        //         SyntaxObject {
        //             inherited: [],
        //             synthesized: [],
        //             syntax: ExprLit(ExprLit { attrs: [] , lit: Int(LitInt { token: 1 }) }),
        //             children: [
        //                 SyntaxObject {
        //                     inherited: [],
        //                     synthesized: [],
        //                     syntax: Lit(Int(LitInt { token: 1 })),
        //                     children: [
        //                         SyntaxObject {
        //                             inherited: [],
        //                             synthesized: [],
        //                             syntax: LitInt(LitInt { token: 1 }),
        //                             children: []
        //                         }
        //                     ]
        //                 }
        //             ]
        //         }
        //     ]
        // }

        Ok(())
    }

    #[test]
    fn cond_exp_var() -> Result<(), syn::Error> {
        let ast_nodes = syn::parse_str::<syn::Expr>("if true { a } else { 2 }")?;

        let _stx_obj: SyntaxObject = ast_nodes.into();

        Ok(())
    }

    #[test]
    fn cond_exp_let() -> Result<(), syn::Error> {
        let ast_nodes = syn::parse_str::<syn::Stmt>("{ let a = 1; if true { a } else { 2 } }")?;

        let _stx_obj: SyntaxObject = ast_nodes.into();

        Ok(())
    }
}

fn main() {}
