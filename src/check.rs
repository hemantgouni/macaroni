#![allow(dead_code)]

use crate::data::{Env, Lit, AST};

#[derive(Debug, Eq, Clone)]
pub enum Type {
    Bottom,
    Var(String),
    I64,
    Bool,
    String,
    Symbol,
    List(Box<Type>),
    Func(Box<Type>, Box<Type>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Bottom, _) => true,
            (_, Type::Bottom) => true,
            (Type::Var(..), Type::Var(..)) => true,
            (Type::I64, Type::I64) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::String, Type::String) => true,
            (Type::Symbol, Type::Symbol) => true,
            (Type::List(..), Type::List(..)) => true,
            (Type::Func(..), Type::Func(..)) => true,
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq)]
struct TypeError {
    expected: Type,
    given: Type,
}

fn type_eq_or_err(given: Type, expected: Type) -> Result<(), TypeError> {
    if expected == given {
        Ok(())
    } else {
        Err(TypeError { expected, given })
    }
}

fn infer_lit(expr: Lit) -> Result<Type, TypeError> {
    match expr {
        Lit::I64(_) => Ok(Type::I64),
        Lit::Bool(_) => Ok(Type::Bool),
        Lit::String(_) => Ok(Type::String),
        Lit::Symbol(_) => Ok(Type::Symbol),
        Lit::List(lits) => lits
            .iter()
            .fold(Ok(Type::Bottom), |prev, next| match prev {
                Ok(ty) if ty != infer_lit(next.clone())? => Err(TypeError {
                    expected: ty,
                    given: infer_lit(next.clone())?,
                }),
                Ok(_) => Ok(infer_lit(next.clone())?),
                Err(_) => prev,
            })
            .map(|ty| Type::List(Box::new(ty))),
    }
}

fn infer_expr(expr: AST, environment: Env) -> Result<Type, TypeError> {
    match expr {
        AST::Lit(lit) => infer_lit(lit),
        AST::Type(ref ty, expr) => match check_expr(*expr, environment, ty.clone()) {
            Ok(()) => Ok(ty.clone()),
            Err(tyerr) => Err(tyerr),
        },
        AST::Add(expr1, expr2)
        | AST::Mult(expr1, expr2)
        | AST::Sub(expr1, expr2)
        | AST::Div(expr1, expr2) => {
            match (
                check_expr(*expr1, environment.clone(), Type::I64),
                check_expr(*expr2, environment, Type::I64),
            ) {
                (Ok(_), Ok(_)) => Ok(Type::I64),
                // TODO: Need to figure out a way to merge errors
                (Err(tyerr), _) | (_, Err(tyerr)) => Err(tyerr),
            }
        }
        _ => todo!(),
    }
}

fn check_expr(expr: AST, environment: Env, expected: Type) -> Result<(), TypeError> {
    match expr {
        _ => match infer_expr(expr, environment) {
            Ok(ty) => {
                if ty == expected {
                    Ok(())
                } else {
                    Err(TypeError {
                        expected,
                        given: ty,
                    })
                }
            }
            Err(tyerr) => Err(tyerr),
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::data::Env;
    use crate::parse::tokenize;

    #[test]
    fn test_typecheck_simple() {
        let ast = tokenize("(: I64 (+ (: I64 1) (: I64 1)))").unwrap().parse();

        let result = infer_expr(ast, Env::new()).unwrap();

        assert_eq!(result, Type::I64)
    }

    #[test]
    fn test_typecheck_simple_err() {
        let ast = tokenize("(: I64 (+ (: I64 true) (: I64 1)))")
            .unwrap()
            .parse();

        let result = infer_expr(ast, Env::new()).unwrap_err();

        assert_eq!(
            result,
            TypeError {
                expected: Type::I64,
                given: Type::Bool
            }
        )
    }

    #[test]
    fn typecheck_lit_list() {
        let lit = Lit::List(vec![Lit::I64(1), Lit::I64(2), Lit::I64(3), Lit::I64(4)]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Type::List(Box::new(Type::I64))))
    }

    #[test]
    fn typecheck_lit_list_err() {
        let lit = Lit::List(vec![
            Lit::I64(1),
            Lit::I64(2),
            Lit::String("hey".to_string()),
            Lit::I64(4),
        ]);

        let result = infer_lit(lit).unwrap_err();

        assert_eq!(
            result,
            TypeError {
                expected: Type::I64,
                given: Type::String,
            }
        )
    }

    #[test]
    fn typecheck_lit_list_small() {
        let lit = Lit::List(vec![Lit::I64(1)]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Type::List(Box::new(Type::I64))))
    }

    #[test]
    fn typecheck_lit_list_empty() {
        let lit = Lit::List(vec![]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Type::List(Box::new(Type::I64))))
    }
}
