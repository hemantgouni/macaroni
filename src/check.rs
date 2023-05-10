#![allow(dead_code)]

use crate::data::{Env, Ident, Lit, Toplevel, AST};
use crate::expand::expand;

#[derive(Debug, Eq, Clone)]
pub enum Type {
    Bottom,
    Var(String),
    I64,
    Bool,
    String,
    Symbol,
    List(Box<Type>),
    Func(Vec<Type>, Box<Type>),
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        matches!(
            (self, other),
            (Type::Bottom, _)
                | (_, Type::Bottom)
                | (Type::Var(..), Type::Var(..))
                | (Type::I64, Type::I64)
                | (Type::Bool, Type::Bool)
                | (Type::String, Type::String)
                | (Type::Symbol, Type::Symbol)
                | (Type::List(..), Type::List(..))
                | (Type::Func(..), Type::Func(..))
        )
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

fn infer_expr(expr: AST, environment: Env<Type>) -> Result<Type, TypeError> {
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
        // TODO: Figure out a more sensible error message here, make the TypeError type able to
        // handle this
        //
        // Or maybe make a more generic error trait that has a .message method or something, since
        // a variable lookup failure isn't really a type error!
        AST::Var(ident) => environment.lookup(&ident).map_err(|_| TypeError {
            expected: Type::Bottom,
            given: Type::Bottom,
        }),
        AST::Call(name, args) => {
            let func_sig = environment.lookup(&name).map_err(|_| TypeError {
                expected: Type::Bottom,
                given: Type::Bottom,
            })?;

            match func_sig.clone() {
                Type::Func(arg_types, res_type) => {
                    if args
                        .iter()
                        .zip(arg_types.iter())
                        .all(|(arg, expected_type)| {
                            matches!(
                                check_expr(arg.clone(), environment.clone(), expected_type.clone()),
                                Ok(())
                            )
                        })
                    {
                        Ok(*res_type)
                    } else {
                        Err(TypeError {
                            expected: Type::Bottom,
                            given: Type::Bottom,
                        })
                    }
                }
                other => Err(TypeError {
                    expected: Type::Func(vec![Type::Bottom], Box::new(Type::Bottom)),
                    given: other,
                }),
            }
        }
        other => todo!("{:?}", other),
    }
}

fn check_expr(expr: AST, mut environment: Env<Type>, expected: Type) -> Result<(), TypeError> {
    match expr {
        // prevent shadowing with different type, maybe?
        AST::Let(name, binding, body) => {
            let binding_type = infer_expr(*binding, environment.clone())?;
            check_expr(*body, environment.insert(name, binding_type), expected)
        }
        // this is a top level form so we should probably register the name somewhere? or are we
        // assuming it's already registered as such?
        AST::Func(name, args, body) => match expected {
            Type::Func(arg_types, body_type) => {
                let args_env: Env<Type> =
                    args.iter()
                        .zip(arg_types.iter())
                        .fold(environment, |mut env, arg_and_type| {
                            env.insert(arg_and_type.0.clone(), arg_and_type.1.clone())
                        });
                check_expr(*body, args_env, *body_type)
            }
            // TODO: Another place where the TypeError type needs to be extended (or this needs to
            // be generalized into a trait) to handle more kinds of type checking failure cases
            other => Err(TypeError {
                expected: Type::Func(Vec::new(), Box::new(Type::Bottom)),
                given: other,
            }),
        },
        // We can call this with Type::Bottom to start type checking if the top level
        // expr is unannotated? Since Bottom is equal to any other type
        //
        // the subsumption rule is here
        _ => match infer_expr(expr, environment) {
            Ok(given) => {
                if given == expected {
                    Ok(())
                } else {
                    Err(TypeError { expected, given })
                }
            }
            Err(tyerr) => Err(tyerr),
        },
    }
}

// rename environment -> env
// improve error handling with a TypeError trait? Or something
// actually, use an enum

fn check_top(exprs: Vec<AST>, mut env: Env<Type>) -> Result<(), TypeError> {
    match exprs.as_slice() {
        [AST::TypeDec(name, func_type), rest @ ..] => check_top(
            rest.to_vec(),
            env.insert(name.to_owned(), func_type.to_owned()),
        ),
        [AST::Func(..) | AST::Macro(..), rest @ ..] => check_top(rest.to_vec(), env.to_owned()),
        [expr] => check_expr(expr.to_owned(), env, Type::Bottom),
        _ => Err(TypeError {
            expected: Type::Bottom,
            given: Type::Bottom,
        }),
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

    #[test]
    fn typecheck_let() {
        let ast = tokenize("(let var1 2 (let var2 9 (+ var1 var2)))")
            .unwrap()
            .parse();

        let result = check_expr(ast, Env::new(), Type::I64);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn typecheck_let_err() {
        let ast = tokenize(r#"(let var1 2 (let var2 "hello" (+ var1 var2)))"#)
            .unwrap()
            .parse();

        let result = check_expr(ast, Env::new(), Type::I64).unwrap_err();

        assert_eq!(
            result,
            TypeError {
                expected: Type::I64,
                given: Type::String
            }
        )
    }

    #[test]
    fn typecheck_func() {
        let Toplevel(ast) = tokenize(
            r#"((fn add (operand1 operand2)
                (+ operand1 operand2)))"#,
        )
        .unwrap()
        .parse_toplevel();

        let result = check_expr(
            ast.iter().next().unwrap().to_owned(),
            Env::new(),
            Type::Func(vec![Type::I64, Type::I64], Box::new(Type::I64)),
        );

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_call() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add (-> (I64 I64) I64))
                    (fn add (operand1 operand2)
                      (+ operand1 operand2))
                    (: I64 (add 1 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }
}
