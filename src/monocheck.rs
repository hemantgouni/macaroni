#![allow(dead_code)]

use crate::data::{Env, Ident, Lit, Toplevel, AST};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UVar(pub String);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EVar(pub String);

pub enum OrderedEnvElem {
    UVar(UVar),
    TVar(Ident, Type),
    EVar(EVar),
    ESol(EVar, Monotype),
    Marker(EVar),
}

#[derive(Debug, Eq, Clone)]
pub enum Type {
    Forall(Box<Type>),
    List(Box<Type>),
    Func(Vec<Type>, Box<Type>),
    Monotype(Monotype),
}

impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Forall(ty1), Type::Forall(ty2)) if ty1 == ty2 => true,
            (Type::Monotype(mono_ty1), Type::Monotype(mono_ty2)) if mono_ty1 == mono_ty2 => true,
            (Type::Func(arg_ty1, ret_ty1), Type::Func(arg_ty2, ret_ty2))
                if arg_ty1 == arg_ty2 && ret_ty1 == ret_ty2 =>
            {
                true
            }
            _ => false,
        }
    }
}

#[derive(Debug, Eq, Clone)]
pub enum Monotype {
    Bottom,
    UVar(UVar),
    EVar(EVar),
    I64,
    Bool,
    String,
    Symbol,
    List(Box<Monotype>),
    Func(Vec<Monotype>, Box<Monotype>),
}

impl PartialEq for Monotype {
    fn eq(&self, other: &Monotype) -> bool {
        match (self, other) {
            (Monotype::Bottom, _) => true,
            (_, Monotype::Bottom) => true,
            // TODO: is this right?
            (Monotype::UVar(str1), Monotype::UVar(str2)) if str1 == str2 => true,
            (Monotype::I64, Monotype::I64) => true,
            (Monotype::Bool, Monotype::Bool) => true,
            (Monotype::String, Monotype::String) => true,
            (Monotype::Symbol, Monotype::Symbol) => true,
            (Monotype::List(ty1), Monotype::List(ty2)) if ty1 == ty2 => true,
            (Monotype::Func(arg_ty1, ret_ty1), Monotype::Func(arg_ty2, ret_ty2))
                if arg_ty1 == arg_ty2 && ret_ty1 == ret_ty2 =>
            {
                true
            }
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Expected(Monotype);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Given(Monotype);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeError {
    Mismatch(Expected, Given),
    LookupFailure(Ident),
}

fn infer_lit(expr: Lit) -> Result<Monotype, TypeError> {
    match expr {
        Lit::I64(_) => Ok(Monotype::I64),
        Lit::Bool(_) => Ok(Monotype::Bool),
        Lit::String(_) => Ok(Monotype::String),
        Lit::Symbol(_) => Ok(Monotype::Symbol),
        Lit::List(lits) => lits
            .iter()
            .fold(Ok(Monotype::Bottom), |prev, next| match prev {
                Ok(ty) if ty != infer_lit(next.clone())? => Err(TypeError::Mismatch(
                    Expected(ty),
                    Given(infer_lit(next.clone())?),
                )),
                Ok(_) => Ok(infer_lit(next.clone())?),
                Err(_) => prev,
            })
            .map(|ty| Monotype::List(Box::new(ty))),
    }
}

fn infer_expr(expr: AST, env: Env<Monotype>) -> Result<Monotype, TypeError> {
    match expr {
        AST::Lit(lit) => infer_lit(lit),
        AST::Type(ref ty, expr) => match check_expr(*expr, env, ty.clone()) {
            Ok(()) => Ok(ty.clone()),
            Err(tyerr) => Err(tyerr),
        },
        AST::Concat(expr1, expr2) => {
            match (
                check_expr(*expr1, env.clone(), Monotype::String),
                check_expr(*expr2, env, Monotype::String),
            ) {
                (Ok(()), Ok(())) => Ok(Monotype::String),
                // TODO: Need to figure out a way to merge errors
                (Err(tyerr), _) | (_, Err(tyerr)) => Err(tyerr),
            }
        }
        AST::Add(expr1, expr2)
        | AST::Mult(expr1, expr2)
        | AST::Sub(expr1, expr2)
        | AST::Div(expr1, expr2) => {
            match (
                check_expr(*expr1, env.clone(), Monotype::I64),
                check_expr(*expr2, env, Monotype::I64),
            ) {
                (Ok(_), Ok(_)) => Ok(Monotype::I64),
                // TODO: Need to figure out a way to merge errors
                (Err(tyerr), _) | (_, Err(tyerr)) => Err(tyerr),
            }
        }
        AST::List(elems) => match elems.as_slice() {
            [] => Ok(Monotype::List(Box::new(Monotype::Bottom))),
            [first, rest @ ..] => {
                let expected_elem_type: Monotype = infer_expr(first.clone(), env.clone())?;
                rest.iter().fold(
                    Ok(Monotype::List(Box::new(expected_elem_type.clone()))),
                    |prev, next| match (
                        prev,
                        check_expr(next.clone(), env.clone(), expected_elem_type.clone()),
                    ) {
                        (Ok(typ), Ok(())) => Ok(typ),
                        (Err(typ_err), _) => Err(typ_err),
                        (Ok(_), Err(typ_err)) => Err(typ_err),
                    },
                )
            }
        },
        AST::Cons(elem, list) => {
            let ty = infer_expr(*elem, env.clone())?;
            match check_expr(*list, env, Monotype::List(Box::new(ty.clone()))) {
                Ok(()) => Ok(Monotype::List(Box::new(ty))),
                Err(ty_err) => Err(ty_err),
            }
        }
        AST::Cdr(list) => infer_expr(*list, env),
        AST::Car(list) => match infer_expr(*list, env) {
            Ok(Monotype::List(typ)) => Ok(*typ),
            Ok(typ) => Err(TypeError::Mismatch(
                Expected(Monotype::List(Box::new(Monotype::Bottom))),
                Given(typ),
            )),
            Err(typ_err) => Err(typ_err),
        },
        AST::Emptyp(list) => match infer_expr(*list, env) {
            Ok(Monotype::List(_)) => Ok(Monotype::Bool),
            Ok(typ) => Err(TypeError::Mismatch(
                Expected(Monotype::List(Box::new(Monotype::Bottom))),
                Given(typ),
            )),
            Err(typ_err) => Err(typ_err),
        },
        AST::Var(ident) => env
            .lookup(&ident)
            .map_err(|_| TypeError::LookupFailure(ident)),
        AST::App(lambda, args) => match infer_expr(*lambda, env.clone())? {
            Monotype::Func(arg_types, res_type) => arg_types.clone().iter().zip(args.iter()).fold(
                Ok(Monotype::Func(arg_types, res_type)),
                |res, (expected, given_arg)| match (
                    res,
                    check_expr(given_arg.clone(), env.clone(), expected.clone()),
                ) {
                    (Err(typ_err), _) => Err(typ_err),
                    (Ok(_), Err(typ_err)) => Err(typ_err),
                    (Ok(typ), Ok(())) => Ok(typ),
                },
            ),
            other => Err(TypeError::Mismatch(
                Expected(Monotype::Func(
                    vec![Monotype::Bottom],
                    Box::new(Monotype::Bottom),
                )),
                Given(other),
            )),
        },
        AST::Call(name, args) => {
            let func_sig = env
                .lookup(&name)
                .map_err(|_| TypeError::LookupFailure(name))?;

            match func_sig {
                Monotype::Func(arg_types, res_type) => args.iter().zip(arg_types.iter()).fold(
                    Ok(*res_type),
                    |res, (given_arg, expected_type)| match (
                        res,
                        check_expr(given_arg.clone(), env.clone(), expected_type.clone()),
                    ) {
                        (Err(typ_err), _) | (Ok(_), Err(typ_err)) => Err(typ_err),
                        (Ok(typ), Ok(())) => Ok(typ),
                    },
                ),
                other => Err(TypeError::Mismatch(
                    Expected(Monotype::Func(
                        vec![Monotype::Bottom],
                        Box::new(Monotype::Bottom),
                    )),
                    Given(other),
                )),
            }
        }
        other => todo!("{:?}", other),
    }
}

fn check_expr(expr: AST, mut env: Env<Monotype>, expected: Monotype) -> Result<(), TypeError> {
    match expr {
        // prevent shadowing with different type, maybe?
        AST::Let(name, binding, body) => {
            let binding_type = infer_expr(*binding, env.clone())?;
            check_expr(*body, env.insert(name, binding_type), expected)
        }
        AST::Ite(guard, branch1, branch2) => {
            match (
                check_expr(*guard, env.clone(), Monotype::Bool),
                check_expr(*branch1, env.clone(), expected.clone()),
                check_expr(*branch2, env.clone(), expected),
            ) {
                (Ok(()), Ok(()), Ok(())) => Ok(()),
                (Err(typ_err), _, _) | (_, Err(typ_err), _) | (_, _, Err(typ_err)) => Err(typ_err),
            }
        }
        // this is a top level form so we should probably register the name somewhere? or are we
        // assuming it's already registered as such?
        AST::Func(_, args, body) | AST::Lambda(args, body) => match expected {
            // ensure the argument numbers are the same
            // TODO: emit a more sensible type error for the case where they are not!
            Monotype::Func(arg_types, body_type) if args.len() == arg_types.len() => {
                let args_env: Env<Monotype> =
                    args.iter()
                        .zip(arg_types.iter())
                        .fold(env, |mut env, arg_and_type| {
                            env.insert(arg_and_type.0.clone(), arg_and_type.1.clone())
                        });
                check_expr(*body, args_env, *body_type)
            }
            // TODO: Another place where the TypeError type needs to be extended
            other => Err(TypeError::Mismatch(
                Expected(Monotype::Func(Vec::new(), Box::new(Monotype::Bottom))),
                Given(other),
            )),
        },
        // We can call this with Type::Bottom to start type checking if the top level
        // expr is unannotated? Since Bottom is equal to any other type
        //
        // TODO: use type_eq_or_err here?
        //
        // the subsumption rule is here
        _ => match infer_expr(expr, env) {
            Ok(given) => {
                if given == expected {
                    Ok(())
                } else {
                    Err(TypeError::Mismatch(Expected(expected), Given(given)))
                }
            }
            Err(tyerr) => Err(tyerr),
        },
    }
}

fn check_top(exprs: Vec<AST>, mut env: Env<Monotype>) -> Result<(), TypeError> {
    match exprs.as_slice() {
        [AST::TypeDec(name, func_type), rest @ ..] => check_top(
            rest.to_vec(),
            env.insert(name.to_owned(), func_type.to_owned()),
        ),
        // type checking the function body here
        [func @ AST::Func(name, ..), rest @ ..] => match check_expr(
            func.to_owned(),
            env.clone(),
            env.lookup(name)
                .map_err(|_| TypeError::LookupFailure(name.to_owned()))?,
        ) {
            Ok(()) => check_top(rest.to_vec(), env.to_owned()),
            other => other,
        },
        [AST::Macro(..), rest @ ..] => check_top(rest.to_vec(), env.to_owned()),
        [expr] => check_expr(expr.to_owned(), env, Monotype::Bottom),
        _ => Err(TypeError::Mismatch(
            Expected(Monotype::Bottom),
            Given(Monotype::Bottom),
        )),
    }
}

pub fn check(Toplevel(ast): Toplevel) -> Result<(), TypeError> {
    check_top(ast, Env::new())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::expand::expand;
    use crate::parse::tokenize;

    #[test]
    fn test_typecheck_simple() {
        let ast = tokenize("(: I64 (+ (: I64 1) (: I64 1)))").unwrap().parse();

        let result = infer_expr(ast, Env::new()).unwrap();

        assert_eq!(result, Monotype::I64)
    }

    #[test]
    fn test_typecheck_simple_err() {
        let ast = tokenize("(: I64 (+ (: I64 true) (: I64 1)))")
            .unwrap()
            .parse();

        let result = infer_expr(ast, Env::new()).unwrap_err();

        assert_eq!(
            result,
            TypeError::Mismatch(Expected(Monotype::I64), Given(Monotype::Bool)),
        )
    }

    #[test]
    fn typecheck_lit_list() {
        let lit = Lit::List(vec![Lit::I64(1), Lit::I64(2), Lit::I64(3), Lit::I64(4)]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Monotype::List(Box::new(Monotype::I64))))
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
            TypeError::Mismatch(Expected(Monotype::I64), Given(Monotype::String)),
        )
    }

    #[test]
    fn typecheck_lit_list_small() {
        let lit = Lit::List(vec![Lit::I64(1)]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Monotype::List(Box::new(Monotype::I64))))
    }

    #[test]
    fn typecheck_lit_list_empty() {
        let lit = Lit::List(vec![]);

        let result = infer_lit(lit);

        assert_eq!(result, Ok(Monotype::List(Box::new(Monotype::I64))))
    }

    #[test]
    fn typecheck_let() {
        let ast = tokenize("(let var1 2 (let var2 9 (+ var1 var2)))")
            .unwrap()
            .parse();

        let result = check_expr(ast, Env::new(), Monotype::I64);

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn typecheck_let_err() {
        let ast = tokenize(r#"(let var1 2 (let var2 "hello" (+ var1 var2)))"#)
            .unwrap()
            .parse();

        let result = check_expr(ast, Env::new(), Monotype::I64).unwrap_err();

        assert_eq!(
            result,
            TypeError::Mismatch(Expected(Monotype::I64), Given(Monotype::String)),
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
            Monotype::Func(vec![Monotype::I64, Monotype::I64], Box::new(Monotype::I64)),
        );

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_call() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add (-> (I64 I64) I64))
                    (fn add (operand1 operand2)
                      (/ operand1 operand2))
                    (: I64 (add 1 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_call_err() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add (-> (I64 I64) I64))
                    (fn add (operand1 operand2)
                      (/ operand1 operand2))
                    (: String (add 1 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::String),
                Given(Monotype::I64)
            ))
        )
    }

    #[test]
    fn typecheck_func_err() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add (-> (I64 I64) I64))
                    (fn add (operand1 operand2)
                      (+ operand1 "hello :)"))
                    (: String (add 1 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    #[test]
    fn typecheck_lambda_1() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 I64) I64)
                       (lambda (arg1 arg2) (+ arg1 arg2))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_lambda_err_1() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 I64) I64)
                       (lambda (arg1 arg2) (+ arg1 "hey:)"))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    #[test]
    fn typecheck_lambda_err_2() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 I64) String)
                       (lambda (arg1 arg2) (+ arg1 arg2))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::String),
                Given(Monotype::I64)
            ))
        )
    }

    #[test]
    fn typecheck_lambda_2() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 I64) String)
                       (lambda (arg1 arg2) "hey:)")))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_lambda_3() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 (List I64)) (List I64))
                       (lambda (elem input-list)
                         (cons elem input-list))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_lambda_err_3() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((: (-> (I64 (List I64)) (List String))
                       (lambda (elem input-list)
                         (cons elem input-list))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::List(Box::new(Monotype::String))),
                Given(Monotype::List(Box::new(Monotype::I64))),
            ))
        )
    }

    #[test]
    fn typecheck_app_1() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"(((: (-> (I64 (List I64)) (List I64))
                        (lambda (elem input-list)
                          (cons elem input-list))) 1 (list 1 2 3 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_app_2() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare map (-> ((-> (I64) String) (List I64)) (List String)))
                    (fn map (f input-list)
                      (if (empty? input-list)
                        (list)
                        (cons (f (car input-list)) (map f (cdr input-list)))))
                    (map (lambda (elem) "hey!") (list 1 4 5 8)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_app_err_1() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"(((: (-> (I64 (List I64)) (List I64))
                        (lambda (elem input-list)
                          (cons elem input-list))) "hey" (list 1 2 3 4)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    #[test]
    fn typecheck_app_err_2() {
        // there's a subtle bug in this program. can you spot it? the type checker did!
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare map (-> ((-> (I64) String) (List I64)) (List String)))
                    (fn map (f input-list)
                      (if (empty? input-list)
                        (list)
                        (cons (f (car input-list)) (cdr input-list))))
                    (map (lambda (elem) "hey!") (list 1 4 5 8)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::List(Box::new(Monotype::String))),
                Given(Monotype::List(Box::new(Monotype::I64)))
            ))
        )
    }

    #[test]
    fn typecheck_app_let() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((let my-cons (: (-> (I64 (List I64)) (List I64))
                                    (lambda (elem input-list)
                                        (cons elem input-list)))
                      (my-cons 1 (list 1 2 3 4))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_app_let_err() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((let my-cons (: (-> (I64 (List I64)) (List I64))
                                    (lambda (elem input-list)
                                        (cons elem input-list)))
                      (my-cons "hey" (list 1 2 3 4))))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    #[test]
    fn typecheck_list() {
        let Toplevel(ast) =
            expand(tokenize(r#"((list 1 2 3 4))"#).unwrap().parse_toplevel()).unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    #[test]
    fn typecheck_list_err_1() {
        let Toplevel(ast) = expand(
            tokenize(r#"((list 1 "hey" 3 4))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    #[test]
    fn typecheck_list_err_2() {
        let Toplevel(ast) = expand(
            tokenize(r#"((list 1 (++ "hey" ":)") 3 4))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(
            result,
            Err(TypeError::Mismatch(
                Expected(Monotype::I64),
                Given(Monotype::String)
            ))
        )
    }

    // TODO: add support for closures? though we don't really have mutable objects, i suppose
    // TODO: add more App tests!
    #[test]
    fn typecheck_hof_1() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add (-> (I64 I64) I64))
                    (fn add (operand1 operand2)
                      (+ operand1 operand2))
                    (declare hof-add (-> ((-> (I64 I64) I64) I64 I64) I64))
                    (fn hof-add (hof operand1 operand2)
                      (hof operand1 operand2))
                    (: I64 (hof-add add 1 1)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(result, Ok(()))
    }

    // TODO: add tests for functions with wrong number of arguments from declaration
    #[test]
    fn typecheck_hof_2() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add-wrong-ret (-> (I64 I64) String))
                    (fn add-wrong-ret (operand1 operand2)
                      "hey:)")
                    (declare hof-add (-> ((-> (I64 I64) I64) I64 I64) I64))
                    (fn hof-add (hof operand1 operand2)
                      (hof operand1 operand2))
                    (: I64 (hof-add add-wrong-ret 1 1)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = dbg!(check_top(ast, Env::new()));

        assert_eq!(
            Err(TypeError::Mismatch(
                Expected(Monotype::Func(
                    vec![Monotype::I64, Monotype::I64],
                    Box::new(Monotype::I64)
                )),
                Given(Monotype::Func(
                    vec![Monotype::I64, Monotype::I64],
                    Box::new(Monotype::String)
                ))
            )),
            result
        )
    }

    #[test]
    fn typecheck_hof_3() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add-wrong-ret (-> (I64 I64) String))
                    (fn add-wrong-ret (operand1 operand2)
                      "hey:)")
                    (declare hof-add (-> ((-> (I64 I64) I64) I64 I64) I64))
                    (fn hof-add (hof operand1 operand2)
                      (hof operand1 operand2))
                    (: I64 (hof-add function-doesnt-exist 1 1)))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = dbg!(check_top(ast, Env::new()));

        assert_eq!(
            Err(TypeError::LookupFailure(Ident(
                "function-doesnt-exist".to_string()
            ))),
            result
        )
    }

    #[test]
    fn typecheck_func_3() {
        let Toplevel(ast) = expand(
            tokenize(
                r#"((declare add-wrong (-> (I64 I64) String))
                    (fn add-wrong ()
                      "hey:)")
                    (add-wrong 1 1))"#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let result = check_top(ast, Env::new());

        assert_eq!(matches!(result, Err(_)), true)
    }
}
