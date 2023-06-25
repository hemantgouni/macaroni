#![allow(dead_code)]

mod instantiate;
mod ordered_env;
mod poly;
mod subtyping;
mod well_formed;

use crate::check::ordered_env::OrdEnvElem;
use crate::data::{Env, Ident, Lit, Toplevel, AST};
use crate::utils::VecUtils;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct UVar(pub String);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EVar(pub String);

impl EVar {
    pub fn new_unique() -> EVar {
        EVar(crate::utils::get_unique_id())
    }
}

// Remember, higher rank polymorphism is impredicativity ONLY for function constructors, which is
// why Func is specially a Type here (can contain foralls). A predicative (or prenex) system
// wouldn't have Func here, either
#[derive(Debug, Eq, Clone)]
pub enum Type {
    Forall(UVar, Box<Type>),
    // We can't instantiate this type to one that contains a forall without impredicativity!
    // List(Box<Type>),
    Func(Vec<Type>, Box<Type>),
    Monotype(Monotype),
}

// TODO: these PartialEq impls are bug-prone, because they won't give warnings if we add more
// constructors. Make this a derive macro, perhaps?
impl PartialEq for Type {
    fn eq(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::Monotype(Monotype::Bottom), _) => true,
            (_, Type::Monotype(Monotype::Bottom)) => true,
            // TODO: is this right?
            (Type::Forall(uvar1, typ1), Type::Forall(uvar2, typ2))
                if uvar1 == uvar2 && typ1 == typ2 =>
            {
                true
            }
            // (Type::List(typ1), Type::List(typ2)) if typ1 == typ2 => true,
            (Type::Func(arg_typ1, res_typ1), Type::Func(arg_typ2, res_typ2))
                if arg_typ1 == arg_typ2 && res_typ1 == res_typ2 =>
            {
                true
            }
            (Type::Monotype(monotyp1), Type::Monotype(monotyp2)) if monotyp1 == monotyp2 => true,
            _ => false,
        }
    }
}

impl Type {
    pub fn substitute(&self, target: &UVar, replacement: &EVar) -> Self {
        match self {
            Type::Forall(uvar, _) if target == uvar => {
                panic!("Misguided attempt to replace unfree uvar!")
            }
            Type::Forall(uvar, typ) => Type::Forall(
                uvar.to_owned(),
                Box::new((*typ).substitute(target, replacement)),
            ),
            Type::Func(arg_types, res_type) => Type::Func(
                arg_types
                    .iter()
                    .map(|arg_type| arg_type.substitute(target, replacement))
                    .collect(),
                Box::new(res_type.substitute(target, replacement)),
            ),
            Type::Monotype(monotype) => Type::Monotype(monotype.substitute(target, replacement)),
        }
    }

    pub fn free_evars(&self) -> Vec<EVar> {
        match self {
            Type::Forall(UVar(uvar_str), type_quantified) => type_quantified
                .free_evars()
                .iter()
                .filter(|EVar(evar_str)| uvar_str != evar_str)
                .map(|evar| evar.to_owned())
                .collect(),
            Type::Func(arg_types, res_type) => arg_types
                .iter()
                .flat_map(|arg_type| arg_type.free_evars().to_owned())
                .collect::<Vec<EVar>>()
                .append_immutable(&res_type.free_evars()),
            Type::Monotype(monotype) => monotype.free_evars(),
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

impl Monotype {
    fn substitute(&self, target: &UVar, replacement: &EVar) -> Self {
        match self {
            Monotype::UVar(uvar) if target == uvar => Monotype::EVar(replacement.to_owned()),
            Monotype::List(monotype) => {
                Monotype::List(Box::new(monotype.substitute(target, replacement)))
            }
            Monotype::Func(arg_types, res_type) => Monotype::Func(
                arg_types
                    .iter()
                    .map(|arg_type| arg_type.substitute(target, replacement))
                    .collect(),
                Box::new(res_type.substitute(target, replacement)),
            ),
            _ => self.to_owned(),
        }
    }

    fn free_evars(&self) -> Vec<EVar> {
        match self {
            Monotype::EVar(evar) => vec![evar.to_owned()],
            Monotype::List(monotype) => monotype.free_evars(),
            Monotype::Func(arg_monotypes, res_monotype) => arg_monotypes
                .iter()
                .flat_map(|arg_monotype| arg_monotype.free_evars().to_owned())
                .collect::<Vec<EVar>>()
                .append_immutable(&res_monotype.free_evars()),
            Monotype::Bottom
            | Monotype::UVar(..)
            | Monotype::I64
            | Monotype::Bool
            | Monotype::String
            | Monotype::Symbol => Vec::new(),
        }
    }
}

impl PartialEq for Monotype {
    fn eq(&self, other: &Monotype) -> bool {
        match (self, other) {
            (Monotype::Bottom, _) => true,
            (_, Monotype::Bottom) => true,
            // TODO: is this right?
            (Monotype::UVar(str1), Monotype::UVar(str2)) if str1 == str2 => true,
            (Monotype::EVar(evar1), Monotype::EVar(evar2)) if evar1 == evar2 => true,
            (Monotype::I64, Monotype::I64) => true,
            (Monotype::Bool, Monotype::Bool) => true,
            (Monotype::String, Monotype::String) => true,
            (Monotype::Symbol, Monotype::Symbol) => true,
            (Monotype::List(typ1), Monotype::List(typ2)) if typ1 == typ2 => true,
            (Monotype::Func(arg_typ1, res_typ1), Monotype::Func(arg_typ2, res_typ2))
                if arg_typ1 == arg_typ2 && res_typ1 == res_typ2 =>
            {
                true
            }
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Expected(Type);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Given(Type);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeError {
    Mismatch(Expected, Given),
    SubtypeMismatch(Expected, Given),
    TVarNotFound(Ident),
    UVarNotFound(UVar),
    EVarNotFound(EVar),
    OrdEnvElemNotFound(OrdEnvElem),
    ImpredicativeForall(Type),
    Occurs(EVar, Type),
    Message(String),
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
                    Expected(Type::Monotype(ty)),
                    Given(Type::Monotype(infer_lit(next.clone())?)),
                )),
                Ok(_) => Ok(infer_lit(next.clone())?),
                Err(_) => prev,
            })
            .map(|ty| Monotype::List(Box::new(ty))),
    }
}

fn list_impredicativity_check(typ: &Type) -> Result<Monotype, TypeError> {
    match typ {
        Type::Forall(..) => Err(TypeError::ImpredicativeForall(typ.to_owned())),
        Type::Func(arg_types, res_type) => Ok(Monotype::Func(
            arg_types
                .iter()
                .fold(Ok(Vec::new()), |arg_types_or_err, arg_type| {
                    Ok(arg_types_or_err?.push_immutable(&list_impredicativity_check(arg_type)?))
                })?,
            Box::new(list_impredicativity_check(res_type)?),
        )),
        Type::Monotype(monotyp) => Ok(monotyp.to_owned()),
    }
}

fn infer_expr(expr: AST, env: Env<Type>) -> Result<Type, TypeError> {
    match expr {
        AST::Lit(lit) => Ok(Type::Monotype(infer_lit(lit)?)),
        AST::Type(ref ty, expr) => match check_expr(*expr, env, ty.clone()) {
            Ok(()) => Ok(ty.clone()),
            Err(tyerr) => Err(tyerr),
        },
        AST::Concat(expr1, expr2) => {
            match (
                check_expr(*expr1, env.clone(), Type::Monotype(Monotype::String)),
                check_expr(*expr2, env, Type::Monotype(Monotype::String)),
            ) {
                (Ok(()), Ok(())) => Ok(Type::Monotype(Monotype::String)),
                // TODO: Need to figure out a way to merge errors
                (Err(tyerr), _) | (_, Err(tyerr)) => Err(tyerr),
            }
        }
        AST::Add(expr1, expr2)
        | AST::Mult(expr1, expr2)
        | AST::Sub(expr1, expr2)
        | AST::Div(expr1, expr2) => {
            match (
                check_expr(*expr1, env.clone(), Type::Monotype(Monotype::I64)),
                check_expr(*expr2, env, Type::Monotype(Monotype::I64)),
            ) {
                (Ok(_), Ok(_)) => Ok(Type::Monotype(Monotype::I64)),
                // TODO: Need to figure out a way to merge errors
                (Err(tyerr), _) | (_, Err(tyerr)) => Err(tyerr),
            }
        }
        AST::List(elems) => match elems.as_slice() {
            [] => Ok(Type::Monotype(Monotype::List(Box::new(Monotype::Bottom)))),
            [first, rest @ ..] => {
                let expected_elem_type: Type = infer_expr(first.clone(), env.clone())?;
                rest.iter().fold(
                    Ok(Type::Monotype(Monotype::List(Box::new(
                        list_impredicativity_check(&expected_elem_type.clone())?,
                    )))),
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
            match check_expr(
                *list,
                env,
                Type::Monotype(Monotype::List(Box::new(list_impredicativity_check(
                    &ty.clone(),
                )?))),
            ) {
                Ok(()) => Ok(Type::Monotype(Monotype::List(Box::new(
                    list_impredicativity_check(&ty)?,
                )))),
                Err(ty_err) => Err(ty_err),
            }
        }
        AST::Cdr(list) => infer_expr(*list, env),
        AST::Car(list) => match infer_expr(*list, env) {
            Ok(Type::Monotype(Monotype::List(typ))) => Ok(Type::Monotype(*typ)),
            Ok(typ) => Err(TypeError::Mismatch(
                Expected(Type::Monotype(Monotype::List(Box::new(Monotype::Bottom)))),
                Given(typ),
            )),
            Err(typ_err) => Err(typ_err),
        },
        AST::Emptyp(list) => match infer_expr(*list, env) {
            Ok(Type::Monotype(Monotype::List(_))) => Ok(Type::Monotype(Monotype::Bool)),
            Ok(typ) => Err(TypeError::Mismatch(
                Expected(Type::Monotype(Monotype::List(Box::new(Monotype::Bottom)))),
                Given(typ),
            )),
            Err(typ_err) => Err(typ_err),
        },
        AST::Var(ident) => env
            .lookup(&ident)
            .map_err(|_| TypeError::TVarNotFound(ident)),
        AST::App(lambda, args) => match infer_expr(*lambda, env.clone())? {
            Type::Func(arg_types, res_type) => arg_types.clone().iter().zip(args.iter()).fold(
                Ok(Type::Func(arg_types, res_type)),
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
                Expected(Type::Func(
                    vec![Type::Monotype(Monotype::Bottom)],
                    Box::new(Type::Monotype(Monotype::Bottom)),
                )),
                Given(other),
            )),
        },
        AST::Call(name, args) => {
            let func_sig = env
                .lookup(&name)
                .map_err(|_| TypeError::TVarNotFound(name))?;

            match func_sig {
                Type::Func(arg_types, res_type) => args.iter().zip(arg_types.iter()).fold(
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
                    Expected(Type::Func(
                        vec![Type::Monotype(Monotype::Bottom)],
                        Box::new(Type::Monotype(Monotype::Bottom)),
                    )),
                    Given(other),
                )),
            }
        }
        other => todo!("{:?}", other),
    }
}

fn check_expr(expr: AST, mut env: Env<Type>, expected: Type) -> Result<(), TypeError> {
    match expr {
        // prevent shadowing with different type, maybe?
        AST::Let(name, binding, body) => {
            let binding_type = infer_expr(*binding, env.clone())?;
            check_expr(*body, env.insert(name, binding_type), expected)
        }
        AST::Ite(guard, branch1, branch2) => {
            match (
                check_expr(*guard, env.clone(), Type::Monotype(Monotype::Bool)),
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
            Type::Func(arg_types, body_type) if args.len() == arg_types.len() => {
                let args_env: Env<Type> =
                    args.iter()
                        .zip(arg_types.iter())
                        .fold(env, |mut env, arg_and_type| {
                            env.insert(arg_and_type.0.clone(), arg_and_type.1.clone())
                        });
                check_expr(*body, args_env, *body_type)
            }
            // TODO: Another place where the TypeError type needs to be extended
            other => Err(TypeError::Mismatch(
                Expected(Type::Func(
                    Vec::new(),
                    Box::new(Type::Monotype(Monotype::Bottom)),
                )),
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

fn check_top(exprs: Vec<AST>, mut env: Env<Type>) -> Result<(), TypeError> {
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
                .map_err(|_| TypeError::TVarNotFound(name.to_owned()))?,
        ) {
            Ok(()) => check_top(rest.to_vec(), env.to_owned()),
            other => other,
        },
        [AST::Macro(..), rest @ ..] => check_top(rest.to_vec(), env.to_owned()),
        [expr] => check_expr(expr.to_owned(), env, Type::Monotype(Monotype::Bottom)),
        _ => Err(TypeError::Mismatch(
            Expected(Type::Monotype(Monotype::Bottom)),
            Given(Type::Monotype(Monotype::Bottom)),
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

        assert_eq!(result, Type::Monotype(Monotype::I64))
    }

    #[test]
    fn test_typecheck_simple_err() {
        let ast = tokenize("(: I64 (+ (: I64 true) (: I64 1)))")
            .unwrap()
            .parse();

        let result = infer_expr(ast, Env::new()).unwrap_err();

        assert_eq!(
            result,
            TypeError::Mismatch(
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::Bool))
            ),
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
            TypeError::Mismatch(
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
            ),
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

        let result = check_expr(ast, Env::new(), Type::Monotype(Monotype::I64));

        assert_eq!(result, Ok(()));
    }

    #[test]
    fn typecheck_let_err() {
        let ast = tokenize(r#"(let var1 2 (let var2 "hello" (+ var1 var2)))"#)
            .unwrap()
            .parse();

        let result = check_expr(ast, Env::new(), Type::Monotype(Monotype::I64)).unwrap_err();

        assert_eq!(
            result,
            TypeError::Mismatch(
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
            ),
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
            Type::Func(
                vec![Type::Monotype(Monotype::I64), Type::Monotype(Monotype::I64)],
                Box::new(Type::Monotype(Monotype::I64)),
            ),
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
                Expected(Type::Monotype(Monotype::String)),
                Given(Type::Monotype(Monotype::I64))
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Monotype(Monotype::String)),
                Given(Type::Monotype(Monotype::I64))
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
                Expected(Type::Monotype(Monotype::List(Box::new(Monotype::String)))),
                Given(Type::Monotype(Monotype::List(Box::new(Monotype::I64)))),
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Monotype(Monotype::List(Box::new(Monotype::String)))),
                Given(Type::Monotype(Monotype::List(Box::new(Monotype::I64))))
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::String))
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
                Expected(Type::Func(
                    vec![Type::Monotype(Monotype::I64), Type::Monotype(Monotype::I64)],
                    Box::new(Type::Monotype(Monotype::I64))
                )),
                Given(Type::Func(
                    vec![Type::Monotype(Monotype::I64), Type::Monotype(Monotype::I64)],
                    Box::new(Type::Monotype(Monotype::String))
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
            Err(TypeError::TVarNotFound(Ident(
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
