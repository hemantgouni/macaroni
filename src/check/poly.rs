#![allow(dead_code)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::subtyping::subtype;
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Expected, Given, Ident, Lit, Monotype, Type, TypeError, UVar};
use crate::data::{Toplevel, AST};
use crate::utils::{UniqueString, VecUtils};

#[derive(Debug, Eq, PartialEq)]
struct InferOut {
    typ: Type,
    env: OrdEnv,
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

fn infer_expr(expr: AST, env: OrdEnv) -> Result<InferOut, TypeError> {
    println!("Infer\n========\nexpr: {:#?}\nenv: {:#?}\n", expr, env);
    match expr {
        // Var
        AST::Var(name) => env
            .type_for_tvar(name.clone())
            .map(|typ| InferOut { typ, env })
            .ok_or(TypeError::TVarNotFound(name)),
        // Anno
        AST::Type(typ, expr) => match well_formed(typ.clone(), env.clone()) {
            Ok(()) => {
                check_expr(*expr, typ.clone(), env).map(|out_env| InferOut { typ, env: out_env })
            }
            Err(type_error) => Err(type_error),
        },
        // 1I=>
        AST::Lit(lit) => infer_lit(lit).map(|monotype| InferOut {
            typ: Type::Monotype(monotype),
            env,
        }),
        // ->I=>
        AST::Lambda(args, body) => {
            let arg_evars: Vec<(Ident, EVar)> = args
                .iter()
                .map(|ident| ident.to_owned())
                .zip(args.iter().map(|_| EVar::new_unique()))
                .collect();

            let res_type = EVar::new_unique();

            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            let env_pre_tvar = env.add_all(
                arg_evars
                    .iter()
                    .map(|(_, evar)| OrdEnvElem::EVar(evar.to_owned()))
                    .collect::<Vec<OrdEnvElem>>()
                    .push_immutable(&OrdEnvElem::EVar(res_type.clone()))
                    .push_immutable(&unique_marker),
            );

            let new_env: OrdEnv =
                arg_evars
                    .iter()
                    .fold(env_pre_tvar, |accum_env, (ident, evar)| {
                        accum_env.add(OrdEnvElem::TVar(
                            ident.to_owned(),
                            Type::Monotype(Monotype::EVar(evar.to_owned())),
                        ))
                    });

            check_expr(
                *body,
                Type::Monotype(Monotype::EVar(res_type.clone())),
                new_env,
            )?
            .split_on(&unique_marker)
            .map(|(before_env, _, _)| InferOut {
                typ: Type::Func(
                    arg_evars
                        .iter()
                        .map(|(_, evar)| Type::Monotype(Monotype::EVar(evar.to_owned())))
                        .collect(),
                    Box::new(Type::Monotype(Monotype::EVar(res_type))),
                ),
                env: before_env,
            })
            .ok_or(TypeError::OrdEnvElemNotFound(unique_marker))
        }
        // ->E
        AST::App(lambda, args) => {
            let InferOut {
                typ: lambda_type,
                env: lambda_out_env,
            } = infer_expr(*lambda, env)?;

            apply_type(
                lambda_out_env.substitute_fixpoint(lambda_type),
                args,
                lambda_out_env,
            )
        }
        AST::Emptyp(list) => {
            let new_evar = EVar::new_unique();

            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            let new_env = env
                .add(unique_marker.clone())
                .add(OrdEnvElem::EVar(new_evar.clone()));

            let out_env = check_expr(
                *list,
                Type::Monotype(Monotype::List(Box::new(Monotype::EVar(new_evar)))),
                new_env,
            )?;

            // shouldn't be introducing any existentials here
            // so it's correct to select before_env
            Ok(InferOut {
                typ: Type::Monotype(Monotype::Bool),
                env: out_env
                    .split_on(&unique_marker)
                    .ok_or(TypeError::OrdEnvElemNotFound(unique_marker))
                    .map(|(before_env, _, _)| before_env)?,
            })
        }
        AST::Cons(elem, list) => {
            let InferOut {
                typ: elem_type,
                env: elem_env,
            } = infer_expr(*elem, env)?;

            match elem_type {
                Type::Monotype(elem_monotype) => {
                    let list_type = Type::Monotype(Monotype::List(Box::new(elem_monotype)));
                    // use elem_env here just in case elem_monotype is (or contains) an existential
                    // that was introduced during inference
                    check_expr(*list, list_type.clone(), elem_env).map(|env| InferOut {
                        typ: dbg!(env.substitute_fixpoint(list_type)),
                        env,
                    })
                }
                _ => Err(TypeError::ImpredicativeForall(elem_type)),
            }
        }
        AST::Car(list) => {
            let list_evar = EVar::new_unique();

            let list_type =
                Type::Monotype(Monotype::List(Box::new(Monotype::EVar(list_evar.clone()))));

            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            // TODO: possible source of bugs?
            check_expr(
                *list,
                list_type,
                env.add(OrdEnvElem::EVar(list_evar.clone()))
                    .add(unique_marker.clone()),
            )?
            .split_on(&unique_marker)
            .ok_or(TypeError::OrdEnvElemNotFound(unique_marker))
            .map(|(before_env, _, after_env)| InferOut {
                // should we be dropping the environment here? is it possible that existentials
                // survive...? yes, it is (if they can't be solved? but is that an error)
                env: before_env.clone(),
                typ: before_env
                    .concat(&after_env)
                    .substitute_fixpoint(Type::Monotype(Monotype::EVar(list_evar))),
            })
        }
        AST::Cdr(list) => {
            let list_evar = EVar::new_unique();

            let list_type =
                Type::Monotype(Monotype::List(Box::new(Monotype::EVar(list_evar.clone()))));

            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            check_expr(
                *list,
                list_type,
                env.add(OrdEnvElem::EVar(list_evar.clone()))
                    .add(unique_marker.clone()),
            )?
            .split_on(&unique_marker)
            .ok_or(TypeError::OrdEnvElemNotFound(unique_marker))
            .map(|(before_env, _, after_env)| InferOut {
                // should we be dropping the environment here? is it possible that existentials
                // survive...? yes, it is (if they can't be solved? but is that an error)
                env: before_env.clone(),
                typ: before_env
                    .concat(&after_env)
                    .substitute_fixpoint(Type::Monotype(Monotype::List(Box::new(Monotype::EVar(
                        list_evar,
                    ))))),
            })
        }
        AST::Ite(guard, branch1, branch2) => {
            let guard_env = check_expr(*guard, Type::Monotype(Monotype::Bool), env)?;

            let InferOut {
                typ: branch1_type,
                env: branch1_env,
                // must ALWAYS thread through the most recent environment!
            } = infer_expr(*branch1, guard_env)?;

            let branch2_env = check_expr(*branch2, branch1_type.clone(), branch1_env)?;

            Ok(InferOut {
                typ: branch1_type,
                env: branch2_env,
            })
        }
        AST::Call(func_name, args) => {
            let func_type = env
                .type_for_tvar(func_name.clone())
                .ok_or(TypeError::TVarNotFound(func_name))?;

            apply_type(env.substitute_fixpoint(func_type), args, env)
        }
        other => todo!("{:?}", other),
    }
}

fn check_expr(expr: AST, typ: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    println!(
        "Check\n========\nexpr: {:#?}\ntype: {:#?}\nenv: {:#?}\n",
        expr, typ, env
    );
    match (expr.clone(), typ.clone()) {
        // ForallI
        (_, Type::Forall(uvar, typ)) => {
            let unique_env_elem = OrdEnvElem::UniqueMarker(UniqueString::new());

            let env_appended = env
                .add(unique_env_elem.clone())
                .add(OrdEnvElem::UVar(uvar.clone()));

            check_expr(expr, *typ, env_appended.clone())?
                .split_on(&unique_env_elem)
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::UVarNotFound(uvar))
        }
        // ->I
        (AST::Lambda(ast_args, ast_body), Type::Func(arg_types, res_type))
            if ast_args.len() == arg_types.len() =>
        {
            // TODO: kind of a hack, rework this a bit when we have an a-normal pass
            let unique_env_elem = OrdEnvElem::UniqueMarker(UniqueString::new());

            let new_env = ast_args.iter().zip(arg_types.iter()).fold(
                env.add(unique_env_elem.clone()).clone(),
                |env_accum, (arg_ast, arg_type)| {
                    env_accum.add(OrdEnvElem::TVar(arg_ast.to_owned(), arg_type.to_owned()))
                },
            );

            check_expr(*ast_body, *res_type, new_env)?
                .split_on(&unique_env_elem)
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::OrdEnvElemNotFound(unique_env_elem))
        }
        (AST::List(elems), Type::Monotype(Monotype::List(typ))) => {
            elems.iter().fold(Ok(env), |res, elem| {
                check_expr(elem.to_owned(), Type::Monotype(*typ.clone()), res?)
            })
        }
        (AST::Ite(guard, branch1, branch2), typ) => {
            let env_guard = check_expr(*guard, Type::Monotype(Monotype::Bool), env)?;
            let env_branch1 = check_expr(*branch1, typ.clone(), env_guard)?;
            check_expr(*branch2, typ, env_branch1)
        }
        // Comparable to what we do for lambdas?
        // (AST::Let(var, assigned_expr, body_expr), _) => todo!(),
        // Sub
        (_, _) => {
            let InferOut {
                typ: expr_type,
                env: out_env,
            } = infer_expr(expr, env)?;

            subtype(
                out_env.substitute_fixpoint(expr_type),
                out_env.substitute_fixpoint(typ),
                out_env,
            )
        }
    }
}

fn apply_type(func_type: Type, args: Vec<AST>, env: OrdEnv) -> Result<InferOut, TypeError> {
    println!(
        "Apply\n========\ntype: {:#?}\nargs: {:#?}\nenv: {:#?}\n",
        func_type, args, env
    );
    match func_type {
        // ForallApp
        Type::Forall(UVar(str), quantified_type) => {
            let substituted_type =
                quantified_type.substitute(&UVar(str.to_string()), &EVar(str.to_string()));
            let new_env = env.add(OrdEnvElem::EVar(EVar(str.to_string())));

            apply_type(substituted_type, args, new_env)
        }
        // We _need_ an a-normal form transform
        // \hat{alpha}App
        Type::Monotype(Monotype::EVar(evar)) => {
            let (before_env, _, after_env) = env
                .split_on(&OrdEnvElem::EVar(evar.clone()))
                .ok_or(TypeError::EVarNotFound(evar.clone()))?;

            let args_and_evars: Vec<(AST, EVar)> =
                args.iter().fold(Vec::new(), |args_and_evars, arg| {
                    args_and_evars.push_immutable(&(arg.to_owned(), EVar::new_unique()))
                });

            let res_evar = EVar::new_unique();

            let env_evars: Vec<OrdEnvElem> = args_and_evars
                .iter()
                .map(|(_, evar)| OrdEnvElem::EVar(evar.to_owned()))
                .collect::<Vec<OrdEnvElem>>()
                .push_immutable(&OrdEnvElem::EVar(res_evar.clone()));

            let monotype_evars: Vec<Monotype> = args_and_evars
                .iter()
                .map(|(_, evar)| Monotype::EVar(evar.to_owned()))
                .collect::<Vec<Monotype>>();

            let solution = OrdEnvElem::ESol(
                evar,
                Monotype::Func(monotype_evars, Box::new(Monotype::EVar(res_evar.clone()))),
            );

            let new_env = before_env
                .add_all(env_evars)
                .add(solution)
                .concat(&after_env);

            let out_env = args_and_evars
                .iter()
                .fold(Ok(new_env), |env_or_err, (arg, evar)| {
                    let in_env = env_or_err?;
                    check_expr(
                        arg.clone(),
                        Type::Monotype(Monotype::EVar(evar.to_owned())),
                        in_env,
                    )
                })?;

            Ok(InferOut {
                typ: Type::Monotype(Monotype::EVar(res_evar)),
                env: out_env,
            })
        }
        // ->App
        Type::Func(type_args, res) => type_args
            .iter()
            .zip(args.iter())
            .fold(
                Ok(env),
                |in_env_or_err: Result<OrdEnv, TypeError>, (arg_type, arg)| {
                    let in_env = in_env_or_err?;
                    let check_out = check_expr(arg.clone(), arg_type.clone(), in_env.clone())?;

                    Ok(in_env.concat(&check_out))
                },
            )
            .map(|env| InferOut { typ: *res, env }),
        // TODO: need this case and the previous?
        Type::Monotype(Monotype::Func(type_args, res)) => {
            let type_args: Vec<Type> = type_args
                .iter()
                .map(|arg| Type::Monotype(arg.to_owned()))
                .collect();

            let type_res = Box::new(Type::Monotype(*res));

            let type_func = Type::Func(type_args, type_res);

            apply_type(type_func, args, env)
        }
        _ => todo!(),
    }
}

fn make_binding_env(identifiers: Vec<Ident>, types: Vec<Type>) -> OrdEnv {
    identifiers
        .iter()
        .zip(types.iter())
        .fold(OrdEnv::new(), |env, (ident, ident_type)| {
            env.add(OrdEnvElem::TVar(ident.to_owned(), ident_type.to_owned()))
        })
}

fn peel_foralls(foralls: Type, env: OrdEnv) -> (Vec<Type>, Type, OrdEnv) {
    match foralls {
        Type::Forall(uvar, typ) => peel_foralls(*typ, env.add(OrdEnvElem::UVar(uvar))),
        Type::Func(arg_types, res_type) => (arg_types, *res_type, env),
        _ => panic!(
            "Incorrect type variant passed to peel_foralls: {:?}",
            foralls
        ),
    }
}

fn check_top(exprs: Vec<AST>, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match exprs.as_slice() {
        [AST::TypeDec(func, func_type), rest @ ..] => check_top(
            rest.to_vec(),
            env.add(OrdEnvElem::TVar(func.to_owned(), func_type.to_owned())),
        ),
        [AST::Func(name, args, body), rest @ ..] => {
            let func_type = env
                .type_for_tvar(name.to_owned())
                .ok_or(TypeError::TVarNotFound(name.to_owned()))?;

            match func_type {
                Type::Func(arg_types, res_type) => {
                    let args_env = env.concat(&make_binding_env(args.to_owned(), arg_types));

                    check_expr(*body.to_owned(), *res_type, args_env)?;

                    check_top(rest.to_vec(), env)
                }
                forall @ Type::Forall(..) => {
                    let (arg_types, res_type, env_with_uvars) = peel_foralls(forall, env.clone());

                    let args_env =
                        env_with_uvars.concat(&make_binding_env(args.to_owned(), arg_types));

                    check_expr(*body.to_owned(), res_type, args_env)?;

                    check_top(rest.to_vec(), env)
                }
                _ => todo!(),
            }
        }
        [expr] => infer_expr(expr.to_owned(), env.clone()).map(
            |InferOut {
                 typ: expr_type,
                 env: expr_env,
             }| {
                dbg!(expr_env.substitute_fixpoint(expr_type));
                expr_env
            },
        ),
        [] => todo!(),
        _ => todo!(),
    }
}

pub fn check(Toplevel(exprs): Toplevel) -> Result<OrdEnv, TypeError> {
    check_top(exprs, OrdEnv::new())
}

// todo: implement let binding by thinking about how a lambda would handle it!
//
// todo: make sure we only create evars that are unique?
//
// todo: implement a-normal form pass?
#[cfg(test)]
mod test {
    use super::*;
    use crate::expand::expand;
    use crate::parse::tokenize;

    #[test]
    fn prim_1() {
        let ast = AST::Lit(Lit::I64(7));

        let out = infer_expr(ast, OrdEnv::new());

        assert_eq!(
            out,
            Ok(InferOut {
                typ: Type::Monotype(Monotype::I64),
                env: OrdEnv::new()
            })
        )
    }

    #[test]
    fn prim_2() {
        let ast = AST::Lit(Lit::List(vec![Lit::I64(4), Lit::I64(5)]));

        let out = infer_expr(ast, OrdEnv::new());

        assert_eq!(
            out,
            Ok(InferOut {
                typ: Type::Monotype(Monotype::List(Box::new(Monotype::I64))),
                env: OrdEnv::new()
            })
        )
    }

    // TODO: weird error involving EVars when we attempt to infer the type of the polymorphic
    // identity function
    #[test]
    fn lambda_1() {
        let ast = AST::Lambda(
            vec![Ident("y".to_string())],
            Box::new(AST::Var(Ident("y".to_string()))),
        );

        let out = check_expr(
            ast,
            Type::Forall(
                UVar("a".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("a".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                )),
            ),
            OrdEnv::new(),
        );

        assert_eq!(out, Ok(OrdEnv::new()))
    }

    #[test]
    fn lambda_1_err() {
        let ast = AST::Lambda(
            vec![Ident("y".to_string())],
            Box::new(AST::Var(Ident("y".to_string()))),
        );

        let out = check_expr(
            ast,
            Type::Forall(
                UVar("a".to_string()),
                Box::new(Type::Forall(
                    UVar("b".to_string()),
                    Box::new(Type::Func(
                        vec![Type::Monotype(Monotype::UVar(UVar("a".to_string())))],
                        Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                    )),
                )),
            ),
            OrdEnv::new(),
        );

        assert_eq!(
            out,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                Given(Type::Monotype(Monotype::UVar(UVar("b".to_string()))))
            ))
        )
    }

    #[test]
    fn lambda_2() {
        let ast = AST::Lambda(
            vec![Ident("y".to_string()), Ident("x".to_string())],
            Box::new(AST::Var(Ident("y".to_string()))),
        );

        let out = check_expr(
            ast,
            Type::Forall(
                UVar("a".to_string()),
                Box::new(Type::Forall(
                    UVar("b".to_string()),
                    Box::new(Type::Func(
                        vec![
                            Type::Monotype(Monotype::UVar(UVar("a".to_string()))),
                            Type::Monotype(Monotype::UVar(UVar("b".to_string()))),
                        ],
                        Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                    )),
                )),
            ),
            OrdEnv::new(),
        );

        assert_eq!(out, Ok(OrdEnv::new()))
    }

    #[test]
    fn lambda_2_err() {
        let ast = AST::Lambda(
            vec![Ident("y".to_string()), Ident("x".to_string())],
            Box::new(AST::Var(Ident("y".to_string()))),
        );

        let out = check_expr(
            ast,
            Type::Forall(
                UVar("a".to_string()),
                Box::new(Type::Forall(
                    UVar("b".to_string()),
                    Box::new(Type::Func(
                        vec![
                            Type::Monotype(Monotype::UVar(UVar("a".to_string()))),
                            Type::Monotype(Monotype::UVar(UVar("b".to_string()))),
                        ],
                        Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                    )),
                )),
            ),
            OrdEnv::new(),
        );

        assert_eq!(
            out,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                Given(Type::Monotype(Monotype::UVar(UVar("b".to_string()))))
            ))
        )
    }

    #[test]
    fn lambda_3() {
        let ast = AST::Lambda(
            vec![Ident("x".to_string()), Ident("y".to_string())],
            Box::new(AST::Var(Ident("y".to_string()))),
        );

        let out = check_expr(
            ast,
            Type::Forall(
                UVar("a".to_string()),
                Box::new(Type::Forall(
                    UVar("b".to_string()),
                    Box::new(Type::Func(
                        vec![
                            Type::Monotype(Monotype::UVar(UVar("a".to_string()))),
                            Type::Monotype(Monotype::UVar(UVar("b".to_string()))),
                        ],
                        Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                    )),
                )),
            ),
            OrdEnv::new(),
        );

        assert_eq!(out, Ok(OrdEnv::new()))
    }

    // we maybe need to be more clever about env.substitute, which should follow the
    // correct path through ESols

    #[test]
    fn app_infer_1() {
        let ast_lambda = AST::Lambda(
            vec![Ident("x".to_string())],
            Box::new(AST::Var(Ident("x".to_string()))),
        );

        let ast_app = AST::App(Box::new(ast_lambda), vec![AST::Lit(Lit::I64(5))]);

        let InferOut { typ, env } = infer_expr(ast_app, OrdEnv::new()).unwrap();

        // maybe we need to substitute more in general?
        assert_eq!(env.substitute_fixpoint(typ), Type::Monotype(Monotype::I64))
    }

    #[test]
    fn list_check_1() {
        let ast_list = AST::List(vec![AST::Lit(Lit::I64(1))]);

        let res = check_expr(
            ast_list,
            Type::Monotype(Monotype::List(Box::new(Monotype::I64))),
            OrdEnv::new(),
        );

        assert!(matches!(res, Ok(_)))
    }

    #[test]
    fn emptyp_infer_1() {
        let ast_list = AST::List(vec![AST::Lit(Lit::I64(1))]);

        let ast_emptyp = AST::Emptyp(Box::new(ast_list));

        let InferOut { typ, .. } = infer_expr(ast_emptyp, OrdEnv::new()).unwrap();

        assert_eq!(typ, Type::Monotype(Monotype::Bool));
    }

    #[test]
    fn cons_infer_1() {
        let ast_list = AST::List(vec![AST::Lit(Lit::I64(1))]);

        let ast_cons = AST::Cons(Box::new(AST::Lit(Lit::I64(1))), Box::new(ast_list));

        let InferOut { typ, .. } = infer_expr(ast_cons, OrdEnv::new()).unwrap();

        assert_eq!(typ, Type::Monotype(Monotype::List(Box::new(Monotype::I64))));
    }

    #[test]
    fn car_infer_1() {
        let ast_list = AST::List(vec![AST::Lit(Lit::I64(1))]);

        let ast_car = AST::Car(Box::new(ast_list));

        let InferOut { typ, .. } = infer_expr(ast_car, OrdEnv::new()).unwrap();

        assert_eq!(typ, Type::Monotype(Monotype::I64));
    }

    #[test]
    fn cdr_infer_1() {
        let ast_list = AST::List(vec![AST::Lit(Lit::I64(1))]);

        let ast_car = AST::Cdr(Box::new(ast_list));

        let InferOut { typ, .. } = infer_expr(ast_car, OrdEnv::new()).unwrap();

        assert_eq!(typ, Type::Monotype(Monotype::List(Box::new(Monotype::I64))));
    }

    #[test]
    fn ite_infer_1() {
        let ast_ite = tokenize("(if (empty? (list)) 1 2)").unwrap().parse();

        let InferOut { typ, .. } = infer_expr(ast_ite, OrdEnv::new()).unwrap();

        assert_eq!(typ, Type::Monotype(Monotype::I64))
    }

    #[test]
    fn ite_infer_2() {
        let ast_ite = tokenize("(if (empty? (list)) 1 (quote hey))")
            .unwrap()
            .parse();

        let err = infer_expr(ast_ite, OrdEnv::new());

        assert_eq!(
            err,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::Symbol)),
                Given(Type::Monotype(Monotype::I64))
            ))
        )
    }

    #[test]
    fn func_check_mono() {
        let ast_func = expand(
            tokenize(
                r#"
            ((declare map (-> ((-> (I64) String) (List I64)) (List String)))
             (fn map (f input-list)
              (if (empty? input-list)
               (list)
               (cons (f (car input-list)) (map f (cdr input-list)))))
             (map (lambda (elem) "hey") (list 1 4 7 8)))
            "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let res = check_top(ast_func.0, OrdEnv::new());

        assert!(matches!(res, Ok(_)))
    }

    #[test]
    fn func_check_poly_1() {
        let ast_func = expand(
            tokenize(
                r#"
                ((declare map (forall a (forall b (-> ((-> (a) b) (List a)) (List b)))))
                 (fn map (f input-list)
                  (if (empty? input-list)
                   (list)
                   (cons (f (car input-list)) (map f (cdr input-list)))))
                 (map (lambda (elem) "hey") (list 1 4 7 8)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let res = check_top(ast_func.0, OrdEnv::new());

        assert!(matches!(res, Ok(_)))
    }

    #[test]
    fn func_check_poly_1_err_1() {
        let ast_func = expand(
            tokenize(
                r#"
                ((declare map (forall a (forall b (-> ((-> (a) b) (List a)) (List b)))))
                 (fn map (f input-list)
                  (if (empty? input-list)
                   (list)
                   (cons (car input-list) (map f (cdr input-list)))))
                 (map (lambda (elem) "hey") (list 1 4 7 8)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let err = check_top(ast_func.0, OrdEnv::new());

        assert_eq!(
            err,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                Given(Type::Monotype(Monotype::UVar(UVar("a".to_string()))))
            ))
        )
    }

    #[test]
    fn func_check_poly_1_err_2() {
        let ast_func = expand(
            tokenize(
                r#"
                ((declare map (forall a (forall b (-> ((-> (a) b) (List a)) (List a)))))
                 (fn map (f input-list)
                  (if (empty? input-list)
                   (list)
                   (cons (f (car input-list)) (map f (cdr input-list)))))
                 (map (lambda (elem) "hey") (list 1 4 7 8)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let err = check_top(ast_func.0, OrdEnv::new());

        assert_eq!(
            err,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                Given(Type::Monotype(Monotype::UVar(UVar("b".to_string()))))
            ))
        )
    }
}
