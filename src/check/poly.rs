#![allow(dead_code)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::subtyping::subtype;
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Expected, Given, Ident, Lit, Monotype, Type, TypeError, UVar};
use crate::data::AST;
use crate::utils::{UniqueString, VecUtils};

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

            apply_type(lambda_out_env.substitute(lambda_type), args, lambda_out_env)
        }
        _ => todo!(),
    }
}

fn check_expr(expr: AST, typ: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
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
        // Sub
        (_, _) => {
            let InferOut {
                typ: expr_type,
                env: out_env,
            } = infer_expr(expr, env)?;

            subtype(
                out_env.substitute(expr_type),
                out_env.substitute(typ),
                out_env,
            )
        }
    }
}

fn apply_type(func_type: Type, args: Vec<AST>, env: OrdEnv) -> Result<InferOut, TypeError> {
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
        _ => todo!(),
    }
}
