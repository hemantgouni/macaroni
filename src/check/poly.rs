#![allow(dead_code)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::subtyping::subtype;
use crate::check::well_formed::well_formed;
use crate::check::{Expected, Given, Lit, Monotype, Type, TypeError};
use crate::data::AST;

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
        _ => todo!(),
    }
}

fn check_expr(expr: AST, typ: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match (expr.clone(), typ.clone()) {
        // ForallI
        (_, Type::Forall(uvar, typ)) => {
            let env_appended = env.add(OrdEnvElem::UVar(uvar.clone()));

            check_expr(expr, *typ, env_appended.clone())?
                .split_on(&OrdEnvElem::UVar(uvar.clone()))
                .map(|tuple| tuple.0)
                .ok_or(TypeError::UVarNotFound(uvar))
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
