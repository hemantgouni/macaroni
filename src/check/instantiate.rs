#![allow(dead_code)]
#![allow(unused_variables)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Monotype, Type, TypeError};

fn instantiate_left(left: EVar, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match right {
        // InstLReach
        Type::Monotype(Monotype::EVar(evar)) => todo!(),
        // InstLSolve
        Type::Monotype(typ) => match env.split_on(&OrdEnvElem::EVar(left.clone())) {
            Some((left_env, elem, right_env)) => {
                well_formed(Type::Monotype(typ.clone()), left_env.clone()).map(|_| {
                    left_env
                        .add(OrdEnvElem::ESol(left, typ))
                        .concat(&right_env)
                })
            }
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(
                left.clone(),
            ))),
        },
        // InstLArr
        Type::Func(arg_types, res_type) => todo!(),
        // InstLAllR
        Type::Forall(uvar, typ) => todo!(),
        _ => todo!(),
    }
}
