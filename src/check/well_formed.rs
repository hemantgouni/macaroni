#![allow(dead_code)]
#![allow(unused_variables)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::{Monotype, Type, TypeError};

pub fn well_formed(typ: Type, env: OrdEnv) -> Result<(), TypeError> {
    match typ {
        Type::Monotype(typ) => match typ {
            // UvarWF
            Monotype::UVar(uvar) => {
                if env.contains(&OrdEnvElem::UVar(uvar.clone())) {
                    Ok(())
                } else {
                    Err(TypeError::UVarNotFound(uvar))
                }
            }
            // EvarWF, SolvedEvarWF
            Monotype::EVar(evar) => {
                if env.contains_pred(|elem| {
                    elem == &OrdEnvElem::EVar(evar.clone())
                        || matches!(elem, OrdEnvElem::ESol(evar, _))
                }) {
                    Ok(())
                } else {
                    Err(TypeError::EVarNotFound(evar))
                }
            }
            Monotype::Func(mut arg_types, res_type) => {
                arg_types.push(*res_type);

                arg_types.iter().fold(Ok(()), |prev_res, typ| {
                    match (
                        prev_res,
                        well_formed(Type::Monotype(typ.to_owned()), env.to_owned()),
                    ) {
                        (Ok(()), res) => res,
                        (Err(type_err), _) => Err(type_err),
                    }
                })
            }
            Monotype::List(typ) => well_formed(Type::Monotype(*typ), env),
            Monotype::Bottom
            | Monotype::I64
            | Monotype::Bool
            | Monotype::String
            | Monotype::Symbol => Ok(()),
        },
        // ArrowWF
        Type::Func(mut arg_types, res_type) => {
            arg_types.push(*res_type);

            arg_types.iter().fold(Ok(()), |prev_res, typ| {
                match (prev_res, well_formed(typ.to_owned(), env.to_owned())) {
                    (Ok(()), res) => res,
                    (Err(type_err), _) => Err(type_err),
                }
            })
        }
        // Recurse into the argument type to check well-formedness
        Type::List(typ) => well_formed(*typ, env),
        // ForallWF
        Type::Forall(uvar, typ) => well_formed(*typ, env.add(OrdEnvElem::UVar(uvar))),
    }
}

#[cfg(test)]
mod test {
    // TODO: actually write tests, after we've done some basic integration into instantiate
}
