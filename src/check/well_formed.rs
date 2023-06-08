#![allow(dead_code)]
#![allow(unused_variables)]

use crate::check::ordered_env::{OrderedEnv, OrderedEnvElem};
use crate::check::{Monotype, Type, TypeError};

pub fn well_formed(typ: Type, env: OrderedEnv) -> Result<(), TypeError> {
    match typ {
        Type::Monotype(typ) => match typ {
            // UvarWF
            Monotype::UVar(uvar) => {
                if env.contains(&OrderedEnvElem::UVar(uvar.clone())) {
                    Ok(())
                } else {
                    Err(TypeError::UVarLookupFailure(uvar))
                }
            }
            // EvarWF, SolvedEvarWF
            Monotype::EVar(evar) => {
                if env.contains_pred(|elem| {
                    elem == &OrderedEnvElem::EVar(evar.clone())
                        || matches!(elem, OrderedEnvElem::ESol(evar, _))
                }) {
                    Ok(())
                } else {
                    Err(TypeError::EVarLookupFailure(evar))
                }
            }
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
        Type::Forall(uvar, typ) => well_formed(*typ, env.add(OrderedEnvElem::UVar(uvar))),
    }
}
