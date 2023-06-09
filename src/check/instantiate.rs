#![allow(unused_variables)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Monotype, Type, TypeError};

use crate::utils::get_unique_id;

fn instantiate_left(left: EVar, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match right {
        // InstLSolve
        Type::Monotype(typ) => match env.split_on(&OrdEnvElem::EVar(left.clone())) {
            Some((left_env, elem, right_env)) => {
                well_formed(Type::Monotype(typ.clone()), left_env.clone())
                    .map(|_| {
                        left_env
                            .add(OrdEnvElem::ESol(left.clone(), typ.clone()))
                            .concat(&right_env)
                    })
                    // InstLReach
                    .or_else(|typ_err| match typ {
                        Monotype::EVar(evar)
                            if right_env.contains(&OrdEnvElem::EVar(evar.to_owned())) =>
                        {
                            left_env
                                .add(elem)
                                .concat(&right_env)
                                .update(
                                    &OrdEnvElem::EVar(evar.to_owned()),
                                    OrdEnvElem::ESol(evar.to_owned(), Monotype::EVar(left)),
                                )
                                .ok_or(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(
                                    evar.to_owned(),
                                )))
                        }
                        _ => Err(typ_err),
                    })
            }
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(
                left.clone(),
            ))),
        },
        // InstLArr
        // Have to create a ton of existentials here
        Type::Func(mut arg_types, res_type) => {
            match env.split_on(&OrdEnvElem::EVar(left.clone())) {
                Some((left_env, elem, right_env)) => {
                    // arg_types.
                    todo!()
                }
                None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(
                    left.clone(),
                ))),
            }
        }
        // InstLAllR
        Type::Forall(uvar, typ) => todo!(),
        // InstLList?
        _ => todo!(),
    }
}

#[allow(non_snake_case)]
#[cfg(test)]
mod test {
    use super::*;
    use crate::check::UVar;

    #[test]
    fn test_InstLSolve() {
        let input_env = OrdEnv(vec![OrdEnvElem::EVar(EVar("alpha".to_string()))]);

        let result = instantiate_left(
            EVar("alpha".to_string()),
            Type::Monotype(Monotype::I64),
            input_env,
        );

        assert_eq!(
            result,
            Ok(OrdEnv(vec![OrdEnvElem::ESol(
                EVar("alpha".to_string()),
                Monotype::I64
            )]))
        );
    }

    #[test]
    fn test_InstLSolve_err_wronginputenv() {
        let input_env = OrdEnv(vec![OrdEnvElem::EVar(EVar("beta".to_string()))]);

        let result = instantiate_left(
            EVar("alpha".to_string()),
            Type::Monotype(Monotype::I64),
            input_env,
        );

        assert_eq!(
            result,
            Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(EVar(
                "alpha".to_string()
            ))))
        );
    }

    #[test]
    fn test_InstLSolve_err_notwellformed() {
        let input_env = OrdEnv(vec![
            OrdEnvElem::EVar(EVar("alpha".to_string())),
            OrdEnvElem::UVar(UVar("beta".to_string())),
        ]);

        let result = instantiate_left(
            EVar("alpha".to_string()),
            Type::Monotype(Monotype::UVar(UVar("beta".to_string()))),
            input_env,
        );

        assert_eq!(
            result,
            Err(TypeError::UVarNotFound(UVar("beta".to_string())))
        );
    }

    #[test]
    fn test_InstLReach() {
        let input_env = OrdEnv(vec![
            OrdEnvElem::EVar(EVar("alpha".to_string())),
            OrdEnvElem::EVar(EVar("beta".to_string())),
        ]);

        let result = instantiate_left(
            EVar("alpha".to_string()),
            Type::Monotype(Monotype::EVar(EVar("beta".to_string()))),
            input_env.clone(),
        );

        assert_eq!(
            result,
            Ok(OrdEnv(vec![
                OrdEnvElem::EVar(EVar("alpha".to_string())),
                OrdEnvElem::ESol(
                    EVar("beta".to_string()),
                    Monotype::EVar(EVar("alpha".to_string()))
                )
            ]))
        );
    }
}
