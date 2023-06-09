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
        Type::Func(arg_types, res_type) => match env.split_on(&OrdEnvElem::EVar(left.clone())) {
            Some((left_env, elem, right_env)) => {
                let arg_pairs: Vec<(&Type, EVar)> = arg_types
                    .iter()
                    .map(|arg_type| (arg_type, EVar(get_unique_id())))
                    .collect();

                let res_pair: (&Type, EVar) = (&*res_type, EVar(get_unique_id()));

                let func_esol = OrdEnvElem::ESol(
                    left,
                    Monotype::Func(
                        arg_pairs
                            .iter()
                            .map(|pair| Monotype::EVar(pair.1.clone()))
                            .collect(),
                        Box::new(Monotype::EVar(res_pair.1.to_owned())),
                    ),
                );

                let env_to_insert = OrdEnv(
                    arg_pairs
                        .iter()
                        .map(|pair| OrdEnvElem::EVar(pair.1.clone()))
                        .collect(),
                )
                .add(func_esol);

                let new_env_initial = left_env.concat(&env_to_insert).concat(&right_env);

                // remember to substitute using env! add this to OrdEnv
                arg_pairs
                    .iter()
                    .fold(
                        Ok(new_env_initial),
                        |env_or_err: Result<OrdEnv, TypeError>, pair| {
                            instantiate_right(pair.0.to_owned(), pair.1.to_owned(), env_or_err?)
                        },
                    )
                    .and_then(|out_env| {
                        instantiate_left(res_pair.1, res_pair.0.to_owned(), out_env)
                    })
            }
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(
                left.clone(),
            ))),
        },
        // InstLAllR
        Type::Forall(uvar, typ) => todo!(),
        // InstLList?
        Type::List(typ) => todo!(),
    }
}

fn instantiate_right(right: Type, left: EVar, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    todo!()
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
