use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Monotype, Type, TypeError, UVar};

use crate::utils::get_unique_id;

pub fn instantiate_left(left: EVar, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
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
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(left))),
        },
        // InstLArr
        // Have to create a ton of existentials here
        Type::Func(arg_types, res_type) => match env.split_on(&OrdEnvElem::EVar(left.clone())) {
            Some((left_env, _, right_env)) => {
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

                let new_env_init = left_env
                    .concat(
                        &OrdEnv(
                            arg_pairs
                                .iter()
                                .map(|pair| OrdEnvElem::EVar(pair.1.clone()))
                                .collect(),
                        )
                        .add(OrdEnvElem::EVar(res_pair.1.clone()))
                        .add(func_esol),
                    )
                    .concat(&right_env);

                arg_pairs
                    .iter()
                    .fold(
                        Ok(new_env_init),
                        |env_or_err: Result<OrdEnv, TypeError>, pair| {
                            let in_env = env_or_err?;
                            instantiate_right(
                                in_env.substitute(pair.0.to_owned()),
                                pair.1.to_owned(),
                                in_env,
                            )
                        },
                    )
                    .and_then(|in_env| {
                        instantiate_left(
                            res_pair.1,
                            in_env.substitute(res_pair.0.to_owned()),
                            in_env,
                        )
                    })
            }
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(left))),
        },
        // InstLAllR
        Type::Forall(uvar, typ) => {
            if env.contains(&OrdEnvElem::EVar(left.clone())) {
                instantiate_left(left.clone(), *typ, env.add(OrdEnvElem::UVar(uvar.clone()))).map(
                    |out_env| match out_env.split_on(&OrdEnvElem::UVar(uvar)) {
                        Some((left_env, _, _)) => left_env,
                        None => panic!("The variable we inserted wasn't found. This is a bug!."),
                    },
                )
            } else {
                Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(left)))
            }
        }
    }
}

pub fn instantiate_right(left: Type, right: EVar, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match left {
        // InstRSolve, InstRReach
        Type::Monotype(_) => instantiate_left(right, left, env),
        // InstRArr
        Type::Func(arg_types, res_type) => match env.split_on(&OrdEnvElem::EVar(right.clone())) {
            Some((left_env, _, right_env)) => {
                let arg_pairs: Vec<(&Type, EVar)> = arg_types
                    .iter()
                    .map(|arg_type| (arg_type, EVar(get_unique_id())))
                    .collect();

                let res_pair: (&Type, EVar) = (&*res_type, EVar(get_unique_id()));

                let func_esol = OrdEnvElem::ESol(
                    right,
                    Monotype::Func(
                        arg_pairs
                            .iter()
                            .map(|pair| Monotype::EVar(pair.1.clone()))
                            .collect(),
                        Box::new(Monotype::EVar(res_pair.1.to_owned())),
                    ),
                );

                let new_env_init = left_env
                    .concat(
                        &OrdEnv(
                            arg_pairs
                                .iter()
                                .map(|pair| OrdEnvElem::EVar(pair.1.clone()))
                                .collect(),
                        )
                        .add(OrdEnvElem::EVar(res_pair.1.clone()))
                        .add(func_esol),
                    )
                    .concat(&right_env);

                dbg!(new_env_init.clone());

                arg_pairs
                    .iter()
                    .fold(
                        Ok(new_env_init),
                        |env_or_err: Result<OrdEnv, TypeError>, pair| {
                            let in_env = env_or_err?;
                            instantiate_left(
                                pair.1.to_owned(),
                                in_env.substitute(pair.0.to_owned()),
                                in_env,
                            )
                        },
                    )
                    .and_then(|in_env| {
                        instantiate_right(
                            in_env.substitute(res_pair.0.to_owned()),
                            res_pair.1,
                            in_env,
                        )
                    })
            }
            None => Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(right))),
        },
        // InstRAllL
        Type::Forall(UVar(name), typ) => {
            if env.contains(&OrdEnvElem::EVar(right.clone())) {
                let new_env_init = env
                    .add(OrdEnvElem::Marker(EVar(name.clone())))
                    .add(OrdEnvElem::EVar(EVar(name.clone())));

                dbg!(new_env_init.clone());

                instantiate_right(
                    dbg!(typ.substitute(&UVar(name.clone()), &EVar(name.clone()))),
                    dbg!(right),
                    new_env_init,
                )?
                .split_on(&OrdEnvElem::Marker(EVar(name.clone())))
                .map(|split| split.0)
                .ok_or(TypeError::OrdEnvElemNotFound(OrdEnvElem::Marker(EVar(
                    name,
                ))))
            } else {
                Err(TypeError::OrdEnvElemNotFound(OrdEnvElem::EVar(right)))
            }
        }
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

    #[test]
    fn test_InstRAllL_1() {
        let input_env = OrdEnv(vec![OrdEnvElem::EVar(EVar("beta".to_string()))]);

        let result = instantiate_right(
            Type::Forall(
                UVar("alpha".to_string()),
                Box::new(Type::Monotype(Monotype::UVar(UVar("alpha".to_string())))),
            ),
            EVar("beta".to_string()),
            input_env.clone(),
        );

        assert_eq!(result, Ok(input_env))
    }

    // instantiation example from figure 12
    #[test]
    fn test_InstRAllL_2() {
        let input_env = OrdEnv(vec![OrdEnvElem::EVar(EVar("alpha".to_string()))]);

        let result = instantiate_right(
            Type::Forall(
                UVar("beta".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("beta".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("beta".to_string())))),
                )),
            ),
            EVar("alpha".to_string()),
            input_env,
        );

        match result.unwrap().0.as_slice() {
            #[rustfmt::skip]
            [OrdEnvElem::EVar(evar1),
             OrdEnvElem::ESol(evar2, Monotype::EVar(evar3)),
             OrdEnvElem::ESol(evar_alpha, Monotype::Func(args, res))] =>
            {
                assert!(evar1 == evar3);
                match (args.as_slice(), *res.clone()) {
                    ([Monotype::EVar(evar4)], Monotype::EVar(evar5)) => {
                        assert!(evar1 == evar4);
                        assert!(evar2 == &evar5);
                        assert!(matches!(evar_alpha, EVar(name) if name == "alpha"));
                    }
                    _ => panic!("Function argument or result did not take the expected form!"),
                }
            }
            _ => panic!("Final output environment did not take the expected form!"),
        }
    }
}
