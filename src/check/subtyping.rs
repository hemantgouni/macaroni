use crate::check::instantiate::{instantiate_left, instantiate_right};
use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::{EVar, Expected, Given, Monotype, Type, TypeError, UVar};
use crate::utils::UniqueString;

// see 'figure 9: algorithmic subtyping' for rules

pub fn subtype(left: Type, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match (left, right) {
        // <: Var
        (Type::Monotype(Monotype::UVar(uvar1)), Type::Monotype(Monotype::UVar(uvar2)))
            if uvar1 == uvar2 =>
        {
            if env.contains(&OrdEnvElem::UVar(uvar1.clone())) {
                Ok(env)
            } else {
                Err(TypeError::UVarNotFound(uvar1))
            }
        }
        (Type::Monotype(Monotype::UVar(uvar1)), Type::Monotype(Monotype::UVar(uvar2))) => {
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(uvar1))),
                Given(Type::Monotype(Monotype::UVar(uvar2))),
            ))
        }
        // <: Exvar
        (Type::Monotype(Monotype::EVar(evar1)), Type::Monotype(Monotype::EVar(evar2)))
            if evar1 == evar2 =>
        {
            if env.contains(&OrdEnvElem::EVar(evar1.clone())) {
                Ok(env)
            } else {
                Err(TypeError::EVarNotFound(evar1))
            }
        }
        (Type::Monotype(Monotype::EVar(evar1)), Type::Monotype(Monotype::EVar(evar2))) => {
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::EVar(evar1))),
                Given(Type::Monotype(Monotype::EVar(evar2))),
            ))
        }
        // <: ->
        (Type::Func(args1, res1), Type::Func(args2, res2)) => {
            let arg_out_env: OrdEnv =
                args1
                    .iter()
                    .zip(args2.iter())
                    .fold(Ok(env), |env, (arg1, arg2)| {
                        let env = env?;
                        subtype(
                            env.substitute(arg2.to_owned()),
                            env.substitute(arg1.to_owned()),
                            env,
                        )
                    })?;

            let res_out_env: OrdEnv = subtype(
                arg_out_env.substitute(*res1),
                arg_out_env.substitute(*res2),
                arg_out_env,
            )?;

            Ok(res_out_env)
        }
        // <: ForallR
        (type_left, Type::Forall(uvar, type_quantified)) => {
            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            let env_new = env
                .add(unique_marker.clone())
                .add(OrdEnvElem::UVar(uvar.clone()));

            subtype(type_left, *type_quantified, env_new)?
                .split_on(&unique_marker)
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::UVarNotFound(uvar))
        }
        // <: ForallL
        (Type::Forall(UVar(str), type_quantified), type_right) => {
            let unique_marker = OrdEnvElem::UniqueMarker(UniqueString::new());

            let env = env
                .add(unique_marker.clone())
                .add(OrdEnvElem::EVar(EVar(str.clone())));

            let type_substituted =
                type_quantified.substitute(&UVar(str.clone()), &EVar(str.clone()));

            subtype(type_substituted, type_right, env)?
                .split_on(&unique_marker)
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::OrdEnvElemNotFound(unique_marker))
        }
        // <: InstantiateL
        (Type::Monotype(Monotype::EVar(evar)), type_right) => {
            if env.contains(&OrdEnvElem::EVar(evar.clone())) {
                if type_right.free_evars().contains(&evar) {
                    Err(TypeError::Occurs(evar, type_right))
                } else {
                    instantiate_left(evar, type_right, env)
                }
            } else {
                Err(TypeError::EVarNotFound(evar))
            }
        }
        // <: InstantiateR
        (type_left, Type::Monotype(Monotype::EVar(evar))) => {
            if env.contains(&OrdEnvElem::EVar(evar.clone())) {
                // occurs check
                if type_left.free_evars().contains(&evar) {
                    Err(TypeError::Occurs(evar, type_left))
                } else {
                    instantiate_right(type_left, evar, env)
                }
            } else {
                Err(TypeError::EVarNotFound(evar))
            }
        }
        // <: Unit
        (Type::Monotype(monotype1), Type::Monotype(monotype2)) if monotype1 == monotype2 => Ok(env),
        (Type::Monotype(monotype1), Type::Monotype(monotype2)) => Err(TypeError::SubtypeMismatch(
            Expected(Type::Monotype(monotype1)),
            Given(Type::Monotype(monotype2)),
        )),
        (type_left, type_right) => Err(TypeError::Message(format!(
            "Subtyping attempted on invalid arguments: {:?}, {:?}",
            type_left, type_right
        ))),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn subtype_basic_1() {
        let type_left = Type::Monotype(Monotype::I64);
        let type_right = Type::Monotype(Monotype::I64);

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_basic_2() {
        let type_left = Type::Monotype(Monotype::Bool);
        let type_right = Type::Monotype(Monotype::I64);

        let res = subtype(type_left.clone(), type_right.clone(), OrdEnv::new());

        assert_eq!(
            res,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::Bool)),
                Given(Type::Monotype(Monotype::I64))
            ))
        )
    }

    #[test]
    fn subtype_bottom_1() {
        let type_left = Type::Monotype(Monotype::Bottom);
        let type_right = Type::Monotype(Monotype::Bottom);

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    // bottom is automatically handled correctly by subtyping via the equality defined on types
    #[test]
    fn subtype_bottom_2() {
        let type_left = Type::Monotype(Monotype::Bottom);
        let type_right = Type::Monotype(Monotype::I64);

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_1() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let type_right = Type::Monotype(Monotype::I64);

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_1_err() {
        let type_left = Type::Monotype(Monotype::I64);

        let type_right = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(
            res,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::UVar(UVar("a".to_string()))))
            ))
        )
    }

    #[test]
    fn subtype_poly_2() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let type_right = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_2_err_1() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let type_right = Type::Forall(
            UVar("c".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Err(TypeError::UVarNotFound(UVar("b".to_string()))))
    }

    #[test]
    fn subtype_poly_2_err_2() {
        let type_left = Type::Forall(
            UVar("z".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let type_right = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(
            res,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                Given(Type::Monotype(Monotype::UVar(UVar("b".to_string()))))
            ))
        )
    }

    #[test]
    fn subtype_poly_func_1() {
        let type_left = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
            )),
        );

        let type_right = Type::Func(
            vec![Type::Monotype(Monotype::I64)],
            Box::new(Type::Monotype(Monotype::I64)),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_func_1_err() {
        let type_left = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
            )),
        );

        let type_right = Type::Func(
            vec![Type::Monotype(Monotype::I64)],
            Box::new(Type::Monotype(Monotype::Bool)),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(
            res,
            Err(TypeError::SubtypeMismatch(
                Expected(Type::Monotype(Monotype::I64)),
                Given(Type::Monotype(Monotype::Bool))
            ))
        )
    }

    #[test]
    fn subtype_poly_func_2() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("a".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
            )),
        );

        let type_right = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
            )),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_func_3() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Forall(
                UVar("b".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                )),
            )),
        );

        let type_right = Type::Func(
            vec![Type::Monotype(Monotype::I64)],
            Box::new(Type::Monotype(Monotype::Bool)),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    #[test]
    fn subtype_poly_func_4() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let type_right = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
            )),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()))
    }

    // TODO: better error message here?
    #[test]
    fn subtype_poly_func_4_err() {
        let type_left = Type::Forall(
            UVar("b".to_string()),
            Box::new(Type::Func(
                vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
            )),
        );

        let type_right = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert!(matches!(res, Err(_)))
    }

    #[test]
    fn subtype_poly_func_5() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Forall(
                UVar("b".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("a".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                )),
            )),
        );

        let type_right = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Forall(
                UVar("b".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("b".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("a".to_string())))),
                )),
            )),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()));
    }

    #[test]
    fn subtype_poly_func_6() {
        let type_left = Type::Forall(
            UVar("a".to_string()),
            Box::new(Type::Forall(
                UVar("b".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("a".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("b".to_string())))),
                )),
            )),
        );

        let type_right = Type::Forall(
            UVar("c".to_string()),
            Box::new(Type::Forall(
                UVar("d".to_string()),
                Box::new(Type::Func(
                    vec![Type::Monotype(Monotype::UVar(UVar("c".to_string())))],
                    Box::new(Type::Monotype(Monotype::UVar(UVar("d".to_string())))),
                )),
            )),
        );

        let res = subtype(type_left, type_right, OrdEnv::new());

        assert_eq!(res, Ok(OrdEnv::new()));
    }
}
