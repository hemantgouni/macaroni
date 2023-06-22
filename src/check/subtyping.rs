use crate::check::instantiate::{instantiate_left, instantiate_right};
use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::{EVar, Monotype, Type, TypeError, UVar};

// see 'figure 9: algorithmic subtyping' for rules

fn subtype(left: Type, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
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
            Err(TypeError::Message(format!(
                "Subtyping attempted on uvars that are not comparable: {:?}, {:?}",
                uvar1, uvar2
            )))
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
            Err(TypeError::Message(format!(
                "Subtyping attempted on evars that are not comparable: {:?}, {:?}",
                evar1, evar2
            )))
        }
        // <: Unit
        (Type::Monotype(monotype1), Type::Monotype(monotype2)) if monotype1 == monotype2 => Ok(env),
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
        // <: forallL
        (Type::Forall(UVar(str), type_quantified), type_right) => {
            let env = env
                .add(OrdEnvElem::Marker(EVar(str.clone())))
                .add(OrdEnvElem::EVar(EVar(str.clone())));

            let type_substituted =
                type_quantified.substitute(&UVar(str.clone()), &EVar(str.clone()));

            subtype(type_substituted, type_right, env)?
                .split_on(&OrdEnvElem::Marker(EVar(str.clone())))
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::Message(format!(
                    "Unable to find our own marker in the environment: {:?}",
                    OrdEnvElem::Marker(EVar(str))
                )))
        }
        // <: forallR
        (type_left, Type::Forall(uvar, type_quantified)) => {
            let env_new = env.add(OrdEnvElem::UVar(uvar.clone()));

            subtype(type_left, *type_quantified, env_new)?
                .split_on(&OrdEnvElem::UVar(uvar.clone()))
                .map(|(before_env, _, _)| before_env)
                .ok_or(TypeError::UVarNotFound(uvar))
        }
        // <: InstantiateL
        (Type::Monotype(Monotype::EVar(evar)), type_right) => {
            if env.contains(&OrdEnvElem::EVar(evar.clone())) {
                if type_right.free_evars().contains(&evar) {
                    instantiate_left(evar, type_right, env)
                } else {
                    Err(TypeError::Occurs(evar, type_right))
                }
            } else {
                Err(TypeError::EVarNotFound(evar))
            }
        }
        // <: InstantiateR
        (type_left, Type::Monotype(Monotype::EVar(evar))) => {
            if env.contains(&OrdEnvElem::EVar(evar.clone())) {
                if type_left.free_evars().contains(&evar) {
                    instantiate_right(type_left, evar, env)
                } else {
                    Err(TypeError::Occurs(evar, type_left))
                }
            } else {
                Err(TypeError::EVarNotFound(evar))
            }
        }
        (type_left, type_right) => Err(TypeError::Message(format!(
            "Subtyping attempted on invalid arguments: {:#?}, {:#?}",
            type_left, type_right
        ))),
    }
}
