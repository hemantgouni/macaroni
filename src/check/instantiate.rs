#![allow(unused_imports)]
#![allow(unused_variables)]

use crate::check::ordered_env::{OrdEnv, OrdEnvElem};
use crate::check::well_formed::well_formed;
use crate::check::{EVar, Monotype, Type, TypeError, UVar};

fn instantiate_left(left: EVar, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match right {
        // InstLReach
        Type::Monotype(Monotype::EVar(evar)) => todo!(),
        // InstLSolve
        Type::Monotype(typ) => match env.split_on(&OrdEnvElem::EVar(left.clone())) {
            Some((left_env, elem, right_env)) => {
                well_formed(Type::Monotype(typ.clone()), left_env.clone())
                    .map(|_| left_env.add(OrdEnvElem::ESol(left, typ)).concat(&right_env))
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

#[allow(non_snake_case)]
#[cfg(test)]
mod test {
    use super::*;

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
}
