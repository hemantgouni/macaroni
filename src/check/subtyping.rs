use crate::check::ordered_env::OrdEnv;
use crate::check::{Monotype, Type, TypeError};

// see 'figure 9: algorithmic subtyping' for rules

fn subtype(left: Type, right: Type, env: OrdEnv) -> Result<OrdEnv, TypeError> {
    match (left, right) {
        (Type::Monotype(Monotype::UVar(uvar1)), Type::Monotype(Monotype::UVar(uvar2)))
            if uvar1 == uvar2 =>
        {
            todo!()
        }
        (Type::Monotype(Monotype::UVar(uvar1)), Type::Monotype(Monotype::UVar(uvar2))) => todo!(),
        (Type::Monotype(Monotype::EVar(evar1)), Type::Monotype(Monotype::EVar(evar2)))
            if evar1 == evar2 =>
        {
            todo!()
        }
        (Type::Monotype(Monotype::EVar(evar1)), Type::Monotype(Monotype::EVar(evar2))) => todo!(),
        (Type::Monotype(monotype1), Type::Monotype(monotype2)) if monotype1 == monotype2 => todo!(),
        _ => todo!(),
    }
}
