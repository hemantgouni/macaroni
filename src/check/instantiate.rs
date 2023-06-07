#![allow(dead_code)]
#![allow(unused_variables)]

use crate::check::ordered_env::{OrderedEnv, OrderedEnvElem};
use crate::check::{EVar, Monotype, Type};

pub enum InstErr {}

fn instantiate_left(left: EVar, right: Type, env: OrderedEnv) -> Result<OrderedEnv, InstErr> {
    match right {
        // InstLReach
        Type::Monotype(Monotype::EVar(evar)) => todo!(),
        // InstLSolve
        Type::Monotype(typ) => match env.split_on(&OrderedEnvElem::EVar(left)) {
            Some((left, elem, right)) => todo!(),
            _ => todo!(),
        },
        // InstLArr
        Type::Func(arg_types, res_type) => todo!(),
        // InstLAllR
        Type::Forall(typ) => todo!(),
        _ => todo!(),
    }
}
