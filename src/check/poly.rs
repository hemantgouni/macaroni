#![allow(dead_code)]

use crate::check::ordered_env::OrdEnv;
use crate::check::{Type, TypeError};
use crate::data::AST;

struct InferOut {
    typ: Type,
    env: OrdEnv,
}

fn infer_expr(expr: AST, env: OrdEnv) -> Result<InferOut, TypeError> {
    match expr {
        _ => todo!(),
    }
}

fn check_expr(expr: AST, typ: Type, env: OrdEnv) -> Result<(), Type> {
    match expr {
        _ => todo!(),
    }
}
