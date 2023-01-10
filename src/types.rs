use crate::data::{Env, Lit, AST};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Type {
    Int,
    Bool,
    String,
    Symbol,
    List(Box<Type>),
    Func(Box<Type>, Box<Type>),
}

fn check_expr(expr: AST, environment: Env, current: Type) -> Result<bool, String> {
    match expr {
        AST::Lit(lit) => match lit {
            Lit::I64(_) => Ok(current == Type::Int),
            Lit::Bool(_) => Ok(current == Type::Bool),
            Lit::String(_) => Ok(current == Type::String),
            Lit::Symbol(_) => Ok(current == Type::Symbol),
            // Lit::List(lits) => {
            //     lits.iter().map(|lit| check_expr)
            // }
            _ => panic!(),
        },
        other => Err(format!("Type checking not yet implemented for {:?}", other)),
    }
}

fn infer_expr(expr: AST, environment: Env) -> Result<Type, String> {
    match expr {
        AST::Lit(lit) => match lit {
            Lit::I64(_) => Ok(Type::Int),
            Lit::Bool(_) => Ok(Type::Bool),
            Lit::String(_) => Ok(Type::String),
            Lit::Symbol(_) => Ok(Type::Symbol),
            Lit::List(lits) => Ok(Type::List(Box::new(infer_expr(
                AST::Lit(lits.first().unwrap().clone()),
                environment,
            )?))),
        },
        other => Err(format!("Type checking not yet implemented for {:?}", other)),
    }
}
