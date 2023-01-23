use crate::data::{Env, Lit, AST};
use crate::utils::{get_unique_id, vec_all_eq};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Type {
    Var(String),
    I64,
    Bool,
    String,
    Symbol,
    List(Box<Type>),
    Func(Box<Type>, Box<Type>),
}

fn check_or_err(result: Type, target: Type) -> Result<(), String> {
    if target == result {
        Ok(())
    } else {
        Err(format!("Expected {:?}, given {:?}", target, result))
    }
}

fn check_expr(expr: AST, current: Option<Type>, environment: Env) -> Result<(), String> {
    let current_type;

    match current {
        Some(current) => current_type = current,
        None => current_type = infer_expr(expr.clone(), environment.clone())?,
    }

    match expr {
        AST::Lit(lit) => match lit {
            Lit::I64(_) => check_or_err(Type::I64, current_type),
            Lit::Bool(_) => check_or_err(Type::Bool, current_type),
            Lit::String(_) => check_or_err(Type::String, current_type),
            Lit::Symbol(_) => check_or_err(Type::Symbol, current_type),
            Lit::List(lits) => {
                match vec_all_eq(
                    lits.iter()
                        .map(|lit| infer_expr(AST::Lit(lit.clone()), environment.clone()).unwrap())
                        .collect(),
                ) {
                    (true, Some(typ)) => check_or_err(Type::List(Box::new(typ)), current_type),
                    (false, _) => Err(format!("Heterogeneous lists are not supported!")),
                    // check_or_err needs to do unification, right?
                    //
                    // but List a should not unify with List b, necessarily, so this way of doing
                    // it might be an issue
                    (true, None) => check_or_err(
                        // make sure type variables that start with numbers are syntactically
                        // prohibited
                        //
                        // orr maybe we should have a special namespace for compiler generated type
                        // variables!
                        Type::List(Box::new(Type::Var(get_unique_id()))),
                        current_type,
                    ),
                }
            }
        },
        other => Err(format!("Type checking not yet implemented for {:?}", other)),
    }
}

fn infer_expr(expr: AST, environment: Env) -> Result<Type, String> {
    match expr {
        AST::Lit(lit) => match lit {
            Lit::I64(_) => Ok(Type::I64),
            Lit::Bool(_) => Ok(Type::Bool),
            Lit::String(_) => Ok(Type::String),
            Lit::Symbol(_) => Ok(Type::Symbol),
            Lit::List(lits) => Ok(Type::List(Box::new(infer_expr(
                AST::Lit(lits.first().unwrap().clone()),
                environment,
            )?))),
        },
        AST::Add(expr1, expr2) => {
            match (
                check_expr(*expr1, Some(Type::I64), environment.clone())?,
                check_expr(*expr2, Some(Type::I64), environment.clone())?,
            ) {
                ((), ()) => Ok(Type::I64),
            }
        }
        other => Err(format!(
            "Type inference not yet implemented for {:?}",
            other
        )),
    }
}
