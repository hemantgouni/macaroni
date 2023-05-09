#![allow(dead_code)]

use crate::data::{Env, Lit, AST};
use crate::utils::VecUtils;

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

#[derive(Debug, PartialEq)]
struct TypeError {
    expected: Type,
    given: Type,
}

fn type_eq_or_err(given: Type, expected: Type) -> Result<(), TypeError> {
    if expected == given {
        Ok(())
    } else {
        Err(TypeError { expected, given })
    }
}

fn infer_lit(expr: Lit) -> Type {
    match expr {
        Lit::I64(_) => Type::I64,
        Lit::Bool(_) => Type::Bool,
        Lit::String(_) => Type::String,
        Lit::Symbol(_) => Type::Symbol,
        Lit::List(lits) => match lits.as_slice() {
            // need polymorphism to support this case
            [] => todo!(),
            [head, ..] => infer_lit(head.to_owned()),
        },
    }
}

fn infer_expr(expr: AST, environment: Env) -> Result<Type, TypeError> {
    match expr {
        AST::Type(ty, _) => Ok(ty),
        _ => todo!(),
    }
}

fn check_lit(expr: Lit) -> Result<(), TypeError> {
    match expr {
        Lit::List(lits) => {
            if lits.all_eq() {
                Ok(())
            } else {
                panic!()
            }
        }
        _ => todo!(),
    }
}

fn check_expr(expr: AST, environment: Env, expected: Type) -> Result<(), TypeError> {
    match expr {
        _ => infer_expr(expr, environment).map(|_| ()),
    }
}

// fn check_or_err(result: Type, target: Type) -> Result<(), TypeError> {
//     if target == result {
//         Ok(())
//     } else {
//         Err(TypeError {
//             expected: target,
//             given: result,
//         })
//     }
// }

//fn check_expr(expr: AST, current: Option<Type>, environment: Env) -> Result<(), TypeError> {
//    let current_type = match current {
//        Some(current) => current,
//        None => infer_expr(expr.clone(), environment.clone())?,
//    };

//    match expr {
//        AST::Lit(lit) => match lit {
//            Lit::I64(_) => check_or_err(Type::I64, current_type),
//            Lit::Bool(_) => check_or_err(Type::Bool, current_type),
//            Lit::String(_) => check_or_err(Type::String, current_type),
//            Lit::Symbol(_) => check_or_err(Type::Symbol, current_type),
//            Lit::List(lits) => {
//                match vec_all_eq(
//                    lits.iter()
//                        .map(|lit| infer_expr(AST::Lit(lit.clone()), environment.clone()).unwrap())
//                        .collect(),
//                ) {
//                    (true, Some(typ)) => check_or_err(Type::List(Box::new(typ)), current_type),
//                    (false, _) => panic!("Heterogeneous lists are not supported!"),
//                    // check_or_err needs to do unification, right?
//                    //
//                    // but List a should not unify with List b, necessarily, so this way of doing
//                    // it might be an issue
//                    (true, None) => check_or_err(
//                        // make sure type variables that start with numbers are syntactically
//                        // prohibited
//                        //
//                        // orr maybe we should have a special namespace for compiler generated type
//                        // variables!
//                        Type::List(Box::new(Type::Var(get_unique_id()))),
//                        current_type,
//                    ),
//                }
//            }
//        },
//        AST::Type(typ, expr) => check_expr(*expr, Some(typ), environment),
//        AST::Add(expr1, expr2) => check_expr(*expr1, Some(Type::I64), environment.clone())
//            .and_then(|_| check_expr(*expr2, Some(Type::I64), environment)),
//        other => panic!("Type checking not yet implemented for {:?}", other),
//    }
//}

//fn infer_expr(expr: AST, environment: Env) -> Result<Type, TypeError> {
//    match expr {
//        AST::Lit(lit) => match lit {
//            Lit::I64(_) => Ok(Type::I64),
//            Lit::Bool(_) => Ok(Type::Bool),
//            Lit::String(_) => Ok(Type::String),
//            Lit::Symbol(_) => Ok(Type::Symbol),
//            Lit::List(lits) => Ok(Type::List(Box::new(infer_expr(
//                AST::Lit(lits.first().unwrap().clone()),
//                environment,
//            )?))),
//        },
//        AST::Add(expr1, expr2) => {
//            check_expr(*expr1, Some(Type::I64), environment.clone())?;
//            check_expr(*expr2, Some(Type::I64), environment)?;

//            Ok(Type::I64)
//        }
//        AST::Type(typ, _) => Ok(typ),
//        other => panic!("Type inference not yet implemented for {:?}", other),
//    }
//}

#[cfg(test)]
mod test {
    use super::*;
    use crate::data::Env;
    use crate::parse::tokenize;

    #[test]
    fn test_typecheck_simple() {
        let ast = tokenize("(: I64 (+ (: I64 1) (: I64 1)))").unwrap().parse();

        let result = infer_expr(ast, Env::new()).unwrap();

        assert_eq!(result, Type::I64)
    }

    #[test]
    fn test_typecheck_simple_err() {
        let ast = tokenize("(: I64 (+ (: I64 true) (: I64 1)))")
            .unwrap()
            .parse();

        let result = infer_expr(ast, Env::new()).unwrap_err();

        assert_eq!(
            result,
            TypeError {
                expected: Type::I64,
                given: Type::Bool
            }
        )
    }
}
