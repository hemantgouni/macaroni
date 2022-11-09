use std::collections::HashMap;

use crate::data::{Ident, Lit, Toplevel, AST};

#[derive(Clone)]
struct Env(pub HashMap<Ident, AST>);

impl Env {
    fn insert(&mut self, ident: Ident, ast: AST) -> Self {
        match self {
            Env(map) => {
                map.insert(ident, ast);
                Env(map.clone())
            }
        }
    }

    fn lookup(&mut self, ident: &Ident) -> Result<AST, String> {
        match self {
            Env(map) => map
                .get(&ident)
                .cloned()
                .ok_or(format!("No binding found: {:?}", ident)),
        }
    }
}

pub fn evaluate(Toplevel(forms): Toplevel) -> Result<Lit, String> {
    evaluate_top(forms, Env(HashMap::new()))
}

fn evaluate_top(forms: Vec<AST>, mut environment: Env) -> Result<Lit, String> {
    match forms.as_slice() {
        [func @ AST::Func(ident, _, _), rest @ ..] => evaluate_top(
            rest.to_vec(),
            environment.insert(ident.clone(), func.clone()),
        ),
        [mac @ AST::Macro(ident, _, _), rest @ ..] => evaluate_top(
            rest.to_vec(),
            environment.insert(ident.clone(), mac.clone()),
        ),
        // this stops registering functions at the first non-decl form
        [expr, ..] => evaluate_expr(expr.clone(), environment),
        [] => panic!("No top-level forms or evaluable expressions provided!"),
    }
}

fn evaluate_expr(program: AST, mut environment: Env) -> Result<Lit, String> {
    match program {
        AST::Call(ident, formal_args) => match environment.lookup(&ident) {
            Ok(AST::Func(_, actual_args, body)) => {
                let environment: Env = actual_args
                    .iter()
                    .zip(formal_args.iter())
                    .fold(environment.to_owned(), |mut env, (ident, ast)| {
                        env.insert(ident.to_owned(), ast.to_owned())
                    });
                evaluate_expr(*body, environment)
            }
            _ => panic!("Could not find function {:?}", ident),
        },
        AST::Add(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 + num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Sub(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 - num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Div(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 / num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Mult(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 * num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Lit(lit) => Ok(lit),
        AST::Let(ident, bind_expr, body_expr) => {
            let res = evaluate_expr(*bind_expr, environment.to_owned())?;
            evaluate_expr(*body_expr, environment.insert(ident, AST::Lit(res)))
        }
        AST::Ite(cond_expr, then_expr, else_expr) => {
            match evaluate_expr(*cond_expr.to_owned(), environment.to_owned())? {
                Lit::Bool(bool_lit) => {
                    if bool_lit {
                        evaluate_expr(*then_expr, environment.to_owned())
                    } else {
                        evaluate_expr(*else_expr, environment.to_owned())
                    }
                }
                _ => panic!(
                    "Non-boolean expression encountered as conditional guard: {:?}",
                    cond_expr
                ),
            }
        }
        AST::Eq(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::Bool(num1 == num2)),
            (Lit::Bool(bool1), Lit::Bool(bool2)) => Ok(Lit::Bool(bool1 == bool2)),
            (Lit::String(str1), Lit::String(str2)) => Ok(Lit::Bool(str1 == str2)),
            _ => panic!(),
        },
        AST::Symbol(ident) => environment
            .lookup(&ident)
            .map(|expr| evaluate_expr(expr, environment))?,
        _ => Err(format!("Unable to evaluate the tree {:?}", program)),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parse::parse;

    #[test]
    fn test_evaluate_1() {
        let res: Lit = evaluate(parse("((+ (+ 1 1) (- 1 1)))").unwrap().into()).unwrap();
        let target: Lit = Lit::I64(2);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_2() {
        let res: Lit = evaluate(parse("((let a 4 (+ (+ 1 1) (+ 1 a))))").unwrap().into()).unwrap();
        let target: Lit = Lit::I64(7);

        assert_eq!(res, target);
    }

    #[test]
    #[should_panic]
    fn test_evaluate_4() {
        evaluate(parse("((+ a 1))").unwrap().into()).unwrap();
    }
}
