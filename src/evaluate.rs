use std::collections::HashMap;

use crate::data::{Ident, Lit, Toplevel, AST};

#[derive(Clone)]
struct Env(pub HashMap<String, AST>);

impl Env {
    fn insert(&mut self, string: String, ast: AST) -> Self {
        match self {
            Env(map) => {
                map.insert(string, ast);
                Env(map.clone())
            }
        }
    }

    fn lookup(&mut self, string: String) -> Result<AST, String> {
        match self {
            Env(map) => map
                .get(&string)
                .cloned()
                .ok_or(format!("No binding found: {:?}", string)),
        }
    }
}

pub fn evaluate(Toplevel(forms): Toplevel) -> Result<Lit, String> {
    evaluate_top(forms, Env(HashMap::new()))
}

fn evaluate_top(forms: Vec<AST>, mut environment: Env) -> Result<Lit, String> {
    match forms.as_slice() {
        [func @ AST::Func(Ident(name), _, _), rest @ ..] => evaluate_top(
            rest.to_vec(),
            environment.insert(name.clone(), func.clone()),
        ),
        [mac @ AST::Macro(Ident(name), _, _), rest @ ..] => {
            evaluate_top(rest.to_vec(), environment.insert(name.clone(), mac.clone()))
        }
        [expr, ..] => evaluate_expr(expr.clone(), environment),
        [] => panic!("No top-level forms provided!"),
    }
}

fn evaluate_expr(program: AST, mut environment: Env) -> Result<Lit, String> {
    match program {
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
        AST::Lit(num) => Ok(num),
        AST::Let(Ident(name), bind_expr, body_expr) => {
            let res = evaluate_expr(*bind_expr, environment.to_owned())?;
            evaluate_expr(*body_expr, environment.insert(name, AST::Lit(res)))
        }
        AST::Symbol(Ident(name)) => environment
            .lookup(name)
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
