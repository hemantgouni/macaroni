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
}

fn evaluate_top(forms: Vec<AST>, mut environment: Env) -> Result<Lit, String> {
    match forms.as_slice() {
        [func @ AST::Func(Ident(name), _, _), rest @ ..] => evaluate_top(
            rest.to_vec(),
            environment.insert(name.clone(), func.clone()),
        ),
        _ => Err(format!("Unable to evaluate the toplevel form {:#?}", forms)),
    }
}

fn evaluate(program: AST, environment: Env) -> Result<Lit, String> {
    match program {
        AST::Add(expr1, expr2) => match (
            evaluate(*expr1, environment.to_owned())?,
            evaluate(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 + num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Sub(expr1, expr2) => match (
            evaluate(*expr1, environment.to_owned())?,
            evaluate(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 - num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Div(expr1, expr2) => match (
            evaluate(*expr1, environment.to_owned())?,
            evaluate(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 / num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Mult(expr1, expr2) => match (
            evaluate(*expr1, environment.to_owned())?,
            evaluate(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 * num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        _ => Err(format!("Unable to evaluate the tree {:#?}", program)),
    }
}

#[cfg(test)]
mod test {

    #[test]
    fn test_evaluate_1() {}
}
