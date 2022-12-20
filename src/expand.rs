use crate::data::{Env, Ident, Lit, Toplevel, AST};

fn expand_expr(expr: AST, mut environment: Env) -> Result<AST, String> {
    match expr {
        AST::MacroCall(ident, actual_args) => match environment.lookup(&ident) {
            Ok(AST::Macro(_, formal_args, body)) => {
                let binding_list: Vec<(Ident, Lit)> = formal_args
                    .iter()
                    .map(|ident| ident.to_owned())
                    .zip(actual_args)
                    .collect();

                let environment: Result<Env, String> =
                    binding_list
                        .iter()
                        .fold(Ok(environment.to_owned()), |env, (ident, lit)| {
                            // We shouldn't expand the lit binding here, since the macro must receive
                            // it as syntax, unmodified
                            Ok(env?.insert(ident.to_owned(), AST::Lit(lit.to_owned())))
                        });

                expand_expr(*body, environment?)
            }
            Ok(AST::Func(..)) => Ok(AST::Call(
                ident,
                actual_args
                    .iter()
                    .map(|sexpr| sexpr.to_elem().parse())
                    .collect(),
            )),
            _ => Err(format!(
                "Unexpected or non-existent top-level binding in environment!"
            )),
        },
        AST::Eval(expr) => Ok(AST::Eval(Box::new(expand_expr(*expr, environment)?))),
        AST::List(exprs) => Ok(AST::List({
            let exprs: Result<Vec<AST>, String> =
                exprs.iter().fold(Ok(Vec::new()), |exprs, expr| {
                    let var: AST = expand_expr(expr.to_owned(), environment.to_owned())?;
                    let mut exprs = exprs?;
                    exprs.push(var);
                    Ok(exprs)
                });
            exprs?
        })),
        other => Ok(other),
    }
}

fn expand_top(forms: Vec<AST>, mut environment: Env) -> Result<Vec<AST>, String> {
    use crate::utils::concat;

    match forms.as_slice() {
        [func @ AST::Func(ident, _, _), rest @ ..] => {
            let res: Vec<AST> = expand_top(
                rest.to_vec(),
                environment.insert(ident.clone(), func.clone()),
            )?;
            Ok(concat(vec![func.clone()], res))
        }
        [mac @ AST::Macro(ident, _, _), rest @ ..] => {
            let res: Vec<AST> = expand_top(
                rest.to_vec(),
                environment.insert(ident.clone(), mac.clone()),
            )?;
            Ok(concat(vec![mac.clone()], res))
        }
        [expr, ..] => Ok(vec![expand_expr(expr.clone(), environment.clone())?]),
        [] => Err("No top-level forms or evaluable expressions provided!".into()),
    }
}

fn expand(Toplevel(forms): Toplevel) -> Result<Toplevel, String> {
    Ok(Toplevel(expand_top(forms, Env::new())?))
}
