use crate::data::{Env, Ident, Lit, Toplevel, AST};

fn expand_top(program: Toplevel, environment: Env) -> Toplevel {
    match program {
        _ => panic!(),
    }
}

fn expand(expr: AST, mut environment: Env) -> Result<AST, String> {
    match expr {
        AST::ExpandCall(ident, actual_args) => match environment.lookup(&ident) {
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

                expand(*body, environment?)
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
        AST::Eval(expr) => Ok(AST::Eval(Box::new(expand(*expr, environment)?))),
        AST::List(exprs) => Ok(AST::List({
            let exprs: Result<Vec<AST>, String> =
                exprs.iter().fold(Ok(Vec::new()), |exprs, expr| {
                    let var: AST = expand(expr.to_owned(), environment.to_owned())?;
                    let mut exprs = exprs?;
                    exprs.push(var);
                    Ok(exprs)
                });
            exprs?
        })),
        other => Ok(other),
    }
}
