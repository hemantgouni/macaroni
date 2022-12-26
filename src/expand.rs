use crate::data::{Env, Ident, Lit, Toplevel, AST};
use crate::evaluate::evaluate_expr;
use crate::utils::concat;

fn expand_expr(expr: AST, mut environment: Env) -> Result<AST, String> {
    match expr {
        AST::MacroCall(ident, actual_args) => match environment.lookup(dbg!(&ident)) {
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

                let expanded: AST = dbg!(expand_expr(*body, environment.clone()?)?);

                dbg!(evaluate_expr(expanded, environment?)).map(|lit| lit.to_elem().parse())
            }
            Ok(AST::Func(..)) => Ok(AST::Call(
                ident,
                actual_args.iter().fold(
                    Ok(vec![]),
                    |arg_vec: Result<Vec<AST>, String>, expr: &Lit| {
                        Ok(concat(
                            // TODO: order matters here; see if we made this mistake anywhere else!!
                            arg_vec?,
                            vec![expand_expr(
                                expr.clone().to_elem().parse(),
                                environment.clone(),
                            )?],
                        ))
                    },
                )?,
            )),
            _ => Err("Unexpected or non-existent top-level binding in environment!".to_string()),
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
        AST::Add(expr1, expr2) => Ok(AST::Add(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Sub(expr1, expr2) => Ok(AST::Sub(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Mult(expr1, expr2) => Ok(AST::Mult(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Cons(expr1, expr2) => Ok(AST::Cons(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Car(expr) => Ok(AST::Car(Box::new(expand_expr(*expr, environment.clone())?))),
        AST::Cdr(expr) => Ok(AST::Cdr(Box::new(expand_expr(*expr, environment.clone())?))),
        // We need to do the same rewriting thing here!
        AST::Let(var, binding, expr) => Ok(AST::Let(
            var,
            Box::new(expand_expr(*binding, environment.clone())?),
            Box::new(expand_expr(*expr, environment.clone())?),
        )),
        AST::Ite(guard, expr1, expr2) => Ok(AST::Ite(
            Box::new(expand_expr(*guard, environment.clone())?),
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Lt(expr1, expr2) => Ok(AST::Lt(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Eq(expr1, expr2) => Ok(AST::Eq(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Emptyp(expr) => Ok(AST::Emptyp(Box::new(expand_expr(
            *expr,
            environment.clone(),
        )?))),
        AST::Lit(lit) => Ok(AST::Lit(lit)),
        AST::Ident(ident) => environment.lookup(&ident),
        other => Err(format!("Macro expansion yet implemented for {:?}", other)),
    }
}

fn expand_top(forms: Vec<AST>, in_env: Env, mut out_env: Env) -> Result<Vec<AST>, String> {
    match forms.as_slice() {
        [AST::Func(ident, args, body), rest @ ..] | [AST::Macro(ident, args, body), rest @ ..] => {
            let rewrite_to_ident: fn(AST) -> AST = |ast: AST| match ast {
                AST::Lit(Lit::Symbol(string)) => AST::Ident(Ident(string)),
                _ => panic!("Ident rewrite lambda called on non-symbol: this is a bug!"),
            };

            let binding_list: Vec<(Ident, AST)> = args
                .iter()
                .map(|Ident(arg_str)| {
                    (
                        Ident(arg_str.to_string()),
                        AST::Rewrite(
                            Box::new(AST::Lit(Lit::Symbol(arg_str.to_string()))),
                            rewrite_to_ident,
                        ),
                    )
                })
                .collect();

            let bind_env: Env = binding_list.iter().fold(
                Ok(in_env.to_owned()),
                |env: Result<Env, String>, (ident, ast)| {
                    Ok(env?.insert(ident.to_owned(), ast.to_owned()))
                },
            )?;

            let expanded_func: AST = AST::Func(
                ident.to_owned(),
                args.to_owned(),
                Box::new(expand_expr(*body.to_owned(), bind_env.to_owned())?.rewrite()),
            );

            Ok(concat(
                vec![expanded_func.to_owned()],
                expand_top(
                    rest.to_vec(),
                    in_env,
                    out_env.insert(ident.to_owned(), expanded_func),
                )?,
            ))
        }
        [expr, ..] => Ok(vec![expand_expr(expr.to_owned(), out_env)?]),
        [] => Err(
            "expand_top either didn't find any top-level forms or a runnable expr. This is a bug!"
                .to_string(),
        ),
    }
}

fn register_top(forms: Vec<AST>, mut environment: Env) -> Env {
    match forms.as_slice() {
        [func @ AST::Func(ident, _, _), rest @ ..] => register_top(
            rest.to_vec(),
            environment.insert(ident.clone(), func.clone()),
        ),
        [mac @ AST::Macro(ident, _, _), rest @ ..] => register_top(
            rest.to_vec(),
            environment.insert(ident.clone(), mac.clone()),
        ),
        [..] => environment,
    }
}

pub fn expand(Toplevel(forms): Toplevel) -> Result<Toplevel, String> {
    Ok(Toplevel(expand_top(
        forms.to_owned(),
        register_top(forms, Env::new()),
        Env::new(),
    )?))
}
