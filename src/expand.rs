use crate::data::{Env, Ident, Lit, Toplevel, AST};
use crate::evaluate::evaluate_expr;
use crate::utils::concat;

fn expand_expr(expr: AST, mut environment: Env) -> Result<AST, String> {
    match dbg!(expr) {
        AST::MacroCall(ident, actual_args) => match environment.lookup(&ident) {
            Ok(AST::Macro(_, formal_args, body)) => {
                let binding_list: Vec<(Ident, Lit)> = formal_args
                    .iter()
                    .map(|ident| ident.to_owned())
                    .zip(dbg!(actual_args))
                    .collect();

                let environment: Result<Env, String> =
                    binding_list
                        .iter()
                        .fold(Ok(environment.to_owned()), |env, (ident, lit)| {
                            // We shouldn't expand the lit binding here, since the macro must receive
                            // it as syntax, unmodified
                            Ok(env?.insert(ident.to_owned(), AST::Lit(lit.to_owned())))
                        });

                let expanded: AST = expand_expr(*body, environment.clone()?)?;

                evaluate_expr(expanded, environment?).map(|lit| lit.to_elem().parse())
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
            other => Err(format!(
                "Unexpected or non-existent top-level binding in environment: {:?}",
                other
            )),
        },
        // TODO: Figure out why we need this!
        AST::Call(ident, actual_args) => Ok(AST::Call(
            ident,
            actual_args.iter().fold(
                Ok(Vec::new()),
                |args: Result<Vec<AST>, String>, arg: &AST| {
                    Ok(concat(
                        args?,
                        vec![expand_expr(arg.to_owned(), environment.clone())?],
                    ))
                },
            )?,
        )),
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
        AST::Div(expr1, expr2) => Ok(AST::Div(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Mod(expr1, expr2) => Ok(AST::Mod(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Concat(expr1, expr2) => Ok(AST::Concat(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Cons(expr1, expr2) => Ok(AST::Cons(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Car(expr) => Ok(AST::Car(Box::new(expand_expr(*expr, environment.clone())?))),
        AST::Cdr(expr) => Ok(AST::Cdr(Box::new(expand_expr(*expr, environment.clone())?))),
        AST::Let(Ident(string), binding, expr) => {
            let rewrite_to_ident: fn(AST) -> AST = |ast: AST| match ast {
                AST::Lit(Lit::Symbol(string)) => AST::Ident(Ident(string)),
                _ => panic!("Ident rewrite lambda called on non-symbol: this is a bug!"),
            };

            let environment = environment.insert(
                Ident(string.to_owned()),
                AST::Rewrite(
                    Box::new(AST::Lit(Lit::Symbol(string.to_owned()))),
                    rewrite_to_ident,
                ),
            );

            Ok(AST::Let(
                Ident(string),
                Box::new(expand_expr(*binding, environment.clone())?),
                Box::new(expand_expr(*expr, environment)?),
            )
            .rewrite())
        }
        AST::Ite(guard, expr1, expr2) => Ok(AST::Ite(
            Box::new(expand_expr(*guard, environment.clone())?),
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Lt(expr1, expr2) => Ok(AST::Lt(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Gt(expr1, expr2) => Ok(AST::Gt(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Eq(expr1, expr2) => Ok(AST::Eq(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Or(expr1, expr2) => Ok(AST::Or(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::And(expr1, expr2) => Ok(AST::And(
            Box::new(expand_expr(*expr1, environment.clone())?),
            Box::new(expand_expr(*expr2, environment.clone())?),
        )),
        AST::Emptyp(expr) => Ok(AST::Emptyp(Box::new(expand_expr(
            *expr,
            environment.clone(),
        )?))),
        AST::Lit(lit) => Ok(AST::Lit(lit)),
        AST::Ident(ident) => environment.lookup(&ident),
        other => Err(format!(
            "Macro expansion not yet implemented for {:?}",
            other
        )),
    }
}

fn expand_top(forms: Vec<AST>, in_env: Env, mut out_env: Env) -> Result<Vec<AST>, String> {
    match forms.as_slice() {
        [AST::Func(ident, args, body), rest @ ..] => {
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
                Box::new(expand_expr(*body.to_owned(), bind_env)?.rewrite()),
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
        [AST::Macro(ident, args, body), rest @ ..] => {
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

            let expanded_func: AST = AST::Macro(
                ident.to_owned(),
                args.to_owned(),
                Box::new(expand_expr(*body.to_owned(), bind_env)?.rewrite()),
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

mod test {

    #[test]
    fn test_expand_let() {
        use super::*;
        use crate::evaluate::evaluate;
        use crate::parse::tokenize;
        let program: Toplevel = tokenize(
            "
            ((fn fst (list-variable)
                (car list-variable))
             (fn snd (list-variable)
                (car (cdr list-variable)))
             (fn mlet-helper (bind-list body)
                (if (empty? bind-list)
                    body
                    (let pair (fst bind-list)
                      (list
                        (quote let)
                        (fst pair)
                        (snd pair)
                        (mlet-helper (cdr bind-list) body)))))
             (macro mlet (bind-list body)
                (mlet-helper bind-list body))
             (mlet ((a 4) (b 3) (c 5) (d 8)) (+ d (* c (+ a b)))))
             ",
        )
        .unwrap()
        .parse_toplevel();

        let result: Lit = evaluate(expand(program).unwrap()).unwrap();

        assert_eq!(result, Lit::I64(43));
    }
}
