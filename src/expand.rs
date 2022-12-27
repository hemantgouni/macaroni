use crate::data::{Env, Ident, Lit, Toplevel, AST};
use crate::evaluate::evaluate_expr;
use crate::utils::concat;

fn expand_expr(expr: AST, mut environment: Env) -> Result<AST, String> {
    match expr {
        AST::MacroCall(ident, actual_args) => match dbg!(environment.clone()).lookup(&ident) {
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

                // This doesn't do anything! It'll be a bunch of lits, which we need to evaluate
                // first!
                //
                // let expanded: AST = expand_expr(*body, environment.clone()?)?;

                // We need to expand again here in case the evaluated thing contains any macros!
                expand_expr(
                    evaluate_expr(dbg!(*body), environment.clone()?)
                        .map(|lit| lit.to_elem().parse())?,
                    environment?,
                )
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

fn expand_top(forms: Vec<AST>, out_env: Env) -> Result<Vec<AST>, String> {
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

            let mut bind_env: Env = binding_list.iter().fold(
                Ok(out_env.to_owned()),
                |env: Result<Env, String>, (ident, ast)| {
                    Ok(env?.insert(ident.to_owned(), ast.to_owned()))
                },
            )?;

            let expanded_func: AST = AST::Func(
                ident.to_owned(),
                args.to_owned(),
                Box::new(
                    expand_expr(
                        *body.to_owned(),
                        bind_env.insert(
                            ident.to_owned(),
                            AST::Func(ident.to_owned(), args.to_owned(), body.to_owned()),
                        ),
                    )?
                    .rewrite(),
                ),
            );

            Ok(concat(
                vec![expanded_func.to_owned()],
                expand_top(
                    rest.to_vec(),
                    dbg!(out_env).insert(ident.to_owned(), expanded_func),
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
                Ok(out_env.to_owned()),
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
                    dbg!(out_env).insert(ident.to_owned(), expanded_func),
                )?,
            ))
        }
        [expr, ..] => Ok(vec![expand_expr(expr.to_owned(), dbg!(out_env))?]),
        [] => Err(
            "expand_top either didn't find any top-level forms or a runnable expr. This is a bug!"
                .to_string(),
        ),
    }
}

pub fn expand(Toplevel(forms): Toplevel) -> Result<Toplevel, String> {
    Ok(Toplevel(expand_top(forms.to_owned(), Env::new())?))
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::evaluate::evaluate;
    use crate::parse::tokenize;

    #[test]
    fn test_expand_let() {
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

    #[test]
    fn test_expand_sort() {
        let program: Toplevel = tokenize(
            "
            ((fn pair-fst (input-list)
                 (car (car input-list)))
             (fn pair-snd (input-list)
                 (car (cdr (car input-list))))
             (fn let-list-helper (bindings body)
                 (if (empty? bindings)
                   body
                   (list (quote let) (pair-fst bindings) (pair-snd bindings)
                         (let-list-helper (cdr bindings) body))))
             (macro let-list (bindings body)
                 (let-list-helper bindings body))
             (fn cond-helper (branch-list)
                 (if (== (pair-fst branch-list) (quote else))
                     (pair-snd branch-list)
                     (list (quote if) (pair-fst branch-list)
                           (pair-snd branch-list)
                           (cond-helper (cdr branch-list)))))
             (macro cond (branch-list)
                 (cond-helper branch-list))
             (fn length (input-list)
                 (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
             (fn merge (input-list-1 input-list-2)
                 (cond (((empty? input-list-1) input-list-2)
                        ((empty? input-list-2) input-list-1)
                        (else (let-list ((elem-1 (car input-list-1))
                                         (elem-2 (car input-list-2)))
                                  (if (< elem-1 elem-2)
                                      (cons elem-1
                                            (merge (cdr input-list-1) input-list-2))
                                      (cons elem-2
                                            (merge input-list-1 (cdr input-list-2)))))))))
             (fn take (num input-list)
                 (if (== num 0)
                   (list)
                   (cons (car input-list) (take (- num 1) (cdr input-list)))))
             (fn drop (num input-list)
                 (if (== num 0) input-list (drop (- num 1) (cdr input-list))))
             (fn sort (input-list)
                 (if (|| (empty? input-list) (== (length input-list) 1))
                   input-list
                   (let half-length (/ (length input-list) 2)
                     (merge (sort (take half-length input-list))
                            (sort (drop half-length input-list))))))
             (sort (list 8 3 4 11 7 11 7)))
            ",
        )
        .unwrap()
        .parse_toplevel();

        let result: Lit = evaluate(expand(program).unwrap()).unwrap();

        assert_eq!(
            result,
            Lit::List(
                vec![3, 4, 7, 7, 8, 11, 11]
                    .iter()
                    .map(|num: &i64| Lit::I64(*num))
                    .collect()
            )
        );
    }

    // This variant uses macros inside macro definitions!
    #[test]
    fn test_expand_sort_complex() {
        let program: Toplevel = tokenize(
            "
            ((fn pair-fst (input-list)
                 (car (car input-list)))
             (fn pair-snd (input-list)
                 (car (cdr (car input-list))))
             (fn cond-helper (branch-list)
                  (if (== (pair-fst branch-list) (quote else))
                      (pair-snd branch-list)
                      (list (quote if) (pair-fst branch-list)
                            (pair-snd branch-list)
                            (cond-helper (cdr branch-list)))))
             (macro cond (branch-list)
                 (cond-helper branch-list))
             (fn let-list-helper (bindings body)
                 (cond (((empty? bindings) body)
                        (else (list (quote let) (pair-fst bindings) (pair-snd bindings)
                                   (let-list-helper (cdr bindings) body))))))
             (macro let-list (bindings body)
                 (cond (((== 0 0) (let-list-helper bindings body))
                        (else (let-list-helper bindings body))))) 
             (fn length (input-list)
                 (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
             (fn merge (input-list-1 input-list-2)
                 (cond (((empty? input-list-1) input-list-2)
                        ((empty? input-list-2) input-list-1)
                        (else (let-list ((elem-1 (car input-list-1))
                                         (elem-2 (car input-list-2)))
                                  (if (< elem-1 elem-2)
                                      (cons elem-1
                                            (merge (cdr input-list-1) input-list-2))
                                      (cons elem-2
                                            (merge input-list-1 (cdr input-list-2)))))))))
             (fn take (num input-list)
                 (if (== num 0)
                   (list)
                   (cons (car input-list) (take (- num 1) (cdr input-list)))))
             (fn drop (num input-list)
                 (if (== num 0) input-list (drop (- num 1) (cdr input-list))))
             (fn sort (input-list)
                 (if (|| (empty? input-list) (== (length input-list) 1))
                   input-list
                   (let half-length (/ (length input-list) 2)
                     (merge (sort (take half-length input-list))
                            (sort (drop half-length input-list))))))
             (sort (list 8 3 4 11 7 11 7)))
            ",
        )
        .unwrap()
        .parse_toplevel();

        let result: Lit = evaluate(expand(program).unwrap()).unwrap();

        assert_eq!(
            result,
            Lit::List(
                vec![3, 4, 7, 7, 8, 11, 11]
                    .iter()
                    .map(|num: &i64| Lit::I64(*num))
                    .collect()
            )
        );
    }
}
