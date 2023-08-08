use crate::data::{Env, Lit, Toplevel, AST};

pub fn evaluate(Toplevel(forms): Toplevel) -> Result<Lit, String> {
    evaluate_top(forms, Env::new())
}

pub fn evaluate_top(forms: Vec<AST>, mut environment: Env<AST>) -> Result<Lit, String> {
    match forms.as_slice() {
        [AST::MacroTypeDec(..) | AST::TypeDec(..), rest @ ..] => evaluate_top(rest.to_vec(), environment),
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
        [] => {
            Err("Evaluator: This should never have gotten past the expander, this is a bug!".into())
        }
    }
}

pub fn evaluate_expr(program: AST, mut environment: Env<AST>) -> Result<Lit, String> {
    match dbg!(program.clone()) {
        AST::Type(_, expr) => evaluate_expr(*expr, environment.to_owned()),
        AST::Call(ident, actual_args) => match environment.lookup(&ident) {
            Ok(AST::Func(_, formal_args, body)) => {
                let environment: Result<Env<AST>, String> = formal_args
                    .iter()
                    .zip(actual_args.iter())
                    .fold(Ok(environment.to_owned()), |env, (ident, ast)| {
                        Ok(env?.insert(
                            ident.to_owned(),
                            // we have to evaluate the binding here, because we need to avoid it
                            // being defined in terms of itself when e.g. we're recursive
                            AST::Lit(evaluate_expr(ast.to_owned(), environment.to_owned())?),
                        ))
                    });
                evaluate_expr(*body, environment?)
            }
            _ => Err(format!("Could not find function {:?}", ident)),
        },
        AST::Add(num1, num2) => match (
            evaluate_expr(*num1, environment.to_owned())?,
            evaluate_expr(*num2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 + num2)),
            _ => Err("Attempted to add two non-numbers!".into()),
        },
        AST::Sub(num1, num2) => match (
            evaluate_expr(*num1, environment.to_owned())?,
            evaluate_expr(*num2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 - num2)),
            _ => Err("Attempted to subtract two non-numbers!".into()),
        },
        AST::Div(num1, num2) => match (
            evaluate_expr(*num1, environment.to_owned())?,
            evaluate_expr(*num2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 / num2)),
            _ => Err("Attempted to divide two non-numbers!".into()),
        },
        AST::Mod(num1, num2) => match (
            evaluate_expr(*num1, environment.to_owned())?,
            evaluate_expr(*num2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 % num2)),
            _ => Err("Attempted to take the modulus of two non-numbers!".into()),
        },
        AST::Mult(num1, num2) => match (
            evaluate_expr(*num1, environment.to_owned())?,
            evaluate_expr(*num2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::I64(num1 * num2)),
            _ => Err("Attempted to multiply two non-numbers!".into()),
        },
        AST::Lit(lit) => Ok(lit),
        AST::List(elems) => Ok(Lit::List(elems.iter().fold(
            Ok(Vec::new()),
            |results: Result<Vec<Lit>, String>, elem| {
                let mut results = results?;
                results.push(evaluate_expr((*elem).clone(), environment.to_owned())?);
                Ok(results)
            },
        )?)),
        AST::Car(list) => match evaluate_expr(*list, environment.to_owned())? {
            Lit::List(lits) => match lits.as_slice() {
                [first, ..] => Ok((*first).clone()),
                [] => Err("No elements remaining in list given to car!".to_string()),
            },
            other => Err(format!("Non-list given as argument to cons: {:?}", other)),
        },
        AST::Cdr(list) => match evaluate_expr(*list, environment.to_owned())? {
            Lit::List(lits) => match lits.as_slice() {
                [_, rest @ ..] => Ok(Lit::List(rest.to_vec())),
                [] => Err("No elements remaining in list given to cdr!".to_string()),
            },
            other => Err(format!("Non-list given as argument to cons: {:?}", other)),
        },
        AST::Cons(elem, list) => {
            let elem = evaluate_expr(*elem, environment.to_owned())?;
            let list = evaluate_expr(*list, environment.to_owned())?;

            match list {
                Lit::List(mut elems) => {
                    elems.insert(0, elem);
                    Ok(Lit::List(elems))
                }
                _ => Err(format!(
                    "Non-list given as a second argument to cons: {:?}",
                    list
                )),
            }
        }
        AST::Emptyp(list) => match evaluate_expr(*list, environment.clone())? {
            Lit::List(list) => Ok(match list.as_slice() {
                [] => Lit::Bool(true),
                [..] => Lit::Bool(false),
            }),
            other => Err(format!(
                "Non-list given as an argument to empty?: {:?}",
                other
            )),
        },
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
                _ => Err(format!(
                    "Non-boolean expression encountered as conditional guard: {:?}",
                    cond_expr
                )),
            }
        }
        AST::Eq(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::Bool(num1 == num2)),
            (Lit::Bool(bool1), Lit::Bool(bool2)) => Ok(Lit::Bool(bool1 == bool2)),
            (Lit::String(str1), Lit::String(str2)) => Ok(Lit::Bool(str1 == str2)),
            (Lit::Symbol(str1), Lit::Symbol(str2)) => Ok(Lit::Bool(str1 == str2)),
            // TODO: Add a test case for this!!!!
            (Lit::List(lit_vec1), Lit::List(lit_vec2)) => Ok(Lit::Bool(lit_vec1 == lit_vec2)),
            _ => Ok(Lit::Bool(false)),
        },
        AST::Lt(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::Bool(num1 < num2)),
            other => Err(format!("Non-numeric argument(s) given to <: {:?}", other)),
        },
        AST::Gt(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::I64(num1), Lit::I64(num2)) => Ok(Lit::Bool(num1 > num2)),
            other => Err(format!("Non-numeric argument(s) given to >: {:?}", other)),
        },
        AST::And(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::Bool(bool1), Lit::Bool(bool2)) => Ok(Lit::Bool(bool1 && bool2)),
            other => Err(format!(
                "Non-boolean arguments received for &&: {:?}",
                other
            )),
        },
        AST::Or(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::Bool(bool1), Lit::Bool(bool2)) => Ok(Lit::Bool(bool1 || bool2)),
            other => Err(format!(
                "Non-boolean arguments received for ||: {:?}",
                other
            )),
        },
        AST::Concat(expr1, expr2) => match (
            evaluate_expr(*expr1, environment.to_owned())?,
            evaluate_expr(*expr2, environment.to_owned())?,
        ) {
            (Lit::String(str1), Lit::String(str2)) => Ok(Lit::String(str1 + &str2)),
            other => Err(format!("Non-string arguments given to ++: {:?}", other)),
        },
        AST::Var(ident) => environment
            .lookup(&ident)
            .map(|expr| evaluate_expr(expr, environment))?,
        AST::Eval(expr) => {
            let prog = evaluate_expr(*expr, environment.to_owned())?;
            evaluate_expr(prog.to_elem().parse(), environment.to_owned())
        }
        AST::ParseInt(expr) => match evaluate_expr(*expr, environment.to_owned())? {
            Lit::Symbol(str) => {
                let parsed_str = str.parse::<i64>().map_err(|err| err.to_string())?;
                Ok(Lit::I64(parsed_str))
            }
            other => Err(format!("Unable to parse {:?} as integer", other)),
        },
        AST::Rewrite(expr, _) => evaluate_expr(*expr, environment),
        _ => Err(format!("Unable to evaluate the tree {:?}", program)),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::expand::expand;
    use crate::parse::tokenize;

    #[test]
    fn test_evaluate_1() {
        let res: Lit =
            evaluate(tokenize("((+ (+ 1 1) (- 1 1)))").unwrap().parse_toplevel()).unwrap();
        let target: Lit = Lit::I64(2);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_2() {
        let res: Lit = evaluate(
            tokenize("((let a 4 (+ (+ 1 1) (+ 1 a))))")
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::I64(7);

        assert_eq!(res, target);
    }

    #[test]
    #[should_panic]
    fn test_evaluate_4() {
        evaluate(tokenize("((+ a 1))").unwrap().parse_toplevel()).unwrap();
    }

    #[test]
    fn test_evaluate_func() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    "((fn add1 (num) (+ num 1))
                      (add1 1))",
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();
        let target: Lit = Lit::I64(2);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_func_rec() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    "((fn exp (base exponent)
                      (if (== exponent 0)
                         1
                         (* base (exp base (- exponent 1)))))
                      (exp 2 4))",
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();
        let target: Lit = Lit::I64(16);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_and() {
        let res: Lit = evaluate(tokenize("((&& true false))").unwrap().parse_toplevel()).unwrap();
        let target: Lit = Lit::Bool(false);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_or_1() {
        let res: Lit = evaluate(tokenize("((|| true false))").unwrap().parse_toplevel()).unwrap();
        let target: Lit = Lit::Bool(true);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_or_2() {
        let res: Lit = evaluate(
            tokenize("((|| (== 1 1) (== true false)))")
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::Bool(true);

        assert_eq!(res, target);
    }

    #[test]
    fn test_evaluate_concat() {
        let res: Lit = evaluate(
            tokenize(r#"((++ "hey " "there")))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::String("hey there".to_string());

        assert_eq!(res, target);
    }

    #[test]
    fn test_litlist_1() {
        let res: Lit = evaluate(
            tokenize(r#"((list 4 4 4 7 7 7 7))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::List(vec![
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_litlist_2() {
        let res: Lit = evaluate(
            tokenize(r#"((list 4 4 4 7 (+ 3 4) 7 (+ 3 4)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::List(vec![
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_car() {
        let res: Lit = evaluate(
            tokenize(r#"((car (list 4 4 4 7 7 7 7)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::I64(4);

        assert_eq!(res, target);
    }

    #[test]
    fn test_cdr() {
        let res: Lit = evaluate(
            tokenize(r#"((cdr (list 4 4 4 4 7 7 7 7)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::List(vec![
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_cons() {
        let res: Lit = evaluate(
            tokenize(r#"((cons 4 (list 4 4 4 7 7 7 7)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::List(vec![
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_list_4() {
        let res: Lit = evaluate(
            tokenize(r#"((cons (+ 2 5) (list (+ 2 5) (+ 2 5) 3 4 7)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::List(vec![
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(3),
            Lit::I64(4),
            Lit::I64(7),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_list_5() {
        let res: Lit = evaluate(
            tokenize(r#"((car (car (cdr (cons (+ 1 1) (list (list 4)))))))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();
        let target: Lit = Lit::I64(4);

        assert_eq!(res, target);
    }

    #[test]
    fn test_sort_empty() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn length (input-list)
                   (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
                 (fn merge (input-list-1 input-list-2)
                   (if (empty? input-list-1)
                       input-list-2
                       (if (empty? input-list-2)
                           input-list-1
                           (let elem-1 (car input-list-1)
                             (let elem-2 (car input-list-2)
                               (if (< elem-1 elem-2)
                                   (cons elem-1 (merge (cdr input-list-1) input-list-2))
                                   (cons elem-2 (merge input-list-1 (cdr input-list-2)))))))))
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
                 (sort (list)))
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::List(Vec::new());

        assert_eq!(res, target);
    }

    #[test]
    fn test_sort_singleton() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn length (input-list)
                   (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
                 (fn merge (input-list-1 input-list-2)
                   (if (empty? input-list-1)
                       input-list-2
                       (if (empty? input-list-2)
                           input-list-1
                           (let elem-1 (car input-list-1)
                             (let elem-2 (car input-list-2)
                               (if (< elem-1 elem-2)
                                   (cons elem-1 (merge (cdr input-list-1) input-list-2))
                                   (cons elem-2 (merge input-list-1 (cdr input-list-2)))))))))
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
                 (sort (list 1)))
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::List(vec![Lit::I64(1)]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_sort_id() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn length (input-list)
                   (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
                 (fn merge (input-list-1 input-list-2)
                   (if (empty? input-list-1)
                       input-list-2
                       (if (empty? input-list-2)
                           input-list-1
                           (let elem-1 (car input-list-1)
                             (let elem-2 (car input-list-2)
                               (if (< elem-1 elem-2)
                                   (cons elem-1 (merge (cdr input-list-1) input-list-2))
                                   (cons elem-2 (merge input-list-1 (cdr input-list-2)))))))))
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
                 (sort (list 3 4 8 7 7 11 11)))
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::List(vec![
            Lit::I64(3),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(8),
            Lit::I64(11),
            Lit::I64(11),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_sort() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn length (input-list)
                   (if (empty? input-list) 0 (+ 1 (length (cdr input-list)))))
                 (fn merge (input-list-1 input-list-2)
                   (if (empty? input-list-1)
                       input-list-2
                       (if (empty? input-list-2)
                           input-list-1
                           (let elem-1 (car input-list-1)
                             (let elem-2 (car input-list-2)
                               (if (< elem-1 elem-2)
                                   (cons elem-1 (merge (cdr input-list-1) input-list-2))
                                   (cons elem-2 (merge input-list-1 (cdr input-list-2)))))))))
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
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::List(vec![
            Lit::I64(3),
            Lit::I64(4),
            Lit::I64(7),
            Lit::I64(7),
            Lit::I64(8),
            Lit::I64(11),
            Lit::I64(11),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_quote_1() {
        let res: Lit = evaluate(
            tokenize(
                r#"
                ((quote (+ 1 1)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::List(vec![
            Lit::Symbol("+".to_string()),
            Lit::Symbol("1".to_string()),
            Lit::Symbol("1".to_string()),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_quote_2() {
        let res: Lit = evaluate(
            tokenize(
                r#"
                ((cons (quote hey) (quote (a b (c "hey" e) f g h))))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::List(vec![
            Lit::Symbol("hey".to_string()),
            Lit::Symbol("a".to_string()),
            Lit::Symbol("b".to_string()),
            Lit::List(vec![
                Lit::Symbol("c".to_string()),
                Lit::String("hey".to_string()),
                Lit::Symbol("e".to_string()),
            ]),
            Lit::Symbol("f".to_string()),
            Lit::Symbol("g".to_string()),
            Lit::Symbol("h".to_string()),
        ]);

        assert_eq!(res, target);
    }

    #[test]
    fn test_quote_4() {
        let res: Lit = evaluate(
            tokenize(
                r#"
                ((eval (quote (+ 1 1))))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::I64(2);

        assert_eq!(res, target);
    }

    #[test]
    fn test_eval_1() {
        let res: Lit = evaluate(
            tokenize(
                r#"
                ((eval 1)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::I64(1);

        assert_eq!(res, target);
    }

    #[test]
    fn test_eval_2() {
        let res: Lit = evaluate(
            tokenize(
                r#"
                ((eval (eval 1)))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::I64(1);

        assert_eq!(res, target);
    }

    #[test]
    fn test_eval_4() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn gen-quoted-list () (quote (1 1)))
                 (eval (cons (quote +) (gen-quoted-list))))
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::I64(2);

        assert_eq!(res, target);
    }

    #[test]
    fn test_eval_5() {
        let res: Lit = evaluate(
            expand(
                tokenize(
                    r#"
                ((fn return-two-numbers ()
                     (quote (4 4)))
                 (eval
                   (cons (quote *) (cons (quote 4) (list (cons (quote *) (return-two-numbers)))))))
                "#,
                )
                .unwrap()
                .parse_toplevel(),
            )
            .unwrap(),
        )
        .unwrap();

        let target: Lit = Lit::I64(64);

        assert_eq!(res, target);
    }

    #[test]
    #[should_panic]
    fn test_eval_7() {
        evaluate(
            tokenize(
                r#"
                ((fn return-two-numbers ()
                     (quote (4 4)))
                 (eval
                   (cons (quote *) (cons (quote 4) (cons (quote *) (return-two-numbers))))))
                "#,
            )
            .unwrap()
            .parse_toplevel(),
        )
        .unwrap();

        // let target: Result<Lit, String> = Err("Special form used incorrectly: *".to_string());

        // assert_eq!(res, target);
    }

    #[test]
    fn test_eq_list() {
        let result = evaluate(
            tokenize(r#"((== (list 1 2 4 4) (list 1 2 4 4)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::Bool(true);

        assert_eq!(result, target);
    }

    #[test]
    fn test_not_eq_list_1() {
        let result = evaluate(
            tokenize(r#"((== (list 1 2 3 4) (list 1 2 4 4)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::Bool(false);

        assert_eq!(result, target);
    }

    #[test]
    fn test_not_eq_list_2() {
        let result = evaluate(
            tokenize(r#"((== (list 1 2 3 4) (list 1 2 3 4 1)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::Bool(false);

        assert_eq!(result, target);
    }

    #[test]
    fn test_not_eq_list_4() {
        let result = evaluate(
            tokenize(r#"((== (list 1 2 3 4 1) (list 1 2 3 4)))"#)
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::Bool(false);

        assert_eq!(result, target);
    }

    #[test]
    fn test_types_ignored() {
        let result: Lit = evaluate(
            tokenize("((: I64 (+ (: I64 1) (: I64 1))))")
                .unwrap()
                .parse_toplevel(),
        )
        .unwrap();

        let target: Lit = Lit::I64(2);

        assert_eq!(result, target);
    }
}
