use crate::data::{Elem, Ident, Lit, Toplevel, AST};

// parses all non-toplevel expressions
impl From<Elem<'_>> for AST {
    fn from(elem: Elem) -> AST {
        match elem {
            Elem::String(str) => AST::Lit(Lit::String(str.into())),
            Elem::Symbol(str) => str
                .to_string()
                .parse::<i64>()
                .map(|int| AST::Lit(Lit::I64(int)))
                .unwrap_or_else(|_| {
                    str.to_string()
                        .parse::<bool>()
                        .map(|bool| AST::Lit(Lit::Bool(bool)))
                        .unwrap_or_else(|_| AST::Symbol(str.into()))
                }),
            Elem::List(elems) => match elems.as_slice() {
                [Elem::Symbol("list"), rest @ ..] => {
                    AST::List(rest.iter().map(|elem| elem.clone().into()).collect())
                }
                [Elem::Symbol("cons"), elem, list] => {
                    AST::Cons(Box::new(elem.clone().into()), Box::new(list.clone().into()))
                }
                [Elem::Symbol("car"), list] => AST::Car(Box::new(list.clone().into())),
                [Elem::Symbol("cdr"), list] => AST::Cdr(Box::new(list.clone().into())),
                [Elem::Symbol("if"), cond_expr, then_expr, else_expr] => AST::Ite(
                    Box::new(cond_expr.clone().into()),
                    Box::new(then_expr.clone().into()),
                    Box::new(else_expr.clone().into()),
                ),
                [Elem::Symbol("=="), expr1, expr2] => AST::Eq(
                    Box::new(expr1.clone().into()),
                    Box::new(expr2.clone().into()),
                ),
                [Elem::Symbol("&&"), expr1, expr2] => AST::And(
                    Box::new(expr1.clone().into()),
                    Box::new(expr2.clone().into()),
                ),
                [Elem::Symbol("||"), expr1, expr2] => AST::Or(
                    Box::new(expr1.clone().into()),
                    Box::new(expr2.clone().into()),
                ),
                [Elem::Symbol("quote"), rest @ ..] => AST::Quote(
                    rest.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                ),
                [Elem::Symbol("let"), Elem::Symbol(ident), expr1, expr2] => AST::Let(
                    (*ident).into(),
                    Box::new(expr1.clone().into()),
                    Box::new(expr2.clone().into()),
                ),
                [Elem::Symbol("++"), str1, str2] => {
                    AST::Concat(Box::new(str1.clone().into()), Box::new(str2.clone().into()))
                }
                [Elem::Symbol("+"), num1, num2] => {
                    AST::Add(Box::new(num1.clone().into()), Box::new(num2.clone().into()))
                }
                [Elem::Symbol("-"), num1, num2] => {
                    AST::Sub(Box::new(num1.clone().into()), Box::new(num2.clone().into()))
                }
                [Elem::Symbol("/"), num1, num2] => {
                    AST::Div(Box::new(num1.clone().into()), Box::new(num2.clone().into()))
                }
                [Elem::Symbol("*"), num1, num2] => {
                    AST::Mult(Box::new(num1.clone().into()), Box::new(num2.clone().into()))
                }
                [Elem::Symbol(ident), rest @ ..] => AST::Call(
                    (*ident).into(),
                    rest.iter().map(|elem| elem.to_owned().into()).collect(),
                ),
                other => panic!("Unable to abstractify: {:#?}", other),
            },
        }
    }
}

// parses all expressions, plus top-level declarations
impl From<Elem<'_>> for Toplevel {
    fn from(elem: Elem) -> Toplevel {
        match elem {
            Elem::List(elems) => Toplevel(elems.iter().map(|elem| match elem {
                Elem::List(toplevel_form) => match toplevel_form.as_slice() {
                    [Elem::Symbol("fn"), Elem::Symbol(ident), Elem::List(args), body] =>
                        AST::Func(
                            (*ident).into(),
                            args.iter()
                                .map(|elem| match elem {
                                    Elem::Symbol(str) => (*str).into(),
                                    other => panic!(
                                        "Only valid identifiers allowed in argument lists: {:?}",
                                        other
                                    ),
                                })
                                .collect::<Vec<Ident>>(),
                            Box::new(body.to_owned().into()),
                        ),
                    [Elem::Symbol("macro"), Elem::Symbol(ident), Elem::List(args), body] =>
                        AST::Macro(
                            (*ident).into(),
                            args.iter()
                                .map(|elem| match elem {
                                    Elem::Symbol(str) => (*str).into(),
                                    other => panic!(
                                        "Only valid identifiers allowed in argument lists: {:?}",
                                        other
                                    ),
                                })
                                .collect::<Vec<Ident>>(),
                            Box::new(body.to_owned().into()),
                        ),
                    // defer to the AST impl to translate 'normal' exprs which
                    // could appear at the top level
                    _ => elem.to_owned().into(),
                },
                _ => elem.to_owned().into(),
            }).collect::<Vec<AST>>()),
            // The top level wasn't passed a list of top-level forms, error!
            _ => panic!("Parsing into toplevel form failed: {:#?}", elem),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parse::parse;

    #[test]
    fn test_from_1() {
        let res: AST = parse("(let a 4 (+ a 4))").unwrap().into();
        let target: AST = AST::Let(
            "a".into(),
            Box::new(AST::Lit(Lit::I64(4))),
            Box::new(AST::Add(
                Box::new(AST::Symbol("a".into())),
                Box::new(AST::Lit(Lit::I64(4))),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_2() {
        let res: AST = parse("(+ (+ 1 1) (+ 1 (+ 1 (+ 1 1))))").unwrap().into();
        let target: AST = AST::Add(
            Box::new(AST::Add(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Lit(Lit::I64(1))),
            )),
            Box::new(AST::Add(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Add(
                    Box::new(AST::Lit(Lit::I64(1))),
                    Box::new(AST::Add(
                        Box::new(AST::Lit(Lit::I64(1))),
                        Box::new(AST::Lit(Lit::I64(1))),
                    )),
                )),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_4() {
        let res: AST = parse("(quote a b c d e (+ 1 1))").unwrap().into();
        let target: AST = AST::Quote(vec![
            AST::Symbol("a".into()),
            AST::Symbol("b".into()),
            AST::Symbol("c".into()),
            AST::Symbol("d".into()),
            AST::Symbol("e".into()),
            AST::Add(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Lit(Lit::I64(1))),
            ),
        ]);
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_7() {
        let res: AST = parse("(/ 1 (- 1 (+ 1 (* 1 1))))").unwrap().into();
        let target: AST = AST::Div(
            Box::new(AST::Lit(Lit::I64(1))),
            Box::new(AST::Sub(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Add(
                    Box::new(AST::Lit(Lit::I64(1))),
                    Box::new(AST::Mult(
                        Box::new(AST::Lit(Lit::I64(1))),
                        Box::new(AST::Lit(Lit::I64(1))),
                    )),
                )),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_8() {
        let res: Toplevel = parse("((fn add1 (num) (+ 1 num)))").unwrap().into();
        let target: Toplevel = Toplevel(vec![AST::Func(
            "add1".into(),
            vec!["num".into()],
            Box::new(AST::Add(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Symbol("num".into())),
            )),
        )]);
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_10() {
        let res: Toplevel = parse(
            "((fn add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .into();
        let target: Toplevel = Toplevel(vec![
            AST::Func(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Lit(Lit::I64(1))),
                )),
            ),
            AST::Let(
                "a".into(),
                Box::new(AST::Lit(Lit::I64(4))),
                Box::new(AST::Add(
                    Box::new(AST::Lit(Lit::I64(1))),
                    Box::new(AST::Lit(Lit::I64(1))),
                )),
            ),
        ]);
        assert_eq!(res, target);
    }

    #[test]
    fn test_from_11() {
        let res: Toplevel = parse(
            "((macro add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .into();
        let target: Toplevel = Toplevel(vec![
            AST::Macro(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Lit(Lit::I64(1))),
                )),
            ),
            AST::Let(
                "a".into(),
                Box::new(AST::Lit(Lit::I64(4))),
                Box::new(AST::Add(
                    Box::new(AST::Lit(Lit::I64(1))),
                    Box::new(AST::Lit(Lit::I64(1))),
                )),
            ),
        ]);
        assert_eq!(res, target);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_12() {
        Toplevel::from(parse("(())").unwrap());
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_14() {
        Toplevel::from(parse("(+ 1 1)").unwrap());
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_15() {
        Toplevel::from(
            parse(
                "((fn add1 (num) (+ 1 num))
                  (fn 1))",
            )
            .unwrap(),
        );
    }

    #[test]
    fn test_from_16() {
        let res: Toplevel = parse(
            "
            ((fn add1 (num)
              (+ num 1))
             (add1 1))
        ",
        )
        .unwrap()
        .into();
        let target: Toplevel = Toplevel(vec![
            AST::Func(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Lit(Lit::I64(1))),
                )),
            ),
            AST::Call("add1".into(), vec![AST::Lit(Lit::I64(1))]),
        ]);
        assert_eq!(res, target);
    }

    #[test]
    #[allow(unused_must_use)]
    fn test_ident_1() {
        crate::data::Ident::from("variable1");
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_ident_2() {
        crate::data::Ident::from("fn");
    }

    #[test]
    fn test_list_1() {}
}
