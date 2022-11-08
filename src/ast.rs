use crate::data::{Elem, Toplevel, Value, AST};

// parses all non-toplevel expressions
impl From<Elem<'_>> for AST {
    fn from(elem: Elem) -> AST {
        match elem {
            Elem::String(str) => AST::Value(Value::String(str.into())),
            Elem::Symbol(str) => str
                .to_string()
                .parse::<i64>()
                .map(|int| AST::Value(Value::I64(int)))
                .unwrap_or_else(|_| AST::Symbol(str.into())),
            Elem::List(elems) => match elems.as_slice() {
                [Elem::Symbol("quote"), rest @ ..] => AST::Quote(
                    rest.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                ),
                [Elem::Symbol("unquote"), rest @ ..] => AST::Unquote(
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
                    rest.iter().map(|elem| dbg!(elem).to_owned().into()).collect(),
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
                                .map(|elem| elem.to_owned().into())
                                .collect::<Vec<AST>>(),
                            Box::new(body.to_owned().into()),
                        ),
                    [Elem::Symbol("macro"), Elem::Symbol(ident), Elem::List(args), body] =>
                        AST::Macro(
                            (*ident).into(),
                            args.iter()
                                .map(|elem| elem.to_owned().into())
                                .collect::<Vec<AST>>(),
                            Box::new(body.to_owned().into()),
                        ),
                    // defer to the AST impl to translate 'normal' exprs which
                    // could appear at the top level
                    _ => elem.to_owned().into(),
                },
                _ => panic!("Error: no list of top-level forms provided!"),
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
            Box::new(AST::Value(Value::I64(4))),
            Box::new(AST::Add(
                Box::new(AST::Symbol("a".into())),
                Box::new(AST::Value(Value::I64(4))),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_2() {
        let res: AST = parse("(+ (+ 1 1) (+ 1 (+ 1 (+ 1 1))))").unwrap().into();
        let target: AST = AST::Add(
            Box::new(AST::Add(
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Value(Value::I64(1))),
            )),
            Box::new(AST::Add(
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::I64(1))),
                    Box::new(AST::Add(
                        Box::new(AST::Value(Value::I64(1))),
                        Box::new(AST::Value(Value::I64(1))),
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
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Value(Value::I64(1))),
            ),
        ]);
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_5() {
        let res: AST = parse("(unquote a b c d e (+ 1 1))").unwrap().into();
        let target: AST = AST::Unquote(vec![
            AST::Symbol("a".into()),
            AST::Symbol("b".into()),
            AST::Symbol("c".into()),
            AST::Symbol("d".into()),
            AST::Symbol("e".into()),
            AST::Add(
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Value(Value::I64(1))),
            ),
        ]);
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_7() {
        let res: AST = parse("(/ 1 (- 1 (+ 1 (* 1 1))))").unwrap().into();
        let target: AST = AST::Div(
            Box::new(AST::Value(Value::I64(1))),
            Box::new(AST::Sub(
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::I64(1))),
                    Box::new(AST::Mult(
                        Box::new(AST::Value(Value::I64(1))),
                        Box::new(AST::Value(Value::I64(1))),
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
            vec![AST::Symbol("num".into())],
            Box::new(AST::Add(
                Box::new(AST::Value(Value::I64(1))),
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
                vec![AST::Symbol("num".into())],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
            AST::Let(
                "a".into(),
                Box::new(AST::Value(Value::I64(4))),
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::I64(1))),
                    Box::new(AST::Value(Value::I64(1))),
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
                vec![AST::Symbol("num".into())],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
            AST::Let(
                "a".into(),
                Box::new(AST::Value(Value::I64(4))),
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::I64(1))),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
        ]);
        assert_eq!(res, target);
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_12() {
        <Elem as Into<Toplevel>>::into(parse("(())").unwrap());
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_14() {
        let res = <Elem as Into<Toplevel>>::into(parse("(+ 1 1)").unwrap());
        println!("{:#?}", res);
    }

    #[test]
    fn test_from_15() {
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
                vec![AST::Symbol("num".into())],
                Box::new(AST::Add(
                    Box::new(AST::Symbol("num".into())),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
            AST::Call("add1".into(), vec![AST::Value(Value::I64(1))]),
        ]);
        assert_eq!(res, target);
    }
}
