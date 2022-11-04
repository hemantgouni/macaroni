use crate::data::{Elem, Ident, Value, AST};

impl From<Elem<'_>> for AST {
    fn from(elem: Elem) -> AST {
        match elem {
            Elem::String(str) => AST::Value(Value::String(str.to_string())),
            Elem::Symbol(str) => str
                .to_string()
                .parse::<i64>()
                .and_then(|int| Ok(AST::Value(Value::I64(int))))
                .unwrap_or(AST::Value(Value::Symbol(str.to_string()))),
            Elem::List(elems) => match elems.as_slice() {
                [Elem::Symbol("fn"), Elem::Symbol(ident), Elem::List(args), body] => AST::Func(
                    Ident(ident.to_string()),
                    args.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                    Box::new(body.to_owned().into()),
                ),
                [Elem::Symbol("macro"), Elem::Symbol(ident), Elem::List(args), body] => AST::Macro(
                    Ident(ident.to_string()),
                    args.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                    Box::new(body.to_owned().into()),
                ),
                [Elem::Symbol("quote"), rest @ ..] => AST::Quote(
                    rest.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                ),
                [Elem::Symbol("unquote"), rest @ ..] => AST::Unquote(Vec::from(
                    rest.iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                )),
                [Elem::Symbol("let"), Elem::Symbol(ident), expr1, expr2] => AST::Let(
                    Ident(ident.to_string()),
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
                toplevel => AST::Toplevel(
                    toplevel
                        .iter()
                        .map(|elem| elem.to_owned().into())
                        .collect::<Vec<AST>>(),
                ),
            },
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
            Ident("a".to_string()),
            Box::new(AST::Value(Value::I64(4))),
            Box::new(AST::Add(
                Box::new(AST::Value(Value::Symbol("a".to_string()))),
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
            AST::Value(Value::Symbol("a".into())),
            AST::Value(Value::Symbol("b".into())),
            AST::Value(Value::Symbol("c".into())),
            AST::Value(Value::Symbol("d".into())),
            AST::Value(Value::Symbol("e".into())),
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
            AST::Value(Value::Symbol("a".into())),
            AST::Value(Value::Symbol("b".into())),
            AST::Value(Value::Symbol("c".into())),
            AST::Value(Value::Symbol("d".into())),
            AST::Value(Value::Symbol("e".into())),
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
        let res: AST = parse("(fn add1 (num) (+ 1 num))").unwrap().into();
        let target: AST = AST::Func(
            Ident("add1".into()),
            vec![AST::Value(Value::Symbol("num".into()))],
            Box::new(AST::Add(
                Box::new(AST::Value(Value::I64(1))),
                Box::new(AST::Value(Value::Symbol("num".into()))),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_10() {
        let res: AST = parse(
            "((fn add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .into();
        let target: AST = AST::Toplevel(vec![
            AST::Func(
                Ident("add1".into()),
                vec![AST::Value(Value::Symbol("num".into()))],
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::Symbol("num".into()))),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
            AST::Let(
                Ident("a".into()),
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
        let res: AST = parse(
            "((macro add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .into();
        let target: AST = AST::Toplevel(vec![
            AST::Macro(
                Ident("add1".into()),
                vec![AST::Value(Value::Symbol("num".into()))],
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::Symbol("num".into()))),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
            AST::Let(
                Ident("a".into()),
                Box::new(AST::Value(Value::I64(4))),
                Box::new(AST::Add(
                    Box::new(AST::Value(Value::I64(1))),
                    Box::new(AST::Value(Value::I64(1))),
                )),
            ),
        ]);
        assert_eq!(res, target);
    }
}
