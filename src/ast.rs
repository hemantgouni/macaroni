use crate::data::{Elem, Ident, Lit, Toplevel, AST};

fn quote_elem(elem: &Elem) -> Lit {
    // Hey, this is basically the lexed representation of the code!!!!
    match elem {
        Elem::String(str) => Lit::String(str.to_string()),
        Elem::Symbol(str) => Lit::Symbol(str.to_string()),
        Elem::List(elems) => Lit::List(elems.iter().map(|elem| quote_elem(elem)).collect()),
    }
}

// parses all non-toplevel expressions
impl Elem<'_> {
    pub fn parse(self) -> AST {
        match self {
            Elem::String(str) => AST::Lit(Lit::String(str.into())),
            Elem::Symbol(str) => str
                .to_string()
                .parse::<i64>()
                .map(|int| AST::Lit(Lit::I64(int)))
                .unwrap_or_else(|_| {
                    str.to_string()
                        .parse::<bool>()
                        .map(|bool| AST::Lit(Lit::Bool(bool)))
                        .unwrap_or_else(|_| AST::Ident(str.into()))
                }),
            Elem::List(elems) => match elems.as_slice() {
                [Elem::Symbol("list"), rest @ ..] => {
                    AST::List(rest.iter().map(|elem| elem.clone().parse()).collect())
                }
                [Elem::Symbol("cons"), elem, list] => AST::Cons(
                    Box::new(elem.clone().parse()),
                    Box::new(list.clone().parse()),
                ),
                [Elem::Symbol("car"), list] => AST::Car(Box::new(list.clone().parse())),
                [Elem::Symbol("cdr"), list] => AST::Cdr(Box::new(list.clone().parse())),
                [Elem::Symbol("empty?"), list] => AST::Emptyp(Box::new(list.clone().parse())),
                [Elem::Symbol("if"), cond_expr, then_expr, else_expr] => AST::Ite(
                    Box::new(cond_expr.clone().parse()),
                    Box::new(then_expr.clone().parse()),
                    Box::new(else_expr.clone().parse()),
                ),
                [Elem::Symbol("=="), expr1, expr2] => AST::Eq(
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol("<"), expr1, expr2] => AST::Lt(
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol(">"), expr1, expr2] => AST::Gt(
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol("&&"), expr1, expr2] => AST::And(
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol("||"), expr1, expr2] => AST::Or(
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol("quote"), rest] => AST::Quote(Box::new(AST::Lit(quote_elem(rest)))),
                [Elem::Symbol("let"), Elem::Symbol(ident), expr1, expr2] => AST::Let(
                    (*ident).into(),
                    Box::new(expr1.clone().parse()),
                    Box::new(expr2.clone().parse()),
                ),
                [Elem::Symbol("++"), str1, str2] => AST::Concat(
                    Box::new(str1.clone().parse()),
                    Box::new(str2.clone().parse()),
                ),
                [Elem::Symbol("+"), num1, num2] => AST::Add(
                    Box::new(num1.clone().parse()),
                    Box::new(num2.clone().parse()),
                ),
                [Elem::Symbol("-"), num1, num2] => AST::Sub(
                    Box::new(num1.clone().parse()),
                    Box::new(num2.clone().parse()),
                ),
                [Elem::Symbol("/"), num1, num2] => AST::Div(
                    Box::new(num1.clone().parse()),
                    Box::new(num2.clone().parse()),
                ),
                [Elem::Symbol("%"), num1, num2] => AST::Mod(
                    Box::new(num1.clone().parse()),
                    Box::new(num2.clone().parse()),
                ),
                [Elem::Symbol("*"), num1, num2] => AST::Mult(
                    Box::new(num1.clone().parse()),
                    Box::new(num2.clone().parse()),
                ),
                [Elem::Symbol(ident), rest @ ..] => AST::Call(
                    (*ident).into(),
                    rest.iter().map(|elem| elem.to_owned().parse()).collect(),
                ),
                other => panic!("Unable to abstractify: {:#?}", other),
            },
        }
    }

    // parses all expressions, plus top-level declarations
    pub fn parse_toplevel(self) -> Toplevel {
        match self {
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
                            Box::new(body.to_owned().parse()),
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
                            Box::new(body.to_owned().parse()),
                        ),
                    // defer to the AST impl to translate 'normal' exprs which
                    // could appear at the top level
                    _ => elem.to_owned().parse(),
                },
                _ => elem.to_owned().parse(),
            }).collect::<Vec<AST>>()),
            // The top level wasn't passed a list of top-level forms, error!
            _ => panic!("Parsing into toplevel form failed: {:#?}", self),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::parse::tokenize;

    #[test]
    fn test_from_1() {
        let res: AST = tokenize("(let a 4 (+ a 4))").unwrap().parse();
        let target: AST = AST::Let(
            "a".into(),
            Box::new(AST::Lit(Lit::I64(4))),
            Box::new(AST::Add(
                Box::new(AST::Ident("a".into())),
                Box::new(AST::Lit(Lit::I64(4))),
            )),
        );
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_2() {
        let res: AST = tokenize("(+ (+ 1 1) (+ 1 (+ 1 (+ 1 1))))").unwrap().parse();
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
        let res: AST = tokenize("(quote (a b c d e (+ 1 1)))").unwrap().parse();
        let target: AST = AST::Quote(Box::new(AST::Lit(Lit::List(vec![
            Lit::Symbol("a".into()),
            Lit::Symbol("b".into()),
            Lit::Symbol("c".into()),
            Lit::Symbol("d".into()),
            Lit::Symbol("e".into()),
            Lit::List(vec![
                Lit::Symbol("+".into()),
                Lit::Symbol("1".into()),
                Lit::Symbol("1".into()),
            ]),
        ]))));
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_7() {
        let res: AST = tokenize("(/ 1 (- 1 (+ 1 (* 1 1))))").unwrap().parse();
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
        let res: Toplevel = tokenize("((fn add1 (num) (+ 1 num)))")
            .unwrap()
            .parse_toplevel();
        let target: Toplevel = Toplevel(vec![AST::Func(
            "add1".into(),
            vec!["num".into()],
            Box::new(AST::Add(
                Box::new(AST::Lit(Lit::I64(1))),
                Box::new(AST::Ident("num".into())),
            )),
        )]);
        assert_eq!(res, target)
    }

    #[test]
    fn test_from_10() {
        let res: Toplevel = tokenize(
            "((fn add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .parse_toplevel();
        let target: Toplevel = Toplevel(vec![
            AST::Func(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Ident("num".into())),
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
        let res: Toplevel = tokenize(
            "((macro add1 (num)
               (+ num 1))
              (let a 4
               (+ 1 1)))",
        )
        .unwrap()
        .parse_toplevel();
        let target: Toplevel = Toplevel(vec![
            AST::Macro(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Ident("num".into())),
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
        tokenize("(())").unwrap().parse_toplevel();
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_14() {
        tokenize("(+ 1 1)").unwrap().parse_toplevel();
    }

    #[test]
    #[should_panic]
    #[allow(unused_must_use)]
    fn test_from_15() {
        tokenize(
            "((fn add1 (num) (+ 1 num))
                  (fn 1))",
        )
        .unwrap()
        .parse_toplevel();
    }

    #[test]
    fn test_from_16() {
        let res: Toplevel = tokenize(
            "
            ((fn add1 (num)
              (+ num 1))
             (add1 1))
        ",
        )
        .unwrap()
        .parse_toplevel();
        let target: Toplevel = Toplevel(vec![
            AST::Func(
                "add1".into(),
                vec!["num".into()],
                Box::new(AST::Add(
                    Box::new(AST::Ident("num".into())),
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
}
