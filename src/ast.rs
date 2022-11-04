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
            Elem::List(elems) => match &elems[..] {
                [Elem::Symbol("let"), Elem::Symbol(var), expr1, expr2] => AST::Let(
                    Ident(var.to_string()),
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
                _ => panic!(),
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
}
