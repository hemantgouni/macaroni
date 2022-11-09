use std::str::from_utf8;

use nom::branch::alt;
use nom::bytes::complete::{tag, take_while, take_while1};
use nom::character::is_newline;
use nom::character::is_space;
use nom::error::{Error, ErrorKind};
use nom::multi::many0;
use nom::IResult;

use crate::data::Elem;

fn paren_left(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag("(")(input)
}

fn paren_right(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag(")")(input)
}

fn skip_char(char: u8) -> bool {
    is_space(char) || is_newline(char)
}

fn symbol_char(char: u8) -> bool {
    !is_space(char) && char != b')' && char != b'(' && !is_newline(char)
}

fn string_char(char: u8) -> bool {
    char != b'"'
}

fn string(input: &[u8]) -> IResult<&[u8], Elem> {
    let (input, _) = tag("\"")(input)?;
    let (input, elem) = take_while1(string_char)(input)?;
    let (input, _) = tag("\"")(input)?;
    let (input, _) = take_while(skip_char)(input)?;

    let result = from_utf8(elem).map_err(|_| {
        nom::Err::Error(Error {
            input,
            code: ErrorKind::TakeWhile1,
        })
    })?;

    Ok((input, Elem::String(result)))
}

// result error type holds &[u8]s because that's what the input in the result holds
fn symbol(input: &[u8]) -> IResult<&[u8], Elem> {
    let (input, elem) = take_while1(symbol_char)(input)?;
    let (input, _) = take_while(skip_char)(input)?;

    // get an &str from the &[u8] we get from alpha1
    let result = from_utf8(elem).map_err(|_| {
        nom::Err::Error(Error {
            input,
            code: ErrorKind::TakeWhile1,
        })
    })?;

    Ok((input, Elem::Symbol(result)))
}

fn list(input: &[u8]) -> IResult<&[u8], Elem> {
    let (input, _) = take_while(skip_char)(input)?;
    let (input, _) = paren_left(input)?;
    let (input, _) = take_while(skip_char)(input)?;
    let (input, symbols) = many0(alt((string, symbol, list)))(input)?;
    let (input, _) = paren_right(input)?;
    let (input, _) = take_while(skip_char)(input)?;
    Ok((input, Elem::List(symbols)))
}

pub fn parse(input: &str) -> Result<Elem, String> {
    list(input.as_bytes())
        .map(|(_, elem)| elem)
        .map_err(|err| match err {
            nom::Err::Error(Error { input, code: _ }) => std::str::from_utf8(input)
                .map(|str| str.to_string())
                .unwrap_or_else(|_| format!("{:?}", input)),
            _ => err.to_string(),
        })
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parens_1() {
        let res = symbol(b"abc de");
        assert_eq!(res, Ok(("de".as_bytes(), Elem::Symbol("abc"))));
    }

    #[test]
    fn test_list_1() {
        let res = list(b"(a)");
        assert_eq!(
            res,
            Ok(("".as_bytes(), Elem::List(vec![Elem::Symbol("a")])))
        )
    }

    #[test]
    fn test_list_2() {
        let res = list(b"(a b)");
        assert_eq!(
            res,
            Ok((
                "".as_bytes(),
                Elem::List(vec!["a", "b"].iter().map(|str| Elem::Symbol(str)).collect())
            ))
        )
    }

    #[test]
    fn test_list_3() {
        let res = list(b"(a b (a b c d e))");
        let mut vec1: Vec<Elem> = vec!["a", "b"].iter().map(|str| Elem::Symbol(str)).collect();
        let vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_4() {
        let res = list(b" (a b (a b c d e))");
        let mut vec1: Vec<Elem> = vec!["a", "b"].iter().map(|str| Elem::Symbol(str)).collect();
        let vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_5() {
        let res = list(b"(a b (a b c d e)) ");
        let mut vec1: Vec<Elem> = vec!["a", "b"].iter().map(|str| Elem::Symbol(str)).collect();
        let vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_7() {
        let res = list(b"                                   (   a   b     (    a b c d e) ) ");
        let mut vec1: Vec<Elem> = vec!["a", "b"].iter().map(|str| Elem::Symbol(str)).collect();
        let vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_8() {
        let res = list(
            b"
            (fn hello-world
             (println Hello world))",
        );
        let target: Result<(&[u8], Elem), nom::Err<Error<&[u8]>>> = Ok((
            &[],
            Elem::List(vec![
                Elem::Symbol("fn"),
                Elem::Symbol("hello-world"),
                Elem::List(vec![
                    Elem::Symbol("println"),
                    Elem::Symbol("Hello"),
                    Elem::Symbol("world"),
                ]),
            ]),
        ));
        assert_eq!(res, target)
    }

    #[test]
    fn test_list_10() {
        let res = list(
            b"
            (fn hello-world
             (println \"hey, world!\"))",
        );
        let target: Result<(&[u8], Elem), nom::Err<Error<&[u8]>>> = Ok((
            &[],
            Elem::List(vec![
                Elem::Symbol("fn"),
                Elem::Symbol("hello-world"),
                Elem::List(vec![Elem::Symbol("println"), Elem::String("hey, world!")]),
            ]),
        ));
        assert_eq!(res, target)
    }

    #[test]
    fn test_list_11() {
        let res = list(
            b"
            (fn hello-world
             (println! \"hey, world!\"))",
        );
        let target: Result<(&[u8], Elem), nom::Err<Error<&[u8]>>> = Ok((
            &[],
            Elem::List(vec![
                Elem::Symbol("fn"),
                Elem::Symbol("hello-world"),
                Elem::List(vec![Elem::Symbol("println!"), Elem::String("hey, world!")]),
            ]),
        ));
        assert_eq!(res, target)
    }

    #[test]
    fn test_list_12() {
        let res = list(br#"((++ "hey " "there"))"#);
        let target: Result<(&[u8], Elem), nom::Err<Error<&[u8]>>> = Ok((
            &[],
            Elem::List(vec![Elem::List(vec![
                Elem::Symbol("++"),
                Elem::String("hey "),
                Elem::String("there"),
            ])]),
        ));

        assert_eq!(res, target);
    }
}
