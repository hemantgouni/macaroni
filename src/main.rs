#![allow(warnings, unused)]

use std::string::String;

use nom::branch::alt;
use nom::bytes::complete::{is_not, tag, take_while, take_while1};
use nom::character::complete::alpha1;
use nom::character::{is_alphanumeric, is_space};
use nom::error::{Error, ErrorKind};
use nom::multi::many1;
use nom::Err;
use nom::IResult;

#[derive(Debug, Eq, PartialEq)]
enum Elem {
    Symbol(String),
    List(Vec<Elem>),
}

fn tokenize(prog: String) -> Vec<String> {
    panic!();
}

fn paren_left(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag("(")(input)
}

fn paren_right(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag(")")(input)
}

fn bracket_left(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag("[")(input)
}

fn bracket_right(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag("]")(input)
}

// result error type holds &[u8]s because that's what the input in the result holds
fn symbol(input: &[u8]) -> IResult<&[u8], Elem> {
    let (input, elem) = alpha1(input)?;

    // get a String from the &[u8] we get from alpha1
    let result = String::from_utf8(elem.to_vec()).map_err(|_| {
        nom::Err::Error(Error {
            input,
            code: ErrorKind::TakeWhile1,
        })
    })?;

    let (input, _) = take_while(is_space)(input)?;

    Ok((input, Elem::Symbol(result)))
}

fn list(input: &[u8]) -> IResult<&[u8], Elem> {
    let (input, _) = take_while(is_space)(input)?;
    let (input, _) = paren_left(input)?;
    let (input, _) = take_while(is_space)(input)?;
    let (input, symbols) = many1(alt((symbol, list)))(input)?;
    let (input, _) = paren_right(input)?;
    let (input, _) = take_while(is_space)(input)?;

    Ok((input, Elem::List(symbols)))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_parens_1() {
        let res = symbol(b"abc de");
        assert_eq!(res, Ok(("de".as_bytes(), Elem::Symbol("abc".to_string()))));
    }

    #[test]
    fn test_list_1() {
        let res = list(b"(a)");
        assert_eq!(
            res,
            Ok((
                "".as_bytes(),
                Elem::List(vec![Elem::Symbol("a".to_string())])
            ))
        )
    }

    #[test]
    fn test_list_2() {
        let res = list(b"(a b)");
        assert_eq!(
            res,
            Ok((
                "".as_bytes(),
                Elem::List(
                    vec!["a", "b"]
                        .iter()
                        .map(|str| Elem::Symbol(str.to_string()))
                        .collect()
                )
            ))
        )
    }

    #[test]
    fn test_list_3() {
        let res = list(b"(a b (a b c d e))");
        let mut vec1: Vec<Elem> = vec!["a", "b"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        let mut vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_4() {
        let res = list(b" (a b (a b c d e))");
        let mut vec1: Vec<Elem> = vec!["a", "b"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        let mut vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }

    #[test]
    fn test_list_5() {
        let res = list(b"(a b (a b c d e)) ");
        let mut vec1: Vec<Elem> = vec!["a", "b"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        let mut vec2: Vec<Elem> = vec!["a", "b", "c", "d", "e"]
            .iter()
            .map(|str| Elem::Symbol(str.to_string()))
            .collect();
        vec1.push(Elem::List(vec2));
        assert_eq!(res, Ok(("".as_bytes(), Elem::List(vec1))))
    }
}

fn main() {}
