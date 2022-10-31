use std::io;
use std::str::from_utf8;

use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::alpha1;
use nom::character::is_space;
use nom::error::{Error, ErrorKind};
use nom::multi::many1;
use nom::IResult;

#[derive(Debug, Eq, PartialEq)]
enum Elem<'a> {
    Symbol(&'a str),
    List(Vec<Elem<'a>>),
}

fn paren_left(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag("(")(input)
}

fn paren_right(input: &[u8]) -> IResult<&[u8], &[u8]> {
    tag(")")(input)
}

// result error type holds &[u8]s because that's what the input in the result holds
fn symbol<'a>(input: &'a [u8]) -> IResult<&'a [u8], Elem<'a>> {
    let (input, elem) = alpha1(input)?;

    // get an &str from the &[u8] we get from alpha1
    let result = from_utf8(elem).map_err(|_| {
        nom::Err::Error(Error {
            input,
            code: ErrorKind::TakeWhile1,
        })
    })?;

    let (input, _) = take_while(is_space)(input)?;

    Ok((input, Elem::Symbol(&result)))
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

fn main() -> io::Result<()> {
    let mut buffer = String::new();
    // use ? here to get rid of the unused Result warning
    io::stdin().read_line(&mut buffer)?;
    println!("AST: {:?}\n", list(buffer.as_bytes()));

    Ok(())
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
}
