mod ast;
mod data;
mod evaluate;
mod parse;

use std::{env, fs, io};

use crate::data::Toplevel;

// type checker combinators??
//
// we have parser combinators which are a bunch of functions that make it easier to write parsers,
// what about the same thing for type checkers?

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();

    let contents = fs::read_to_string(args.get(1).unwrap_or(&String::from("input.txt")))
        .expect("No such file or directory!");

    let ast: Toplevel = parse::parse(&contents).unwrap().into();
    println!("AST: {:#?}", ast);

    let res = evaluate::evaluate(ast.clone());
    println!("Result: {:#?}", res);

    Ok(())
}
