mod ast;
mod data;
mod evaluate;
mod expand;
mod fold;
mod parse;
mod utils;

use std::{env, fs};

use crate::data::Toplevel;

// type checker combinators??
//
// we have parser combinators which are a bunch of functions that make it easier to write parsers,
// what about the same thing for type checkers?

fn main() {
    let args: Vec<String> = env::args().collect();

    let contents = fs::read_to_string(args.get(1).unwrap_or(&String::from("input.mcr")))
        .expect("No such file or directory!");

    let ast: Toplevel = parse::tokenize(&contents).unwrap().parse_toplevel();
    println!("AST: {:#?}", ast);

    let expanded_ast: Toplevel = expand::expand(ast).unwrap();
    println!("AST (Expanded): {:#?}", expanded_ast);

    let res = evaluate::evaluate(expanded_ast);
    println!("Result: {:#?}", res);
}
