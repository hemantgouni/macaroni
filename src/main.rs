mod parse;
mod ast;
mod data;

use std::{fs, io};

use crate::data::AST;

fn main() -> io::Result<()> {
    let contents = fs::read_to_string("input.txt").expect("No such file or directory!");
    let ast: AST = parse::parse(&contents).unwrap().into();
    println!("AST: {:?}\n", ast);
    Ok(())
}
