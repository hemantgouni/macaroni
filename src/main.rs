mod parse;

use std::{io, fs};

fn main() -> io::Result<()> {
    // use ? here to get rid of the unused Result warning
    let contents = fs::read_to_string("input.txt").expect("No such file or directory!");
    println!("AST: {:?}\n", parse::list(contents.as_bytes()));

    Ok(())
}
