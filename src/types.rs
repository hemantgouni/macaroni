#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Type {
    Int,
    Bool,
    String,
    List(Box<Type>),
    Func(Box<Type>, Box<Type>),
}


