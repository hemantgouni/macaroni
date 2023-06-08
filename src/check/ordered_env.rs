use crate::check::{EVar, Monotype, Type, UVar};
use crate::data::Ident;

#[derive(Debug, PartialEq, Clone)]
pub enum OrderedEnvElem {
    UVar(UVar),
    TVar(Ident, Type),
    EVar(EVar),
    ESol(EVar, Monotype),
    Marker(EVar),
}

#[derive(Debug, Clone)]
pub struct OrderedEnv(Vec<OrderedEnvElem>);

impl OrderedEnv {
    pub fn new() -> Self {
        OrderedEnv(Vec::new())
    }

    pub fn add(&self, elem: OrderedEnvElem) -> Self {
        let mut self_clone = self.clone();
        self_clone.0.push(elem);
        self_clone
    }

    pub fn concat(&self, other_env: &Self) -> Self {
        let mut self_clone = self.clone();
        let mut other_clone = other_env.clone();
        self_clone.0.append(&mut other_clone.0);
        self_clone
    }

    pub fn contains(&self, elem: &OrderedEnvElem) -> bool {
        self.0.contains(elem)
    }

    // what's with the reference weirdness here
    pub fn contains_pred(&self, pred: impl Fn(&OrderedEnvElem) -> bool) -> bool {
        self.0.iter().find(|elem| pred(elem)).is_some()
    }

    pub fn split_on(&self, elem: &OrderedEnvElem) -> Option<(Self, OrderedEnvElem, Self)> {
        self.0
            .iter()
            .position(|elem_in_vec| elem_in_vec == elem)
            .map(|pos| {
                let split = self.0.split_at(pos);
                let env_left = OrderedEnv(split.0.to_vec());
                let env_right = OrderedEnv(split.1[1..].to_vec());

                (env_left, split.1[0].to_owned(), env_right)
            })
    }
}

#[cfg(test)]
mod test {}
