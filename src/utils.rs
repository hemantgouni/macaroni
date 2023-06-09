use std::sync::atomic::{AtomicUsize, Ordering};

pub trait VecUtils {
    type Elem;

    fn all_eq(&self) -> bool;
    fn append_immutable(&self, other: &Self) -> Self;
    fn push_immutable(&self, other: &Self::Elem) -> Self;
}

impl<A: PartialEq + Clone> VecUtils for Vec<A> {
    type Elem = A;

    fn all_eq(&self) -> bool {
        match self.as_slice() {
            [] => true,
            [head, rest @ ..] => rest.iter().all(|elem| elem == head),
        }
    }

    fn append_immutable(&self, other: &Self) -> Self {
        let mut self_clone = self.clone();
        let mut other_clone = other.clone();
        self_clone.append(&mut other_clone);
        self_clone.to_vec()
    }

    fn push_immutable(&self, elem: &Self::Elem) -> Self {
        let mut self_clone = self.clone();
        let elem_clone = elem.clone();
        self_clone.push(elem_clone);
        self_clone.to_vec()
    }
}

// it should be a syntax error to use variables of any kind that are just numbers
pub fn get_unique_id() -> String {
    static COUNTER: AtomicUsize = AtomicUsize::new(1);

    let mut num_string = COUNTER.fetch_add(1, Ordering::Relaxed).to_string();
    num_string.insert(0, '#');

    num_string
}
