use std::sync::atomic::{AtomicUsize, Ordering};

pub trait VecUtils {
    fn all_eq(&self) -> bool;
}

impl<A: PartialEq> VecUtils for Vec<A> {
    fn all_eq(&self) -> bool {
        match self.as_slice() {
            [] => true,
            [head, rest @ ..] => rest.iter().all(|elem| elem == head),
        }
    }
}

pub fn concat<A>(mut vec1: Vec<A>, mut vec2: Vec<A>) -> Vec<A> {
    vec1.append(&mut vec2);
    vec1
}

pub fn get_unique_id() -> String {
    static COUNTER: AtomicUsize = AtomicUsize::new(1);
    COUNTER.fetch_add(1, Ordering::Relaxed).to_string()
}
