use std::sync::atomic::{AtomicUsize, Ordering};

pub fn concat<A>(mut vec1: Vec<A>, mut vec2: Vec<A>) -> Vec<A> {
    vec1.append(&mut vec2);
    vec1
}

pub fn vec_all_eq<A: PartialEq + Clone>(vec: Vec<A>) -> (bool, Option<A>) {
    match vec.as_slice() {
        [] => (true, None),
        [head, tail @ ..] => (
            tail.iter().all(|elem: &A| elem == head),
            Some(head.to_owned()),
        ),
    }
}

pub fn get_unique_id() -> String {
    static COUNTER: AtomicUsize = AtomicUsize::new(1);
    COUNTER.fetch_add(1, Ordering::Relaxed).to_string()
}
