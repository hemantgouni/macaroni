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
