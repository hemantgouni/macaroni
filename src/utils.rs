pub fn concat<A>(mut vec1: Vec<A>, mut vec2: Vec<A>) -> Vec<A> {
    vec1.append(&mut vec2);
    vec1
}
