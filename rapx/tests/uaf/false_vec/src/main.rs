fn no_alias_here(s: &str, v: &Vec<usize>) {
    let mut new_v = vec![];
    for element in v {
        new_v.push(element);
    }
    print!("{s} and {new_v:?}");
}

pub fn main() {
    let hello = "hello";
    let some_vec = vec![1, 2, 3];
    no_alias_here(hello, &some_vec);
    let hello = "hello".to_owned();
    let world = "world".to_owned();
    let hello_world = format!("{} {}", hello, world);
    print!("{hello_world}");
}
