static mut COUNTER: i32 = 0;

fn foo() {
    let c = unsafe { COUNTER };
    println!("COUNTER = {}", c);
}

fn main() {
    unsafe {
        COUNTER += 1;
    }
    foo();
}
