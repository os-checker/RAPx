unsafe fn f1(p: *mut i32) {
    unsafe {
        *p = 1;
    }
}

unsafe fn foo(p: *mut i32) {
    unsafe {
        f1(p);
    }
}

fn main() {
    let mut value = 0i32;
    let ptr: *mut i32 = &mut value as *mut i32;

    unsafe {
        foo(ptr);
    }

    println!("value = {}", value);
}

