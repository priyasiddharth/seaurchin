#![allow(unused)]

use verification_annotations as verifier;

#[test]
fn test_nopanic() {
    use std::cell::RefCell;

    let c = RefCell::new(5);

    let m = c.borrow_mut();
    // only one mut borrow; so no panic
}


#[test]
fn test_panic() {
    use std::cell::RefCell;

    let c = RefCell::new(5);

    let m = c.borrow_mut();
    let b = c.borrow(); // this causes a panic
    // panic leads to __VERIFIER_ERROR
}