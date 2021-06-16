#![allow(unused)]

use verification_annotations as verifier;

use std::cell;
use std::cell::RefCell;

#[test]
fn test_nopanic() {
    let c = RefCell::new(5);

    let m = c.borrow_mut();
    // only one mut borrow; so no panic
}

#[test]
fn test_panic() {
    let c = RefCell::new(5);

    let m = c.borrow_mut();
    let b = c.borrow(); // this causes a panic
                        // panic leads to __VERIFIER_ERROR
}

/*
 * Non deterministic RefCell tests
 *
 * Naming convention for functions:
 *   mb - mutable borrow
 *   b - borrow
 */

#[test]
fn test_mb_nopanic() {
    let val: u32 = verifier::AbstractValue::abstract_value();
    let nd_flag_val: isize = verifier::AbstractValue::abstract_where(|x| cell::is_unused(*x));
    let c = RefCell::new_with_flag(val, nd_flag_val);
    let m = c.borrow_mut();
}

#[test]
fn test_mb_nopanic2() {
    let val: u32 = verifier::AbstractValue::abstract_value();
    let c = RefCell::new(val);
    let nd_borrow_flag: isize = verifier::AbstractValue::abstract_where(|x| cell::is_unused(*x));
    c.set_borrow_state(nd_borrow_flag);
    let m = c.borrow_mut();
}

#[test]
fn test_b_nopanic() {
    let val: u32 = verifier::AbstractValue::abstract_value();
    let c = RefCell::new(val);
    let nd_borrow_flag: isize = verifier::AbstractValue::abstract_where(|x| {
        cell::is_unused(*x) || (cell::is_reading(*x) && !cell::is_reader_limit_reached(*x))
    });
    c.set_borrow_state(nd_borrow_flag);
    let m = c.borrow();
}

#[test]
// Here we test that if the number of borrows has reached max limit for datatype then adding one
// more borrow rolls over to negative value and we go into mutably borrowed state. This disallows
// one more borrow.
fn test_b_to_mb_rollover_panic_sat() {
    let val: u32 = verifier::AbstractValue::abstract_value();
    let c = RefCell::new(val);
    let nd_borrow_flag: isize =
        verifier::AbstractValue::abstract_where(|x| cell::is_unused(*x) || cell::is_reading(*x));
    c.set_borrow_state(nd_borrow_flag);
    let m = c.borrow();
}

#[test]
// When the lifetime for a mutable borrow ends, we should go back to UNUSED state
fn test_lifetime_end_removes_mb() {
    let val: u32 = verifier::AbstractValue::abstract_value();
    let a = RefCell::new(val);
    let cond: bool = verifier::AbstractValue::abstract_value();
    if cond {
        let m = a.borrow_mut();
    }
    verifier::assert_eq!(a.get_borrow_state(), cell::State::UNUSED);
}
