extern crate verification_annotations as verifier;
extern crate lists as lists;

use lists::fifth::List as List;
use lists::fifth::Node as Node;
use lists::fifth::Link as Link;


/* This function creates a partially initialized linked list of the following form
 *   HEAD -> first -> nd_voidp()  ...  nd_voidp() <- TAIL
 */
fn create_nd_list() -> List<i32> {
    let raw_ptr: *mut Node<i32> = unsafe { verifier::nd_voidp() } as *mut Node<i32>;
    let nd_node: Box<Node<i32>> = unsafe { Box::from_raw(raw_ptr) };

    let first = Box::new(Node {
        elem: 1,
        next: Some(nd_node),
    });
    let nd_tail: *mut Node<i32> = unsafe { verifier::nd_voidp() } as *mut Node<i32>;
    let list: List<i32> = List::new_with_head_and_tail(first, nd_tail);
    list
}

#[test]
/* This verification job tests that we can peek and pop the first element (after head)
 * successfully.
 */
fn test_bigpop1() {
    let mut list: List<i32> = create_nd_list();
    let head_ref: *mut Node<i32> = list.head.as_deref_mut().unwrap();
    unsafe { verifier::assert!(verifier::ptr_is_dereferenceable(head_ref)); }
    verifier::assert_eq!(list.peek(), Some(&1));
    verifier::assert_eq!(list.pop(), Some(1));
}

#[test]
/* This verification job tests that
 *  1. we can peek and pop the first element (after head) successfully.
 *  2. The head after this operation is an invalid element which cannot be de-referenced (SAT)
 */
fn test_bigpop2_sat() {
    let mut list: List<i32> = create_nd_list();
    let head_ref: *mut Node<i32> = list.head.as_deref_mut().unwrap();
    unsafe { verifier::assert!(verifier::ptr_is_dereferenceable(head_ref)); }
    verifier::assert_eq!(list.peek(), Some(&1));
    verifier::assert_eq!(list.pop(), Some(1));
    // TODO: Does Rust do its own is_deref check during this conversion?
    let head_ref: *mut Node<i32> = list.head.as_deref_mut().unwrap();
    unsafe { verifier::assert!(verifier::ptr_is_dereferenceable(head_ref)); }
}

#[test]
/* This verification job tests simple push, pop and peek operations */
fn test_smallpop() {
    let mut list: List<i32> = List::new();
    // Check empty list behaves right
    verifier::assert_eq!(list.pop(), None);
    list.push(1);
    verifier::assert_eq!(list.peek(), Some(&0));
    verifier::assert_eq!(list.pop(), Some(1));
}

fn main() {}