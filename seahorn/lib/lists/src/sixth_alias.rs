// This is a file which is used to demonstrate undef behaviour

/* According to Rust doc
 * &mut T gets a `noalias` attr in LLVM IR. This means that all other ptr args which don't
 * have the same provenance cannot access this memory.
 * This example creates undef behaviour by using unsafe calls to create aliasing ptrs to the
 * same mem location. Both these ptrs have different provenances.
 */
#[cfg(test)]
mod test {
    use super::Node;
    use super::mutate_nodes;
    use std::ptr;

    #[test]
    pub fn noalias_rule() {
        let mut head = Box::new(Node { elem: 1, prev: ptr::null_mut() });
        let raw_head: *mut _ = Box::into_raw(head);
        let mut tail = Box::new(Node { elem: 2, prev: raw_head });
        let mut head_ref = unsafe { Box::from_raw(raw_head) };
        mutate_nodes(head_ref, &mut *tail);
    }
}

use std::ptr;

#[repr(C)]
pub struct Node {
    pub elem: i32,
    pub prev: *mut Node,
}

// This function takes two nodes where the tail node has a member 'prev' which points to the
pub fn mutate_nodes(mut head_node: Box<Node>, tail_node: &mut Node) -> Box<Node> {
    // NOTE: This generates noalias for head_node
    head_node.elem = 3;
    let p = tail_node.prev;
    unsafe { (*p).elem = 4; }
    if (head_node.elem == 3) {
        head_node.elem = 5;
    }
    head_node
}

pub fn mutate_nodes_ref(head_node: &mut Node, tail_node: &mut Node) {
    // TODO: Does this generate noalias for head_node?
    head_node.elem = 3;
    let p = tail_node.prev;
    unsafe { (*p).elem = 4; }
    if (head_node.elem == 3) {
        head_node.elem = 6;
    }
}

// Compiling with
// 1. rustc -C opt-level=2  --emit llvm-ir sixth_alias.rs VS
// 2. rustc  --emit llvm-ir sixth_alias.rs
// gives different results
fn main() {
    let mut head = Box::new(Node { elem: 1, prev: ptr::null_mut() });
    let raw_head: *mut _ = Box::into_raw(head);
    let mut tail = Box::new(Node { elem: 2, prev: raw_head });
    let mut head_node = unsafe { Box::from_raw(raw_head) };
    let mut ret_head = mutate_nodes(head_node, &mut *tail);
    assert_eq!(ret_head.elem, 4);

    mutate_nodes_ref(&mut *ret_head, &mut *tail);
    assert_eq!(ret_head.elem, 4);
}