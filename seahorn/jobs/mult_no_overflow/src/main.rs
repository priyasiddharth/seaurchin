extern crate verification_annotations as verifier;

fn main() {
    let a : u32 = verifier::AbstractValue::abstract_value();
    let b : u32 = verifier::AbstractValue::abstract_value();
    verifier::assume(4 <= a && a <= 7);
    verifier::assume(5 <= b && b <= 8);

    let r = a*b;
    assert!(20 <= r && r <= 56);

}

