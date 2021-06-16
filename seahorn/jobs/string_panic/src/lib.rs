#![allow(unused)]

use verification_annotations as verifier;

#[test]
fn test_string_from_bytes_panic() {
    let b1: u8 = verifier::AbstractValue::abstract_value();
    let b2: u8 = verifier::AbstractValue::abstract_value();
    let bytes = vec![b1, b2];
    let val = std::string::String::from_utf8(bytes).unwrap();
}

#[test]
fn test_string_from_bytes_nopanic() {
    let b1: u8 = verifier::AbstractValue::abstract_value();
    let b2: u8 = verifier::AbstractValue::abstract_value();
    let bytes = vec![b1, b2];
    // assume that the bytes are valid UTF8
    verifier::assume(std::str::from_utf8(&bytes).is_err() == false);
    let val = std::string::String::from_utf8(bytes).unwrap();
}
