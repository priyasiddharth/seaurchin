// Copyright 2021 The Propverify authors
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/////////////////////////////////////////////////////////////////
// FFI wrapper for SeaHorn symbolic execution tool
/////////////////////////////////////////////////////////////////

use std::default::Default;
use std::convert::TryInto;

pub use crate::traits::*;

use std::os::raw::{c_char};
use core::mem;

extern {
    fn __VERIFIER_error() -> !;
    fn __VERIFIER_assume(pred: i32);
    // TODO: How to add attribute __malloc__
    // TODO: wrap in a rust fn
    pub fn nd_voidp() -> *mut u8;
    // TODO: Make printf placeholder work
    pub fn sea_printf(format: *const c_char, ...);
    fn sea_is_dereferenceable(ptr: *mut u8, offset: usize) -> bool;
}

#[no_mangle]
fn spanic() -> ! {
    abort();
}


pub unsafe fn ptr_is_dereferenceable<T>(ptr: *mut T) -> bool {
    sea_is_dereferenceable(ptr.cast(), mem::size_of::<T>())
}

/// Reject the current execution with a verification failure.
///
/// In almost all circumstances, `report_error` should
/// be used instead because it generates an error message.
pub fn abort() -> ! {
    unsafe { __VERIFIER_error(); }
}

/// Assume that condition `cond` is true
///
/// Any paths found must satisfy this assumption.
pub fn assume(pred: bool) {
    if !pred {
        unsafe { __VERIFIER_assume(pred as i32); }
    }
}

/// Reject the current execution path with a verification success.
/// This is equivalent to `assume(false)`
/// and the opposite of `report_error(...)`.
///
/// Typical usage is in generating symbolic values when the value
/// does not meet some criteria.
pub fn reject() -> ! {
    assume(false);
    panic!("Unreachable, should have been rejected!");
}

macro_rules! make_nondet {
    ($typ:ty, $ext:ident, $v:expr) => {
        extern { fn $ext() -> $typ; }
        impl VerifierNonDet for $typ {
            fn verifier_nondet(self) -> Self {
                unsafe { $ext() }
            }
        }
    };
}

make_nondet!(u8, __VERIFIER_nondet_u8, 0);
make_nondet!(u16, __VERIFIER_nondet_u16, 0);
make_nondet!(u32, __VERIFIER_nondet_u32, 0);
make_nondet!(u64, __VERIFIER_nondet_u64, 0);
make_nondet!(usize, __VERIFIER_nondet_usize, 0);

make_nondet!(i8, __VERIFIER_nondet_i8, 0);
make_nondet!(i16, __VERIFIER_nondet_i16, 0);
make_nondet!(i32, __VERIFIER_nondet_i32, 0);
make_nondet!(i64, __VERIFIER_nondet_i64, 0);
make_nondet!(isize, __VERIFIER_nondet_isize, 0);

make_nondet!(f32, __VERIFIER_nondet_f32, 0.0);
make_nondet!(f64, __VERIFIER_nondet_f64, 0.0);

macro_rules! make_nondet_ne_bytes {
    ($typ:ty) => {
        impl VerifierNonDet for $typ {
            fn verifier_nondet(self) -> Self {
                let mut bytes = vec![0u8; std::mem::size_of::<$typ>()];
                for i in 0..bytes.len() {
                    unsafe { bytes[i] = __VERIFIER_nondet_u8(); }
                }
                Self::from_ne_bytes(bytes[..].try_into().unwrap())
            }
        }
    };
}

make_nondet_ne_bytes!(u128);
make_nondet_ne_bytes!(i128);


impl VerifierNonDet for bool {
    fn verifier_nondet(self) -> Self {
        let c = u8::verifier_nondet(0u8);
        assume(c == 0 || c == 1);
        c == 1
    }
}

impl<T: VerifierNonDet + Default> AbstractValue for T {
    fn abstract_value() -> Self {
        Self::verifier_nondet(Self::default())
    }
}

impl<T: VerifierNonDet + Default> Symbolic for T {
    fn symbolic(_desc: &'static str) -> Self {
        Self::verifier_nondet(Self::default())
    }
}

#[macro_export]
macro_rules! assert {
    ($cond:expr,) => { $crate::assert!($cond) };
    ($cond:expr) => { $crate::assert!($cond, "assertion failed: {}", stringify!($cond)) };
    ($cond:expr, $($arg:tt)+) => {{
        if ! $cond {
            $crate::abort();
        }
    }}
}

#[macro_export]
macro_rules! assert_eq {
    ($left:expr, $right:expr) => {{
        let left = $left;
        let right = $right;
        $crate::assert!(
            left == right,
            "assertion failed: `(left == right)` \
             \n  left: `{:?}`,\n right: `{:?}`",
            left,
            right)
    }};
    ($left:expr, $right:expr, $fmt:tt $($arg:tt)*) => {{
        let left = $left;
        let right = $right;
        $crate::assert!(
            left == right,
            concat!(
                "assertion failed: `(left == right)` \
                 \n  left: `{:?}`, \n right: `{:?}`: ", $fmt),
            left, right $($arg)*);
    }};
}

#[macro_export]
macro_rules! assert_ne {
    ($left:expr, $right:expr) => {{
        let left = $left;
        let right = $right;
        $crate::assert!(
            left != right,
            "assertion failed: `(left != right)` \
             \n  left: `{:?}`,\n right: `{:?}`",
            left,
            right)
    }};
    ($left:expr, $right:expr, $fmt:tt $($arg:tt)*) => {{
        let left = $left;
        let right = $right;
        $crate::assert!(
            left != right,
            concat!(
                "assertion failed: `(left != right)` \
                 \n  left: `{:?}`, \n right: `{:?}`: ", $fmt),
            left, right $($arg)*);
    }};
}

/////////////////////////////////////////////////////////////////
// End
/////////////////////////////////////////////////////////////////
