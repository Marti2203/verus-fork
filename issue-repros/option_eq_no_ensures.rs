// `<Option<T> as PartialEq>::eq` carries no postcondition when `T` is not a
// type Verus compares structurally (a user struct with a derived
// `PartialEq`, or a generic `T`). Branching on `a == b` then tells the
// verifier nothing, although the derived impl is plainly structural.
// Payload types Verus handles natively (`u64`, ...) are fine.
use vstd::prelude::*;

verus! {

#[derive(PartialEq, Eq)]
struct P {
    x: u64,
}

fn custom_payload(a: Option<P>, b: Option<P>) {
    if a == b {
        assert(a == b);  // assertion failed
    }
}

fn generic_payload<T: PartialEq>(a: Option<T>, b: Option<T>) {
    if a == b {
        assert(a == b);  // assertion failed
    }
}

fn native_payload(a: Option<u64>, b: Option<u64>) {
    if a == b {
        assert(a == b);  // verifies
    }
}

fn main() {}

} // verus!
