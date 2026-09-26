// Inside a recursive group, an `exists` whose trigger is a call to a function
// of the SAME group never gives up its witness: the definition's body refers
// to the fuel-indexed copy, so the plain call cannot match. A marker function
// outside the group works. No diagnostic points at the trigger.
use vstd::prelude::*;

verus! {

spec fn even(n: nat) -> bool
    decreases n, 1int,
{
    n == 0 || (n >= 2 && exists|m: nat| m + 2 == n && #[trigger] odd_or_even(m, n))
}

spec fn odd_or_even(m: nat, n: nat) -> bool
    decreases n, 0int,
{
    m < n && even(m)
}

proof fn witness_lost(n: nat)
    requires n >= 2, even(n), n != 0,
{
    // the witness should be n - 2, but the exists does not fire
    let m = choose|m: nat| m + 2 == n && #[trigger] odd_or_even(m, n);
    assert(even(m));  // fails
}

// The same definition with the trigger on a marker function that is NOT in
// the recursive group: the witness is recovered.
spec fn mark(m: nat) -> bool { true }

spec fn even2(n: nat) -> bool
    decreases n, 1int,
{
    n == 0 || (n >= 2 && exists|m: nat| #[trigger] mark(m) && m + 2 == n && odd_or_even2(m, n))
}

spec fn odd_or_even2(m: nat, n: nat) -> bool
    decreases n, 0int,
{
    m < n && even2(m)
}

proof fn witness_kept(n: nat)
    requires n >= 2, even2(n), n != 0,
{
    let m = choose|m: nat| #[trigger] mark(m) && m + 2 == n && odd_or_even2(m, n);
    assert(even2(m));  // verifies
}

fn main() {}

} // verus!
