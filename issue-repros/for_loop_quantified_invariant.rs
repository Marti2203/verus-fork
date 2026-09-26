// Minimal reproduction: a `for` loop's quantified invariant whose trigger
// mentions the loop variable cannot be used inside the loop body.
// Run: verus --multiple-errors 20 for_loop_quantified_invariant.rs
// Found against verus-fork 5e83a13e2 (2026-09-24); see README.md here.
use vstd::prelude::*;
verus! {

spec fn p(k: int, j: u16) -> bool;

// The per-index fact the loops carry; each iteration establishes it for the next index.
#[verifier::external_body]
proof fn establish(j: u16)
    ensures forall|k: int| #[trigger] p(k, j),
{
}

// FAILS at `assert(p(3, i))`: the invariant is assumed, but its trigger never fires.
fn for_loop(n: u16) {
    proof { establish(0); }
    for i in 0..n
        invariant
            forall|k: int| #[trigger] p(k, i),
    {
        assert(p(3, i));
        proof { establish((i + 1) as u16); }
    }
}

// PASSES: the same invariant on a `while` loop.
fn while_loop(n: u16) {
    proof { establish(0); }
    let mut i: u16 = 0;
    while i < n
        invariant
            forall|k: int| #[trigger] p(k, i),
        decreases n - i,
    {
        assert(p(3, i));
        proof { establish((i + 1) as u16); }
        i = i + 1;
    }
}

// PASSES: workaround -- a ghost copy of the index, tied to it by a plain equation.
fn for_loop_ghost_copy(n: u16) {
    proof { establish(0); }
    let ghost mut c: u16 = 0;
    for i in 0..n
        invariant
            c == i,
            forall|k: int| #[trigger] p(k, c),
    {
        assert(p(3, i));
        proof {
            establish((i + 1) as u16);
            c = (c + 1) as u16;
        }
    }
}

fn main() {}
}
