#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Investigation for the PR #2741 discussion with @parno: why can't a
// generic Pattern spec for `FnMut(char) -> bool` give the same negative
// ("didn't match") guarantee as the hand-written str_starts_with_pred?
//
// Root cause, confirmed by reading vir/src/ast_simplify.rs (the closure's
// `ensures` axiom generation): a closure's `.ensures((args,), ret)` is only
// ever axiomatized as
//     forall args, ret: closure_ens(f, args, ret) ==> <declared formula>(args, ret)
// (see `mk_implies(closure_ens_call, enss_body)` there) - ONE direction
// only. There is no axiom going the other way. So you can use a *known*
// closure_ens fact to learn the declared formula, but you can never
// establish that closure_ens holds for some `ret` except by way of an
// actual traced call (which assumes closure_ens for the concrete return
// value that call produced). Nothing here depends on whether the closure
// is generic or concrete.

test_verify_one_file_with_options! {
    // Modus tollens on a SINGLE (args, ret) instantiation works fine, with
    // no call at all - this is the existing, documented pattern (see
    // exec_closures.rs's own `assert(!f.ensures((2,),3))`). It works because
    // the declared formula at that ret is independently, statically known
    // to be false, so the one-directional axiom's contrapositive applies.
    #[test] single_instantiation_negative_works_without_a_call ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test() {
            let f = |y: u64| -> (z: u64)
                requires y == 2
                ensures z == 2
            {
                y
            };
            // No call to f has happened yet.
            assert(!f.ensures((2,), 3));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // But nothing bridges DIFFERENT instantiations of `ensures` to each
    // other. Knowing ensures fails for one candidate return value tells you
    // nothing about whether it holds for a different one - "totality"
    // (some return value is ensures-allowed) is never free.
    #[test] totality_across_instantiations_is_not_free ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test<F: Fn(char) -> bool>(pred: F, c: char)
            requires pred.requires((c,)),
        {
            assert(exists|r: bool| pred.ensures((c,), r)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // Same failure for a fully CONCRETE closure - genericity isn't the
    // cause. The declared contract is completely known here, and it still
    // fails, because the axiom never lets you go from "the declared
    // formula holds for r" to "closure_ens holds for r" - only the reverse.
    #[test] totality_fails_even_for_a_concrete_closure ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test(c: char) {
            let pred = |x: char| -> (r: bool)
                ensures r == (x == 'h'),
                { x == 'h' };
            assert(pred.requires((c,)));
            assert(exists|r: bool| pred.ensures((c,), r)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    // A real, traced call is what actually establishes closure_ens for a
    // concrete return value - and from there, both directions become
    // available for that one value, because it's now a known-true fact
    // instead of something we're trying to derive from nothing.
    #[test] a_real_call_establishes_totality_for_that_one_result ["vstd"] => verus_code! {
        use vstd::prelude::*;

        fn test(c: char) {
            let pred = |x: char| -> (r: bool)
                ensures r == (x == 'h'),
                { x == 'h' };
            let actual = pred(c); // <- the real call Verus actually sees
            assert(exists|r: bool| pred.ensures((c,), r)); // now trivial: r = actual
            assert(pred.ensures((c,), actual));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    // The practical consequence, mirroring str_starts_with_pred's own
    // postcondition, but going through a real() function whose body is
    // marked external_body (standing in for `str::starts_with`'s own
    // external, unverified implementation). The "matched" direction is
    // recoverable from the external function's assumed ensures clause; the
    // "didn't match" direction is not, for exactly the reason above.
    #[test] external_body_pattern_call_only_recovers_one_direction ["vstd"] => verus_code! {
        use vstd::prelude::*;

        #[verifier::external_body]
        fn opaque_first_char_check<F: Fn(char) -> bool>(c: char, pred: F) -> (res: bool)
            requires pred.requires((c,)),
            ensures res ==> pred.ensures((c,), true),
        {
            pred(c)
        }

        fn test(c: char) {
            let pred = |x: char| -> (r: bool)
                ensures r == (x == 'h'),
                { x == 'h' };
            let res = opaque_first_char_check(c, pred);
            assert(res ==> c == 'h'); // works: matches the demonstrated direction
            assert(!res ==> c != 'h'); // FAILS: the un-recoverable direction
        }
    } => Err(err) => assert_one_fails(err)
}
