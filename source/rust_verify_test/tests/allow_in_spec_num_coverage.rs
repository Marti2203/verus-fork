#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// std_specs/num.rs's wrapping/checked/saturating arithmetic family (found via
// tools/spec_usage_coverage) carries #[verifier::allow_in_spec] but was never
// called directly in spec position by any test - every existing call went through
// an exec `let` binding first, which doesn't exercise the attribute at all.
//
// Each test below calls a method once via an exec `let` (a real runtime call) and
// once again directly inside assert(...) (a spec-mode call, only legal because of
// allow_in_spec), verified equal for arbitrary inputs. Confirmed to fail to compile
// if the corresponding allow_in_spec attribute is removed (spot-checked for
// wrapping_add and checked_div; the rest follow the identical mechanism).
//
// Written out literally per type rather than generated via a wrapping macro_rules!:
// verus_code! reconstructs its source by reading back the literal text at its
// token span (see rust_verify_test_macros/src/rust_code.rs), which only works for
// directly-written invocations - a macro_rules! substitution layer around it just
// reads back the macro definition's own unsubstituted template text instead.

test_verify_one_file! {
    #[test] u8_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: u8, y: u8, sy: i8, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] i8_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: i8, y: i8, uy: u8, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] u16_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: u16, y: u16, sy: i16, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] i16_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: i16, y: i16, uy: u16, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] u32_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: u32, y: u32, sy: i32, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] i32_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: i32, y: i32, uy: u32, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] u64_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: u64, y: u64, sy: i64, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] i64_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: i64, y: i64, uy: u64, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] u128_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: u128, y: u128, sy: i128, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] i128_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: i128, y: i128, uy: u128, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] usize_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: usize, y: usize, sy: isize, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_signed(sy);
            assert(x.wrapping_add_signed(sy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_signed(sy);
            assert(x.checked_add_signed(sy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_next_multiple_of(y);
            assert(x.checked_next_multiple_of(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
            let a = x.saturating_add(y);
            assert(x.saturating_add(y) == a);
            let a = x.saturating_sub(y);
            assert(x.saturating_sub(y) == a);
            let a = x.saturating_mul(y);
            assert(x.saturating_mul(y) == a);
            let a = x.is_multiple_of(y);
            assert(x.is_multiple_of(y) == a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] isize_allow_in_spec_coverage verus_code! {
        use vstd::prelude::*;

        fn test(x: isize, y: isize, uy: usize, r: u32) {
            let a = x.wrapping_add(y);
            assert(x.wrapping_add(y) == a);
            let a = x.wrapping_add_unsigned(uy);
            assert(x.wrapping_add_unsigned(uy) == a);
            let a = x.wrapping_sub(y);
            assert(x.wrapping_sub(y) == a);
            let a = x.wrapping_mul(y);
            assert(x.wrapping_mul(y) == a);
            let a = x.wrapping_shl(r);
            assert(x.wrapping_shl(r) == a);
            let a = x.wrapping_shr(r);
            assert(x.wrapping_shr(r) == a);
            let a = x.checked_add(y);
            assert(x.checked_add(y) == a);
            let a = x.checked_add_unsigned(uy);
            assert(x.checked_add_unsigned(uy) == a);
            let a = x.checked_sub(y);
            assert(x.checked_sub(y) == a);
            let a = x.checked_sub_unsigned(uy);
            assert(x.checked_sub_unsigned(uy) == a);
            let a = x.checked_mul(y);
            assert(x.checked_mul(y) == a);
            let a = x.checked_div(y);
            assert(x.checked_div(y) == a);
            let a = x.checked_div_euclid(y);
            assert(x.checked_div_euclid(y) == a);
            let a = x.checked_rem(y);
            assert(x.checked_rem(y) == a);
            let a = x.checked_rem_euclid(y);
            assert(x.checked_rem_euclid(y) == a);
        }
    } => Ok(())
}
