#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Regression coverage for https://github.com/verus-lang/verus/issues/767
// ("Panic due to `#[derive(Debug)]`"). The original repro (a single-field
// struct with `#[derive(Debug)]`) was fixed by #1488, but only that one
// shape was ever locked in with a test. This sweeps a much broader battery
// of struct/enum shapes (see `common::DIVERSE_DERIVE_DEBUG_STRUCT_ENUM_SHAPES`,
// reusable by future tests too) to catch a regression in any of them, not
// just the exact original repro.

test_verify_one_file! {
    #[test] test_derive_debug_original_repro verus_code! {
        #[derive(Debug)]
        pub struct Q {
            pub x: i32,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_derive_debug_diverse_struct_enum_shapes
        DIVERSE_DERIVE_DEBUG_STRUCT_ENUM_SHAPES.to_string()
    => Ok(())
}

// Using the derived impl via `{:?}`/`println!` from *inside* a verified
// `verus!{}` function still isn't supported (fmt::Arguments/std::io::_print
// have no Verus spec), but this must fail with a normal, clean compile
// error - not a panic. This is expected behavior for unsupported std
// functionality, not a regression of #767 itself.
test_verify_one_file! {
    #[test] test_derive_debug_println_inside_verus_block_fails_cleanly verus_code! {
        #[derive(Debug)]
        pub struct Q {
            pub x: i32,
        }

        fn use_it() {
            let q = Q { x: 5 };
            println!("{:?}", q);
        }
    } => Err(e) => {
        assert!(e.errors.len() >= 1);
        assert!(e.errors[0].message.contains("is not supported"));
    }
}

// A field type that genuinely doesn't implement `Debug` (vstd's ghost-only
// `Ghost<T>`) must still be an ordinary, clean rustc trait-bound error, not
// a panic - `#[derive(Debug)]` generates a `T: Debug` bound per field like
// upstream rustc always has.
test_verify_one_file! {
    #[test] test_derive_debug_ghost_field_fails_cleanly verus_code! {
        #[derive(Debug)]
        pub struct WithGhost {
            pub x: i32,
            pub g: Ghost<int>,
        }
    } => Err(e) => assert_rust_error_msg(e, "doesn't implement `std::fmt::Debug`")
}
