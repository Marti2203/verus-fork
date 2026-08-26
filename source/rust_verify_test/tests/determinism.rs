#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

use tempfile::TempDir;

// Regression test for https://github.com/verus-lang/verus/issues/469 ("verus
// nondeterminism"): the reporter saw the same input produce different
// verification results across runs, traced by a maintainer to AIR/SMT
// declarations being emitted in hash-table iteration order. That was fixed by
// giving tuple/closure datatypes a fixed print order (77e518bbd) and
// replacing the order-sensitive HashMap/HashSet uses with IndexMap/IndexSet
// (b05f6d30c). The issue's own follow-up asked for exactly this: "add a
// smoke test that Verus produces identical SMTLIB inputs on repeated runs".
//
// This exercises cross-module #[verifier::opaque] spec functions, several
// trait impls, and a quantified requires clause together, since those are
// the areas that used to rely on HashMap/HashSet iteration order.
#[test]
fn air_and_smt_output_is_deterministic_issue469() {
    let tempdir = TempDir::new().expect("temp dir");
    let entry_file = tempdir.path().join("test.rs");
    let code = format!(
        "{}\n{}\n{}",
        FEATURE_PRELUDE,
        USE_PRELUDE,
        r#"
verus! {

mod m1 {
    use verus_builtin::*;
    use verus_builtin_macros::*;
    #[verifier::opaque]
    pub open spec fn f1(x: int) -> bool { x > 0 }
    #[verifier::opaque]
    pub open spec fn f2(x: int) -> bool { x > 1 }
    #[verifier::opaque]
    pub open spec fn f3(x: int) -> bool { x > 2 }
    #[verifier::opaque]
    pub open spec fn f4(x: int) -> bool { x > 3 }
    #[verifier::opaque]
    pub open spec fn f5(x: int) -> bool { x > 4 }
}

mod m2 {
    use verus_builtin::*;
    use verus_builtin_macros::*;
    use crate::m1::*;
    #[verifier::opaque]
    pub open spec fn g1(x: int) -> bool { f1(x) && f2(x) }
    #[verifier::opaque]
    pub open spec fn g2(x: int) -> bool { f2(x) && f3(x) }
    #[verifier::opaque]
    pub open spec fn g3(x: int) -> bool { f3(x) && f4(x) }
    #[verifier::opaque]
    pub open spec fn g4(x: int) -> bool { f4(x) && f5(x) }
    #[verifier::opaque]
    pub open spec fn g5(x: int) -> bool { f5(x) && f1(x) }
}

pub trait Tr1 {
    spec fn inv(&self) -> bool;
    fn m(&self)
        requires self.inv();
}

pub struct A { pub v: u64 }
pub struct B { pub v: u64 }
pub struct C { pub v: u64 }
pub struct D { pub v: u64 }
pub struct E { pub v: u64 }

impl Tr1 for A {
    open spec fn inv(&self) -> bool { self.v > 0 }
    fn m(&self) { }
}
impl Tr1 for B {
    open spec fn inv(&self) -> bool { self.v > 1 }
    fn m(&self) { }
}
impl Tr1 for C {
    open spec fn inv(&self) -> bool { self.v > 2 }
    fn m(&self) { }
}
impl Tr1 for D {
    open spec fn inv(&self) -> bool { self.v > 3 }
    fn m(&self) { }
}
impl Tr1 for E {
    open spec fn inv(&self) -> bool { self.v > 4 }
    fn m(&self) { }
}

use m1::*;
use m2::*;

proof fn test_cross(x: int)
    requires
        f1(x), f2(x), f3(x), f4(x), f5(x),
        g1(x), g2(x), g3(x), g4(x), g5(x),
{
    reveal(f1); reveal(f2); reveal(f3); reveal(f4); reveal(f5);
    reveal(g1); reveal(g2); reveal(g3); reveal(g4); reveal(g5);
    assert(x > 0);
    assert(x > 4);
}

spec fn le(a: int, b: int) -> bool { a <= b }

proof fn test_transitive(a: int, b: int, c: int)
    requires
        forall|x: int, y: int| #![auto] le(x, y) && le(y, c) ==> le(x, c),
        le(a, b), le(b, c),
{
    assert(le(a, c));
}

fn main() {}

} // verus!
"#
    );
    std::fs::write(&entry_file, code).expect("write source file");

    let suffixes = ["root.air", "root-final.air", "root.smt2"];
    let mut contents: Vec<Vec<Vec<u8>>> = suffixes.iter().map(|_| Vec::new()).collect();
    for run_id in 0..3 {
        let log_dir = tempdir.path().join(format!("logs{run_id}"));
        let output = run_verus_raw(
            &["--log-all", "--log-dir", log_dir.to_str().unwrap(), entry_file.to_str().unwrap()],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed on run {}:\n{}",
            run_id,
            String::from_utf8_lossy(&output.stderr)
        );
        for (i, suffix) in suffixes.iter().enumerate() {
            let bytes = std::fs::read(log_dir.join(suffix))
                .unwrap_or_else(|e| panic!("failed to read {} from run {}: {}", suffix, run_id, e));
            contents[i].push(bytes);
        }
    }
    for (i, suffix) in suffixes.iter().enumerate() {
        for run_id in 1..contents[i].len() {
            assert_eq!(
                contents[i][0], contents[i][run_id],
                "{} differs between run 0 and run {} on identical input (issue #469)",
                suffix, run_id
            );
        }
    }
}
