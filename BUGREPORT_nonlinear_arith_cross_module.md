# Cross-module reference blows up an unrelated nonlinear_arith proof

## Summary

In a large real project (`nanoda_lib`), adding a small, otherwise-uncalled
`proof fn` in module `beta_model.rs` that merely *references* (in its
`requires` clause) a recursive `open spec fn` defined in a different module
(`expr_model.rs`) causes an **already-verified, logically-unrelated**
proof function elsewhere in `beta_model.rs` (`pstep_subst`, which uses
`assert(...) by (nonlinear_arith) requires ... {}`) to go from verifying in
~2-3s to hanging indefinitely (confirmed still running past 700s+ at
`--rlimit 200`).

This is confirmed to be genuine Z3 CPU-bound search blowup (`ps` shows the
`z3` subprocess pegged at ~99% CPU throughout), not a Rust-side hang, a
deadlock, or a threading artifact.

## Exact repro conditions (bisected)

All of the following were tested against `nanoda_lib` at commit `53a8a66`
(this repo checked out at `af037984`, current `main` tip at the time of
writing). Project not included here — see "Reproducing" below for how to
get a minimal case.

- Baseline: `beta_model::pstep_subst` verifies cleanly and fast (`--verify-
  function pstep_subst`, default `--rlimit 60`).
- Add ONE new function anywhere in `beta_model.rs`:
  ```rust
  #[verifier::external_body]
  pub proof fn repro_trigger(e: ExprSpec, ks: Seq<u64>, vs: Seq<LevelSpec>, e2: ExprSpec)
      requires crate::expr_model::subst_expr_levels_rel(e, ks, vs, e2)
      ensures size(e2) == size(e)
  {
  }
  ```
  (`subst_expr_levels_rel` is a recursive `open spec fn` over the same
  recursive datatype `ExprSpec` that `pstep_subst` itself recurses over,
  defined in the OTHER module, `expr_model.rs`.) → `pstep_subst` STILL
  verifies fine.
- Add a SECOND function alongside it — **even a totally trivial, unrelated
  one that doesn't reference `subst_expr_levels_rel` at all**:
  ```rust
  pub proof fn repro_trigger2() ensures true {}
  ```
  → `pstep_subst` now HANGS (confirmed CPU-bound in `z3`, not just slow).
- Two trivial functions with NEITHER referencing `subst_expr_levels_rel` →
  fine (fast, as baseline).
- One function referencing `subst_expr_levels_rel` + one trivial function →
  hangs, confirmed independently of:
  - `--rlimit` value: tried 5, 20, 30, 40, 50, 60, 120, 200 — same result
    at every value ≥ 20 that isn't immediately fast (5-50 all still pass
    when only 1 relevant function is present; with 2 present, EVERY rlimit
    tested still hangs, including 5, which should make Z3 give up almost
    instantly if the query were merely "somewhat harder").
  - `#[verifier::external_body]` vs a real recursive proof body on the new
    function(s) — same result either way, so it isn't about the new
    function's own proof search cost.
  - `#[verifier::opaque]` on `subst_expr_levels_rel` (+ matching `reveal()`
    calls at all call sites) — does NOT fix it, unlike an apparently
    similar-looking prior case in the same file (see "Related" below)
    where opacity WAS the fix.
  - `--num-threads 1` vs the default (9) — same result, ruling out any
    spinoff-context/thread-scheduling interaction.

So the trigger is specifically: **(a function whose contract references a
cross-module recursive spec fn) + (any second function existing in the
same source file)**. Either alone is fine.

## Evidence it's genuine Z3 search cost, not a Rust-side hang

```
$ ps aux | grep -E "verus|z3"
... z3 -smt2 -in                                    99.6%  CPU  ...
... rust_verify ...                                  0.0%  CPU  ...
```
The `z3` subprocess itself accumulates real CPU time throughout the hang.
This persisted identically under `--num-threads 1`.

## Hypothesis

Not confirmed, but consistent with all observations: `vir/src/prune.rs`'s
per-module/per-function reachability computation (`prune_krate_for_module_
or_krate` and friends) is pulling additional axioms/definitions into
`pstep_subst`'s SMT query once *any* new function referencing the
cross-module spec fn exists in the same file, and this happens to depend on
there being at least 2 "new" reachable items (possibly a batching/grouping
artifact in how reachable functions get attached to buckets, or in how
opaque-function axioms get attached per-bucket vs per-krate). Z3's
nonlinear-arithmetic tactic (`smt.arith.solver=6`, set specifically for
`by (nonlinear_arith)` queries — see `apply_per_query_smt_options` in
`rust_verify/src/verifier.rs`) is known to be highly sensitive to the
presence of extra quantified axioms in scope, even entirely unused ones,
because they change what the instantiation heuristics try.

This was NOT root-caused at the `vir`/AIR-generation level — that's the
suggested next step (see below), since attempts to compare `--log air`/
`--log smt` dumps directly were confounded by unrelated I/O overhead (the
target function set pulled in by `--verify-function pstep_subst
--verify-only-module beta_model` turned out to include dozens of *other*
functions too, each producing large log files, making direct diffing
impractical without first understanding why so many functions are
"reachable" from a single `--verify-function` target in the first place —
itself possibly a related or contributing observation).

## Related

A structurally similar-sounding issue was previously observed and
"fixed" by marking two OTHER cross-module recursive functions
(`nlbv`/`subst_full`, called far more pervasively — 13 call sites across 4
files) `#[verifier::opaque]`... except that attempt was later reverted
because, even after adding all needed `reveal()` calls and confirming every
individual function still verified fine, the WHOLE-MODULE check ballooned
to 8+ minutes even at `--rlimit 10`. That is: this general class of
"aggregate slowdown from a new/changed cross-module recursive definition"
has now been hit at least twice, with two different specific functions,
and opacity fixed neither case satisfactorily. See nanoda_lib's own
project memory (`project_beta_model_opacity_status.md`,
`project_nanoda_verification_goal.md`) for the fuller history if useful.

## Suggested next steps

1. Reproduce standalone (outside nanoda_lib): construct two small modules,
   each with a handful of recursive datatype/spec-fn definitions plus one
   deliberately delicate `by (nonlinear_arith)` proof (may need real
   tuning to get one that's "on the edge" the way `pstep_subst` was after
   months of accumulated proof complexity — the naive small repro attempt
   in this session did not immediately reproduce it standalone, likely
   because the victim proof needs to be genuinely close to its resource
   ceiling already).
2. Instrument `prune_krate_for_module_or_krate` (and/or the bucket-assembly
   code in `rust_verify/src/verifier.rs`) to print, for the SAME target
   function, the exact set of reached functions/axioms in the 1-extra-
   function vs 2-extra-function cases, and diff them directly — this
   sidesteps needing to diff huge AIR/SMT text dumps.
3. Check whether `--verify-function` genuinely restricts pruning as
   expected, or whether (as observed above) it ends up including many more
   functions' full queries in the same invocation than expected — if the
   latter is itself a bug, it may be the more fundamental root cause worth
   fixing first.

## Session context

Investigated 2026-08-26 while extending `nanoda_lib` (a separate, unrelated
project verifying a Lean 4 kernel implementation) — see that project's
`git log` around commit `53a8a66` and its Claude-memory files referenced
above for full context if picking this up later.
