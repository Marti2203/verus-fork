# RESOLVED: cross-module reference blows up an unrelated nonlinear_arith proof

**Status: root-caused and fixed. Not a Verus bug — a rediscovery of the
documented "flaky proof" scenario, now with a concrete, instrumented
explanation of the mechanism.**

## Summary

In a large real project (`nanoda_lib`), adding a small, otherwise-uncalled
`proof fn` in module `beta_model.rs` that merely *references* (in its
`requires` clause) a recursive `open spec fn` defined in a different module
(`expr_model.rs`) — **plus any second, completely unrelated function
existing in the same file** — caused an already-verified, logically-
unrelated proof function elsewhere in `beta_model.rs` (`pstep_subst`, which
uses `assert(...) by (nonlinear_arith) requires ... {}`) to go from
verifying in ~2-3s to hanging indefinitely (confirmed still running past
700s+ at `--rlimit 200`, and confirmed genuine Z3 CPU-bound search blowup
via `ps`, not a deadlock — independent of `--rlimit` and `--num-threads`).

## Root cause (confirmed via instrumentation)

`rust_verify/src/buckets.rs::get_buckets`: a function gets its own
`BucketId::Fun` (and therefore its own, function-scoped pruning) **only if**
it has `#[verifier::spinoff_prover]`. Every other function in a module
falls into one shared `BucketId::Module` bucket.

`vir/src/prune.rs::prune_krate_for_module_or_krate` prunes a `BucketId::
Module` bucket with `fun=None`, which means **every function in the module
is a reachability root** — confirmed directly by adding a debug print (see
"Instrumentation" below) right after `traverse_reachable`:

```
[prune-debug] root fun=None reached_functions.len()=691
[prune-debug]   contains needle: repro_trigger
[prune-debug]   contains needle: repro_trigger2
```

vs., after adding `#[verifier::spinoff_prover]` to `pstep_subst`:

```
[prune-debug] root fun=None reached_functions.len()=691   <- unrelated shared module bucket, unaffected
[prune-debug] root fun=Some("pstep_subst") reached_functions.len()=95   <- pstep_subst's own bucket, correctly narrow
verification results:: 40 verified, 0 errors
```

So **`--verify-function` does not narrow SMT-query pruning for non-
`spinoff_prover` functions at all** — it only restricts what gets reported/
attempted. Any new function anywhere in a module's shared bucket becomes
part of every other (non-spinoff) function's SMT background regardless of
actual call relationships, and delicate `by (nonlinear_arith)` proofs are
sensitive enough to background-axiom-set perturbation for this to matter a
great deal in practice.

## This is already documented — just not with this level of mechanism detail

`docs/guide/src/checklist.md`:
> **My proof is "flaky": it sometimes works, but then I change something
> unrelated, and it breaks.**
> * Try adding `#[verifier::spinoff_prover]` to the function. This can make
>   it a little more stable.

This is exactly that scenario. What this investigation adds is a concrete,
instrumented, root-caused explanation of *why* — which could be worth
folding into the docs (see "Possible doc improvement" below) so users
understand the mechanism (shared pruning bucket + `fun=None` reachability)
rather than treating `spinoff_prover` as a magic incantation to "try."

## What did NOT fix it (dead ends worth recording)

- `#[verifier::opaque]` on the referenced cross-module spec fn (+ matching
  `reveal()` calls at every call site) — this is the correct fix for a
  DIFFERENT problem (a function's body being auto-unfolded/inlined
  pervasively, inflating every query that mentions it — see `beta_model.rs`'s
  own `shift`/`subst` opacity, a genuine unrelated win). It does nothing
  for the bucket-sharing/pruning-root issue described here.
- `--num-threads 1` — ruled out any spinoff-context/thread-scheduling
  explanation.
- Any `--rlimit` value from 5 to 200 — ruled out "just needs more budget."

## Instrumentation added (this branch, `source/vir/src/prune.rs`)

A debug `eprintln!`, gated behind the `VERUS_DEBUG_PRUNE=<needle>`
environment variable, added right after the `traverse_reachable` call in
`prune_krate_for_module_or_krate`. Prints the root function (if any) and
the count of `reached_functions`, plus any reached function whose last path
segment contains `<needle>`. No effect when the env var is unset. Useful
in general for diagnosing "why is my function's query touching more than I
expected" — kept here as a debugging tool, not intended as a permanent
Verus feature as written (see "Possible next steps" below if it's worth
turning into one).

## Possible next steps (optional, not blocking anything)

1. **Docs improvement**: expand `checklist.md`'s "flaky proof" entry (or
   add a new page) with the mechanism above — shared pruning buckets,
   `fun=None` module-wide reachability roots for non-spinoff functions,
   and a pointer to `--verify-function`'s actual scope (it filters
   reporting, not the SMT background, for non-spinoff-prover functions).
2. **Diagnostic feature**: a real `--log prune` (or similar) flag exposing
   the `VERUS_DEBUG_PRUNE`-style reachability-set size (and maybe full
   list, or a diff against a prior run) without needing a local source
   patch — would have made this investigation much faster to reach the
   root cause.
3. Nothing further is strictly needed — `nanoda_lib`'s own fix (applying
   `#[verifier::spinoff_prover]` to `pstep_subst` and its whole nonlinear-
   arith-heavy sibling family) is landed and confirmed working, full crate
   431 verified / 0 errors, faster than before.

## Session context

Investigated 2026-08-26 while extending `nanoda_lib` (a separate, unrelated
project verifying a Lean 4 kernel implementation) — see that project's
commit `272bd90` and its Claude-memory files (`feedback_verus_spinoff_
prover.md`, `project_beta_model_opacity_status.md`) for full context if
picking this up later.
