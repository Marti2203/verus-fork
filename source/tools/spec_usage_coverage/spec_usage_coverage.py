#!/usr/bin/env python3
"""
Experimental, heuristic audit: for every vstd function tagged
#[verifier::allow_in_spec], does the test corpus (rust_verify_test/tests/**)
contain at least one call site that actually uses it in spec/ghost position
(inside a proof/spec fn, or inside a requires/ensures/invariant/recommends/
decreases/assert clause) - as opposed to only ever calling it from exec code
via a `let` binding, which never exercises allow_in_spec at all.

This is line-based and Rust-syntax-aware only in a shallow way (brace
counting with escape/string/char-literal stripping, keyword matching for
fn/proof fn/spec fn and requires/ensures/... clause headers). It is a triage
tool, not a certifier: every GAP it reports needs the same manual
fail-without/pass-with-fix confirmation used for the char::len_utf8/
is_whitespace case (see PR #2919) before treating it as a real bug.

Usage:
    python3 spec_usage_coverage.py <verus-source-root>
"""
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ALLOW_IN_SPEC_RE = re.compile(r"#\[verifier::allow_in_spec\]")
ASSUME_SPEC_RE = re.compile(r"assume_specification\s*\[\s*(.+?)\s*\]")
FN_NAME_RE = re.compile(r"\bfn\s+(\w+)")
ATTR_LINE_RE = re.compile(r"^\s*#\[")
FN_SIG_START_RE = re.compile(r"\b(proof\s+fn|spec(?:\([\w]+\))?\s+fn|fn)\s+(\w+)")
CLAUSE_HEADER_RE = re.compile(r"^\s*(requires|ensures|invariant|recommends|decreases|returns)\b")

# Strip char/string literal content and unicode escapes so brace-counting
# isn't confused by things like '\u{9}' or "a { b".
STRIP_RE = re.compile(r"'\\u\{[0-9a-fA-F]+\}'|'\\?.'|\"(?:[^\"\\]|\\.)*\"")


@dataclass
class Target:
    method_name: str
    full_path: str
    file: str
    line: int
    covered_by: list = field(default_factory=list)


def find_targets(vstd_root: Path):
    targets = []
    for path in sorted(vstd_root.rglob("*.rs")):
        lines = path.read_text(errors="replace").splitlines()
        for i, line in enumerate(lines):
            if not ALLOW_IN_SPEC_RE.search(line):
                continue
            # Look ahead, skipping other attribute lines (#[cfg(...)] etc.), for the
            # assume_specification[...] path or a plain fn name.
            for j in range(i + 1, min(i + 8, len(lines))):
                if ATTR_LINE_RE.match(lines[j]):
                    continue
                m = ASSUME_SPEC_RE.search(lines[j])
                if m:
                    full = m.group(1)
                    # macro-template paths like <$uN>::wrapping_add - keep the last
                    # real identifier segment as the method name.
                    name = re.split(r"::|[<>$]", full)[-1] or re.split(r"::|[<>$]", full)[-2]
                    targets.append(Target(name, full, str(path), i + 1))
                    break
                m2 = FN_NAME_RE.search(lines[j])
                if m2:
                    name = m2.group(1)
                    targets.append(Target(name, name, str(path), i + 1))
                    break
    return targets


def strip_literals(line: str) -> str:
    return STRIP_RE.sub("", line)


def scan_test_file(path: Path, targets_by_name: dict):
    lines = path.read_text(errors="replace").splitlines()
    # Stack of (brace_depth_at_open, mode) for enclosing fn bodies. mode in {"ghost","exec"}.
    fn_stack = []
    depth = 0
    pending_fn_mode = None  # mode of the most recently seen fn signature, awaiting its '{'
    pending_clause = False  # saw requires/ensures/... since the last fn signature, before body '{'

    for lineno, raw_line in enumerate(lines, start=1):
        line = strip_literals(raw_line)

        sig = FN_SIG_START_RE.search(line)
        if sig:
            kind = sig.group(1)
            pending_fn_mode = "ghost" if kind.startswith(("proof", "spec")) else "exec"
            pending_clause = False

        if pending_fn_mode is not None and CLAUSE_HEADER_RE.search(line):
            pending_clause = True

        in_ghost_here = pending_clause or (fn_stack and fn_stack[-1][1] == "ghost")

        # assert(...)/assert_by/... are always ghost regardless of enclosing fn mode.
        if re.search(r"\bassert(_by|_forall)?\s*[!(]", line):
            in_ghost_here = True

        for name, target_list in targets_by_name.items():
            # Match both method-call (`x.name(`) and UFCS/associated-fn (`Type::name(`)
            # forms; require a word boundary so e.g. `name` doesn't match `my_name(`.
            if re.search(r"(?:\.|::)" + re.escape(name) + r"\(", line) and in_ghost_here:
                for t in target_list:
                    t.covered_by.append(f"{path}:{lineno}")

        opens = line.count("{")
        closes = line.count("}")
        for _ in range(opens):
            depth += 1
            if pending_fn_mode is not None:
                fn_stack.append((depth, pending_fn_mode))
                pending_fn_mode = None
                pending_clause = False
        for _ in range(closes):
            if fn_stack and fn_stack[-1][0] == depth:
                fn_stack.pop()
            depth = max(0, depth - 1)


def main():
    if len(sys.argv) != 2:
        print(__doc__)
        sys.exit(1)
    root = Path(sys.argv[1])
    vstd_root = root / "vstd"
    test_root = root / "rust_verify_test" / "tests"

    targets = find_targets(vstd_root)
    targets_by_name = {}
    for t in targets:
        targets_by_name.setdefault(t.method_name, []).append(t)

    for test_file in sorted(test_root.rglob("*.rs")):
        scan_test_file(test_file, targets_by_name)

    covered = [t for t in targets if t.covered_by]
    gaps = [t for t in targets if not t.covered_by]

    print(f"# allow_in_spec targets found in vstd: {len(targets)}")
    print(f"# with at least one heuristic ghost-mode call site: {len(covered)}")
    print(f"# GAPS (no ghost-mode call site found - needs manual confirmation): {len(gaps)}\n")

    print("## GAPS")
    for t in gaps:
        print(f"  {t.full_path}  ({t.file}:{t.line})")

    print("\n## Covered (first evidence site shown)")
    for t in covered:
        print(f"  {t.full_path}  <- {t.covered_by[0]}")


if __name__ == "__main__":
    main()
