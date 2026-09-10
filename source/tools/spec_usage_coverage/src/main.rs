//! Experimental, AST-based audit: for every vstd item tagged
//! `#[verifier::allow_in_spec]`, does the test corpus (`rust_verify_test/tests/**`)
//! contain at least one call site that actually uses it in spec/ghost position
//! (inside a proof/spec fn body, a requires/ensures/recommends/decreases/invariants/
//! returns clause, or an `assert(...)`) - as opposed to only ever calling it from
//! exec code via a `let` binding, which never exercises the attribute at all.
//!
//! Unlike a text/regex pass, this uses `verus_syn` (the real, Verus-aware fork of
//! `syn` already vendored in this workspace, see tools/line_count for precedent) to
//! parse actual `proof fn`/`spec fn` signatures, `assume_specification[...]` items,
//! and expression trees - so it isn't fooled by nested brackets, string/char
//! literals, or comments, and it distinguishes a real UFCS call to a type's method
//! from a call to a differently-scoped helper (e.g. `u32_specs::wrapping_shl`, an
//! internal per-type module - see std_specs/num.rs's own "Put in separate module to
//! avoid name collisions" comment) by real path segments, not a regex guess.
//!
//! Still a triage tool, not a certifier: matching is by bare method/last-path-segment
//! name with no receiver-type resolution, so two distinct types sharing a method name
//! (e.g. std HashMap's `Entry::key`/`OccupiedEntry::key`/`VacantEntry::key`) can't be
//! told apart - a call to an unrelated type's same-named method still counts as
//! "covered" evidence for all of them. Closing that gap for real needs the compiler's
//! own type information (checking the elaborated SST for a genuine `ExpX::Call` to
//! the exact target `Fun`), which this tool doesn't have.
//!
//! Every GAP this reports still needs the same manual fail-without/pass-with-fix
//! confirmation used for the char::len_utf8/is_whitespace case (PR #2919) before
//! being treated as a real bug.
//!
//! Real, known blind spot: a `verus!`/`verus_code!` block is parsed *in isolation*
//! (its raw tokens, re-tokenized and parsed as a standalone item list) - a file whose
//! `verus!` body sits inside a `macro_rules!` template using metavariables like `$uN`
//! (e.g. std_specs/num.rs's `num_specs!` pattern, generating the wrapping/checked/
//! saturating arithmetic family for every integer type from one template) fails to
//! parse, since `$uN` isn't valid standalone syntax outside the macro definition
//! itself. This tool reports such failures on stderr rather than silently dropping
//! them, but does not attempt to simulate macro_rules! expansion to recover them.
//! This is a known, *accepted* limitation of parsing a verus! block in isolation in
//! this codebase's own tooling, not a mistake unique to this tool: `tools/line_count`
//! hits the identical wall on the same file (`line_count vstd/std_specs/num.rs`
//! reports 519 of ~528 lines "unaccounted"). A text/regex-based pass (see this tool's
//! git history for a prior version) doesn't need valid syntax at all, so it happens
//! not to have this particular blind spot - at the cost of the bracket-nesting and
//! qualifier-ambiguity bugs a real parser doesn't have. Recovering full precision on
//! both fronts at once would need a tiny macro_rules! substitution pass (expand each
//! known invocation like `num_specs!(u8, i8, u8_specs_tmp, ...)` against the
//! template before parsing) - not attempted here.
//!
//! Usage: spec_usage_coverage <verus-source-root>

use std::collections::HashMap;
use std::path::{Path as FsPath, PathBuf};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use verus_syn::spanned::Spanned;
use verus_syn::visit::{self, Visit};
use verus_syn::{
    Assert, AssumeSpecification, Expr, ExprCall, ExprMethodCall, File, FnMode, ImplItemFn, ItemFn,
    Path, SignatureSpec, TraitItemFn,
};

fn line_of<T: Spanned>(node: &T) -> usize {
    node.span().start().line
}

#[derive(Clone)]
struct Target {
    method_name: String,
    full_path: String,
    file: String,
    line: usize,
    covered_by: Vec<String>,
}

fn is_ghost_mode(mode: &FnMode) -> bool {
    matches!(
        mode,
        FnMode::Spec(_) | FnMode::SpecChecked(_) | FnMode::Proof(_) | FnMode::ProofAxiom(_)
    )
}

fn has_allow_in_spec(attrs: &[verus_syn::Attribute]) -> bool {
    attrs.iter().any(|a| {
        let segs: Vec<String> = a.path().segments.iter().map(|s| s.ident.to_string()).collect();
        segs == ["verifier", "allow_in_spec"]
    })
}

fn last_two_segments(path: &Path) -> (Option<String>, String) {
    let segs: Vec<String> = path.segments.iter().map(|s| s.ident.to_string()).collect();
    match segs.len() {
        0 => (None, String::new()),
        1 => (None, segs[0].clone()),
        n => (Some(segs[n - 2].clone()), segs[n - 1].clone()),
    }
}

/// Internal per-type helper modules (e.g. u32_specs, u32_specs_tmp) are always
/// spec-callable and don't exercise the tagged method's own allow_in_spec.
fn is_internal_helper_mod(qualifier: &str) -> bool {
    qualifier.ends_with("_specs") || qualifier.ends_with("_specs_tmp")
}

// ---- Pass 1: collect allow_in_spec targets from vstd ----

struct TargetCollector {
    file: String,
    targets: Vec<Target>,
}

impl TargetCollector {
    fn record(
        &mut self,
        attrs: &[verus_syn::Attribute],
        full_path: String,
        method_name: String,
        line: usize,
    ) {
        if has_allow_in_spec(attrs) {
            self.targets.push(Target {
                method_name,
                full_path,
                file: self.file.clone(),
                line,
                covered_by: Vec::new(),
            });
        }
    }
}

impl<'ast> Visit<'ast> for TargetCollector {
    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        self.record(&i.attrs, i.sig.ident.to_string(), i.sig.ident.to_string(), line_of(i));
        visit::visit_item_fn(self, i);
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        self.record(&i.attrs, i.sig.ident.to_string(), i.sig.ident.to_string(), line_of(i));
        visit::visit_impl_item_fn(self, i);
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        self.record(&i.attrs, i.sig.ident.to_string(), i.sig.ident.to_string(), line_of(i));
        visit::visit_trait_item_fn(self, i);
    }

    fn visit_assume_specification(&mut self, i: &'ast AssumeSpecification) {
        // `<[T]>::len`-style paths put `[T]` in `qself`, leaving just `::len` in
        // `path` - render both together so the reported target is readable.
        let (_, name) = last_two_segments(&i.path);
        let full = match &i.qself {
            Some(q) => format!("<{}>{}", q.ty.to_token_stream(), i.path.to_token_stream()),
            None => i.path.to_token_stream().to_string(),
        };
        self.record(&i.attrs, full, name, line_of(i));
        visit::visit_assume_specification(self, i);
    }
}

// ---- Pass 2: scan the test corpus for ghost-mode call sites ----

struct CoverageScanner<'a> {
    file: String,
    ghost_depth: u32,
    targets_by_name: &'a mut HashMap<String, Vec<usize>>, // name -> indices into `targets`
    targets: &'a mut Vec<Target>,
    current_line_hint: usize,
}

impl<'a> CoverageScanner<'a> {
    fn record_hit(&mut self, name: &str) {
        if let Some(indices) = self.targets_by_name.get(name) {
            let evidence = format!("{}:{}", self.file, self.current_line_hint);
            for &idx in indices {
                self.targets[idx].covered_by.push(evidence.clone());
            }
        }
    }
}

impl<'a, 'ast> Visit<'ast> for CoverageScanner<'a> {
    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        visit::visit_item_fn(self, i);
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        visit::visit_impl_item_fn(self, i);
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        visit::visit_trait_item_fn(self, i);
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    // requires/ensures/recommends/decreases/invariants/returns are always spec-mode
    // expressions, regardless of the enclosing fn's own mode.
    fn visit_signature_spec(&mut self, i: &'ast SignatureSpec) {
        self.ghost_depth += 1;
        visit::visit_signature_spec(self, i);
        self.ghost_depth -= 1;
    }

    fn visit_assert(&mut self, i: &'ast Assert) {
        self.ghost_depth += 1;
        visit::visit_assert(self, i);
        self.ghost_depth -= 1;
    }

    fn visit_expr_call(&mut self, i: &'ast ExprCall) {
        if self.ghost_depth > 0 {
            if let Expr::Path(p) = &*i.func {
                let (qualifier, name) = last_two_segments(&p.path);
                let ufcs_ok = match &qualifier {
                    Some(q) => !is_internal_helper_mod(q),
                    None => true,
                };
                if ufcs_ok {
                    self.current_line_hint = line_of(i);
                    self.record_hit(&name);
                }
            }
        }
        visit::visit_expr_call(self, i);
    }

    fn visit_expr_method_call(&mut self, i: &'ast ExprMethodCall) {
        if self.ghost_depth > 0 {
            self.current_line_hint = line_of(i);
            self.record_hit(&i.method.to_string());
        }
        visit::visit_expr_method_call(self, i);
    }
}

// ---- Finding verus!/verus_code! macro bodies anywhere in a file's raw tokens ----

fn find_verus_blocks(tokens: TokenStream, out: &mut Vec<TokenStream>) {
    let tts: Vec<TokenTree> = tokens.into_iter().collect();
    let mut i = 0;
    while i < tts.len() {
        if let TokenTree::Ident(id) = &tts[i] {
            let name = id.to_string();
            if name == "verus" || name == "verus_code" {
                if let Some(TokenTree::Punct(p)) = tts.get(i + 1) {
                    if p.as_char() == '!' {
                        if let Some(TokenTree::Group(g)) = tts.get(i + 2) {
                            out.push(g.stream());
                            i += 3;
                            continue;
                        }
                    }
                }
            }
        }
        if let TokenTree::Group(g) = &tts[i] {
            find_verus_blocks(g.stream(), out);
        }
        i += 1;
    }
}

// ---- Minimal macro_rules! substitution, for single-rule, non-repetition macros
// like std_specs/num.rs's `num_specs!` - just enough to expose the verus! block
// such macros wrap, not a general macro_rules! expander (no `$(...)* ` support).

struct MacroDef {
    params: Vec<String>,
    body: TokenStream,
}

/// Splits a token sequence on top-level commas (not inside nested groups).
fn split_on_top_level_commas(tts: &[TokenTree]) -> Vec<Vec<TokenTree>> {
    let mut parts = Vec::new();
    let mut current = Vec::new();
    for tt in tts {
        match tt {
            TokenTree::Punct(p) if p.as_char() == ',' => {
                parts.push(std::mem::take(&mut current));
            }
            _ => current.push(tt.clone()),
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

/// Finds every single-rule `macro_rules! name { (params) => { body }; }` definition
/// anywhere in `tokens`. Multi-rule macros (more than one `=>` arm) are skipped -
/// not needed for the one macro (num_specs!) this pass exists for.
fn find_macro_rules_defs(tokens: &TokenStream, out: &mut HashMap<String, MacroDef>) {
    let tts: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let mut i = 0;
    while i < tts.len() {
        if let TokenTree::Ident(id) = &tts[i] {
            if id == "macro_rules" {
                if let (
                    Some(TokenTree::Punct(bang)),
                    Some(TokenTree::Ident(name)),
                    Some(TokenTree::Group(rules)),
                ) = (tts.get(i + 1), tts.get(i + 2), tts.get(i + 3))
                {
                    if bang.as_char() == '!' {
                        let rule_tts: Vec<TokenTree> = rules.stream().into_iter().collect();
                        // Expect exactly: Group(matcher) '=' '>' Group(body) [';']
                        if let (
                            Some(TokenTree::Group(matcher)),
                            Some(TokenTree::Punct(eq)),
                            Some(TokenTree::Punct(gt)),
                            Some(TokenTree::Group(body)),
                        ) = (rule_tts.first(), rule_tts.get(1), rule_tts.get(2), rule_tts.get(3))
                        {
                            let is_single_rule = rule_tts.len() <= 5; // + optional trailing ';'
                            if eq.as_char() == '=' && gt.as_char() == '>' && is_single_rule {
                                let matcher_tts: Vec<TokenTree> =
                                    matcher.stream().into_iter().collect();
                                let mut params = Vec::new();
                                let mut j = 0;
                                while j < matcher_tts.len() {
                                    if let TokenTree::Punct(dollar) = &matcher_tts[j] {
                                        if dollar.as_char() == '$' {
                                            if let Some(TokenTree::Ident(p)) =
                                                matcher_tts.get(j + 1)
                                            {
                                                params.push(p.to_string());
                                            }
                                        }
                                    }
                                    j += 1;
                                }
                                out.insert(
                                    name.to_string(),
                                    MacroDef { params, body: body.stream() },
                                );
                            }
                        }
                    }
                }
            }
        }
        if let TokenTree::Group(g) = &tts[i] {
            find_macro_rules_defs(&g.stream(), out);
        }
        i += 1;
    }
}

/// Finds every `name!( args )` invocation anywhere in `tokens`, split into
/// comma-separated argument token sequences.
fn find_macro_invocations(tokens: &TokenStream, name: &str) -> Vec<Vec<Vec<TokenTree>>> {
    let mut out = Vec::new();
    let tts: Vec<TokenTree> = tokens.clone().into_iter().collect();
    let mut i = 0;
    while i < tts.len() {
        if let TokenTree::Ident(id) = &tts[i] {
            if id == name {
                if let (Some(TokenTree::Punct(bang)), Some(TokenTree::Group(args))) =
                    (tts.get(i + 1), tts.get(i + 2))
                {
                    if bang.as_char() == '!' {
                        let arg_tts: Vec<TokenTree> = args.stream().into_iter().collect();
                        out.push(split_on_top_level_commas(&arg_tts));
                    }
                }
            }
        }
        if let TokenTree::Group(g) = &tts[i] {
            out.extend(find_macro_invocations(&g.stream(), name));
        }
        i += 1;
    }
    out
}

/// Substitutes every `$param` in `body` with its matching argument's tokens,
/// recursing into nested groups (preserving their delimiter).
fn substitute_macro_body(
    body: &TokenStream,
    params: &[String],
    args: &[Vec<TokenTree>],
) -> TokenStream {
    let tts: Vec<TokenTree> = body.clone().into_iter().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < tts.len() {
        if let TokenTree::Punct(dollar) = &tts[i] {
            if dollar.as_char() == '$' {
                if let Some(TokenTree::Ident(name)) = tts.get(i + 1) {
                    if let Some(pos) = params.iter().position(|p| p == &name.to_string()) {
                        if let Some(replacement) = args.get(pos) {
                            out.extend(replacement.iter().cloned());
                            i += 2;
                            continue;
                        }
                    }
                }
            }
        }
        match &tts[i] {
            TokenTree::Group(g) => {
                let inner = substitute_macro_body(&g.stream(), params, args);
                let mut new_group = proc_macro2::Group::new(g.delimiter(), inner);
                new_group.set_span(g.span());
                out.push(TokenTree::Group(new_group));
            }
            other => out.push(other.clone()),
        }
        i += 1;
    }
    out.into_iter().collect()
}

/// Expands every invocation of every single-rule macro_rules! definition found in
/// `tokens`, returning each expansion's substituted token stream.
fn expand_simple_macros(tokens: &TokenStream) -> Vec<TokenStream> {
    let mut defs = HashMap::new();
    find_macro_rules_defs(tokens, &mut defs);
    let mut expansions = Vec::new();
    for (name, def) in &defs {
        for invocation_args in find_macro_invocations(tokens, name) {
            if invocation_args.len() == def.params.len() {
                expansions.push(substitute_macro_body(&def.body, &def.params, &invocation_args));
            }
        }
    }
    expansions
}

/// Parses every verus!/verus_code! block found in `content`. A block whose tokens
/// aren't valid standalone Verus syntax - notably a `macro_rules!` template body
/// containing metavariables like `$uN`, which are only valid inside the macro
/// definition itself (see std_specs/num.rs's `num_specs!` pattern) - fails to parse;
/// that failure is reported via `path` rather than silently dropped, since silently
/// under-counting targets would be worse than a text-based tool that (by accident,
/// since it never required valid syntax) doesn't have this blind spot at all.
fn parse_verus_blocks(path: &str, content: &str) -> Vec<File> {
    let mut blocks = Vec::new();
    let Ok(tokens) = content.parse::<TokenStream>() else {
        return blocks;
    };
    let mut raw_blocks = Vec::new();
    find_verus_blocks(tokens.clone(), &mut raw_blocks);
    // Also expand any single-rule macro_rules! (e.g. num_specs!) that wraps its own
    // verus! block behind metavariables, and search each expansion the same way.
    for expansion in expand_simple_macros(&tokens) {
        find_verus_blocks(expansion, &mut raw_blocks);
    }
    for raw in raw_blocks {
        let rejoined = verus_syn::rejoin_tokens(raw);
        match verus_syn::parse2::<File>(rejoined) {
            Ok(file) => blocks.push(file),
            Err(e) => {
                eprintln!("warning: {path}: failed to parse a verus!/verus_code! block: {e}");
            }
        }
    }
    blocks
}

fn collect_rs_files(root: &FsPath) -> Vec<PathBuf> {
    walkdir::WalkDir::new(root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .filter(|e| e.path().extension().is_some_and(|ext| ext == "rs"))
        .map(|e| e.path().to_path_buf())
        .collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <verus-source-root>", args[0]);
        std::process::exit(1);
    }
    let root = FsPath::new(&args[1]);
    let vstd_root = root.join("vstd");
    let test_root = root.join("rust_verify_test").join("tests");

    let mut targets: Vec<Target> = Vec::new();
    for path in collect_rs_files(&vstd_root) {
        let Ok(content) = std::fs::read_to_string(&path) else { continue };
        let rel = path.strip_prefix(root).unwrap_or(&path).display().to_string();
        for file in parse_verus_blocks(&rel, &content) {
            let mut collector = TargetCollector { file: rel.clone(), targets: Vec::new() };
            collector.visit_file(&file);
            targets.extend(collector.targets);
        }
    }

    let mut targets_by_name: HashMap<String, Vec<usize>> = HashMap::new();
    for (idx, t) in targets.iter().enumerate() {
        targets_by_name.entry(t.method_name.clone()).or_default().push(idx);
    }

    for path in collect_rs_files(&test_root) {
        let Ok(content) = std::fs::read_to_string(&path) else { continue };
        let rel = path.strip_prefix(root).unwrap_or(&path).display().to_string();
        for file in parse_verus_blocks(&rel, &content) {
            let mut scanner = CoverageScanner {
                file: rel.clone(),
                ghost_depth: 0,
                targets_by_name: &mut targets_by_name,
                targets: &mut targets,
                current_line_hint: 0,
            };
            scanner.visit_file(&file);
        }
    }

    let covered: Vec<&Target> = targets.iter().filter(|t| !t.covered_by.is_empty()).collect();
    let gaps: Vec<&Target> = targets.iter().filter(|t| t.covered_by.is_empty()).collect();

    println!("# allow_in_spec targets found in vstd: {}", targets.len());
    println!("# with at least one ghost-mode call site: {}", covered.len());
    println!(
        "# GAPS (no ghost-mode call site found - needs manual confirmation): {}\n",
        gaps.len()
    );

    println!("## GAPS");
    for t in &gaps {
        println!("  {}  ({}:{})", t.full_path, t.file, t.line);
    }

    println!("\n## Covered (first evidence site shown)");
    for t in &covered {
        println!("  {}  <- {}", t.full_path, t.covered_by[0]);
    }
}
