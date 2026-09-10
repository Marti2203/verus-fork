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
//! Still a triage tool, not a certifier. Matching is by bare method/last-path-segment
//! name; when several targets share one name (e.g. std HashMap's `Entry::key`/
//! `OccupiedEntry::key`/`VacantEntry::key`), a UFCS call (`Type::method(...)`)
//! disambiguates by its own explicit qualifier, and a method call disambiguates by
//! the receiver's locally-known type - a fn parameter or explicitly-typed `let`
//! annotation, `self` inside an impl block, or a literal's own implied type (`'a'`
//! is `char`, `5u8` is `u8`). A method call whose receiver's type *isn't*
//! resolvable this way is credited to **nothing**, even when only one vstd target
//! shares that name - not just when several do. That single-candidate case looked
//! safe in theory but wasn't in practice: before this rule, `str::is_empty`'s only
//! "evidence" in the whole corpus turned out to be calls on a `Set`/mask value and
//! on an unrelated `&[T]` slice, never an actual `str`. False positives (crediting
//! the wrong target) matter more to avoid here than false negatives (missing real
//! coverage this tool can't see), so an unresolvable call counts as no evidence at
//! all, full stop. This is still not full type inference (no tracking of a method
//! chain's return type, no generic instantiation) - closing the remaining gap for
//! real needs the compiler's own type information (checking the elaborated SST for
//! a genuine `ExpX::Call` to the exact target `Fun`), which this tool doesn't have.
//!
//! One further, structural limitation from the same root cause (no real name
//! resolution against actual declarations, only string matching on names): a test
//! file defining its own local type or function that happens to share a name with a
//! vstd target (e.g. a test-local `struct Entry { fn key(&self)... }`) would be
//! silently credited as coverage for the real vstd target. Confirmed no such
//! collision exists in the corpus *today* for the specific names this tool
//! currently disambiguates, but that is not something the tool itself checks or
//! enforces going forward.
//!
//! (The type scope used to be per-function rather than per-block, which could have
//! let a shadowing `let` in one nested block leak its type into a later sibling
//! block - fixed by giving every `{ ... }` its own scope via `visit_block`, not
//! just function bodies.)
//!
//! Every GAP this reports still needs the same manual fail-without/pass-with-fix
//! confirmation used for the char::len_utf8/is_whitespace case (PR #2919) before
//! being treated as a real bug.
//!
//! Known limitation: a `verus!`/`verus_code!` block is parsed *in isolation* (its
//! raw tokens, re-tokenized and parsed as a standalone item list) - a file whose
//! `verus!` body sits inside a `macro_rules!` template using metavariables like `$uN`
//! is invalid standalone syntax outside the macro definition itself, and fails to
//! parse on its own. `expand_simple_macros` below recovers exactly one shape of this:
//! a **single-rule, non-repetition** macro_rules! (no `$(...)* `) - simple positional
//! substitution of each `$param` with its matching invocation argument. This is
//! `std_specs/num.rs`'s `num_specs!` pattern exactly (one rule, seven plain
//! metavariables, six invocations - the wrapping/checked/saturating arithmetic family
//! for every integer type), and recovers all 192 of its targets.
//!
//! It is *not* a general macro_rules! expander: a multi-rule macro (more than one
//! `=>` arm) or one using repetition is not expanded, and any `allow_in_spec` target
//! defined inside one would not even appear in the target count - not listed as a
//! gap, simply invisible. Confirmed today that no *other* vstd file whose verus!
//! block currently fails to parse this way (bits.rs, atomic_ghost.rs, std_specs/
//! {ops,cmp,atomic,convert,default,range}.rs, arithmetic/overflow.rs, wrapping.rs -
//! all multi-rule or repetition-based) actually defines any allow_in_spec target, so
//! this costs nothing *today*; that is a fact about vstd's current contents, not a
//! guarantee this tool enforces, and could silently start missing something if one
//! of those files ever grows an allow_in_spec target of its own. Parse failures are
//! reported on stderr rather than silently dropped, but only failures the tool
//! attempts and fails - nothing announces a macro shape it never tried to expand at
//! all. `tools/line_count` hits the identical isolation-parsing wall on num.rs before
//! the substitution below runs on it (`line_count vstd/std_specs/num.rs` reports 519
//! of ~528 lines "unaccounted") - this is an accepted limitation of parsing a verus!
//! block in isolation in this codebase's own tooling generally, not a mistake unique
//! to this tool.
//!
//! Usage: spec_usage_coverage <verus-source-root>

use std::collections::HashMap;
use std::path::{Path as FsPath, PathBuf};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use verus_syn::spanned::Spanned;
use verus_syn::visit::{self, Visit};
use verus_syn::{
    Assert, AssumeSpecification, Block, Expr, ExprCall, ExprMethodCall, File, FnArgKind, FnMode,
    ImplItemFn, ItemFn, ItemImpl, Lit, Local, Pat, Path, Signature, SignatureSpec, TraitItemFn,
    Type,
};

fn line_of<T: Spanned>(node: &T) -> usize {
    node.span().start().line
}

/// The leading type name a value's declared type resolves to, stripping references
/// and parens - `&u8` and `u8` both give `Some("u8")`. `[T]`/`&[T]` (any element)
/// normalize to the synthetic marker `"[]"`, matching how `<[T]>::len`'s own qself
/// is resolved below - `<[T]>::len` is generic over the element type, so any slice
/// receiver is the right kind of match regardless of what it holds. `None` for
/// shapes with no single leading name (tuples, arrays, etc.) - not needed for the
/// cases this tool disambiguates today.
fn type_head(ty: &Type) -> Option<String> {
    match ty {
        Type::Path(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        Type::Reference(r) => type_head(&r.elem),
        Type::Paren(p) => type_head(&p.elem),
        Type::Group(g) => type_head(&g.elem),
        Type::Slice(_) => Some("[]".to_string()),
        _ => None,
    }
}

/// The type a literal expression's own syntax implies - `'a'` is unambiguously
/// `char`, `"s"` is `str` (the `&` is implicit at the reference-stripping level
/// `type_head` already does for declared types), a suffixed number like `5u8`
/// names its own type. An unsuffixed number's type is inferred from context, which
/// this tool doesn't track, so it stays unresolved rather than guessed.
fn literal_type_head(lit: &Lit) -> Option<String> {
    match lit {
        Lit::Char(_) => Some("char".to_string()),
        Lit::Str(_) => Some("str".to_string()),
        Lit::Int(i) if !i.suffix().is_empty() => Some(i.suffix().to_string()),
        Lit::Float(f) if !f.suffix().is_empty() => Some(f.suffix().to_string()),
        _ => None,
    }
}

#[derive(Clone)]
struct Target {
    method_name: String,
    full_path: String,
    /// The type this method/spec belongs to (e.g. "u8" for `<u8>::wrapping_add`,
    /// "Entry" for `Entry::key`), when known. `None` for free functions.
    owning_type: Option<String>,
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

// ---- Pass 1: collect allow_in_spec targets from vstd ----

struct TargetCollector {
    file: String,
    targets: Vec<Target>,
    /// The Self type of the impl block currently being visited, if any.
    current_impl_self_type: Option<String>,
}

impl TargetCollector {
    fn record(
        &mut self,
        attrs: &[verus_syn::Attribute],
        full_path: String,
        method_name: String,
        owning_type: Option<String>,
        line: usize,
    ) {
        if has_allow_in_spec(attrs) {
            self.targets.push(Target {
                method_name,
                full_path,
                owning_type,
                file: self.file.clone(),
                line,
                covered_by: Vec::new(),
            });
        }
    }
}

impl<'ast> Visit<'ast> for TargetCollector {
    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        // A free function (not inside an impl block) has no owning type.
        self.record(&i.attrs, i.sig.ident.to_string(), i.sig.ident.to_string(), None, line_of(i));
        visit::visit_item_fn(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast ItemImpl) {
        let prev = self.current_impl_self_type.take();
        self.current_impl_self_type = type_head(&i.self_ty);
        visit::visit_item_impl(self, i);
        self.current_impl_self_type = prev;
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        self.record(
            &i.attrs,
            i.sig.ident.to_string(),
            i.sig.ident.to_string(),
            self.current_impl_self_type.clone(),
            line_of(i),
        );
        visit::visit_impl_item_fn(self, i);
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        self.record(&i.attrs, i.sig.ident.to_string(), i.sig.ident.to_string(), None, line_of(i));
        visit::visit_trait_item_fn(self, i);
    }

    fn visit_assume_specification(&mut self, i: &'ast AssumeSpecification) {
        // `<[T]>::len`-style paths put `[T]` in `qself`, leaving just `::len` in
        // `path` - render both together so the reported target is readable, and use
        // qself's type as the owning type when present.
        let (qualifier, name) = last_two_segments(&i.path);
        let owning_type = match &i.qself {
            Some(q) => type_head(&q.ty),
            None => qualifier,
        };
        let full = match &i.qself {
            Some(q) => format!("<{}>{}", q.ty.to_token_stream(), i.path.to_token_stream()),
            None => i.path.to_token_stream().to_string(),
        };
        self.record(&i.attrs, full, name, owning_type, line_of(i));
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
    /// Stack of scopes mapping a locally-declared variable to its known type head
    /// (fn parameters, explicitly-typed `let` bindings, `self`). Innermost scope last.
    type_scopes: Vec<HashMap<String, String>>,
    /// The Self type of the impl block currently being visited, if any - used to
    /// resolve `self.method()` receivers inside its methods.
    current_impl_self_type: Option<String>,
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

    /// Credits `name` only to targets whose owning type matches `receiver_type`.
    fn record_hit_for_type(&mut self, name: &str, receiver_type: &str) {
        if let Some(indices) = self.targets_by_name.get(name) {
            let evidence = format!("{}:{}", self.file, self.current_line_hint);
            for &idx in indices {
                if self.targets[idx].owning_type.as_deref() == Some(receiver_type) {
                    self.targets[idx].covered_by.push(evidence.clone());
                }
            }
        }
    }

    fn lookup_var_type(&self, name: &str) -> Option<&str> {
        self.type_scopes.iter().rev().find_map(|scope| scope.get(name)).map(|s| s.as_str())
    }

    fn push_scope(&mut self) {
        self.type_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.type_scopes.pop();
    }

    fn declare(&mut self, name: String, ty: &Type) {
        if let Some(head) = type_head(ty) {
            self.type_scopes.last_mut().expect("a scope is always active").insert(name, head);
        }
    }

    fn declare_params(&mut self, sig: &Signature) {
        for arg in sig.inputs.iter() {
            match &arg.kind {
                FnArgKind::Typed(pat_type) => {
                    if let Pat::Ident(pi) = &*pat_type.pat {
                        self.declare(pi.ident.to_string(), &pat_type.ty);
                    }
                }
                // `self`'s type is the enclosing impl block's Self type, not
                // syntactically present on the receiver itself.
                FnArgKind::Receiver(_) => {
                    if let Some(ty) = self.current_impl_self_type.clone() {
                        self.type_scopes
                            .last_mut()
                            .expect("a scope is always active")
                            .insert("self".to_string(), ty);
                    }
                }
            }
        }
    }

    /// How many *distinct* owning types (None counts as one) the candidates for
    /// `name` span - 1 means unambiguous regardless of receiver type.
    fn distinct_owning_types(&self, name: &str) -> usize {
        let Some(indices) = self.targets_by_name.get(name) else { return 0 };
        let mut seen: Vec<Option<&str>> = Vec::new();
        for &idx in indices {
            let ty = self.targets[idx].owning_type.as_deref();
            if !seen.contains(&ty) {
                seen.push(ty);
            }
        }
        seen.len()
    }
}

impl<'a, 'ast> Visit<'ast> for CoverageScanner<'a> {
    fn visit_item_impl(&mut self, i: &'ast ItemImpl) {
        let prev = self.current_impl_self_type.take();
        self.current_impl_self_type = type_head(&i.self_ty);
        visit::visit_item_impl(self, i);
        self.current_impl_self_type = prev;
    }

    fn visit_item_fn(&mut self, i: &'ast ItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        self.push_scope();
        self.declare_params(&i.sig);
        visit::visit_item_fn(self, i);
        self.pop_scope();
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    fn visit_impl_item_fn(&mut self, i: &'ast ImplItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        self.push_scope();
        self.declare_params(&i.sig);
        visit::visit_impl_item_fn(self, i);
        self.pop_scope();
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    fn visit_trait_item_fn(&mut self, i: &'ast TraitItemFn) {
        let ghost = is_ghost_mode(&i.sig.mode);
        if ghost {
            self.ghost_depth += 1;
        }
        self.push_scope();
        self.declare_params(&i.sig);
        visit::visit_trait_item_fn(self, i);
        self.pop_scope();
        if ghost {
            self.ghost_depth -= 1;
        }
    }

    fn visit_local(&mut self, i: &'ast Local) {
        if let Pat::Type(pt) = &i.pat {
            if let Pat::Ident(pi) = &*pt.pat {
                self.declare(pi.ident.to_string(), &pt.ty);
            }
        }
        visit::visit_local(self, i);
    }

    // Every `{ ... }` block gets its own scope, not just function bodies - a `let`
    // in one nested block must not leak its type into a later sibling block. The
    // function-level push in visit_item_fn/visit_impl_item_fn/visit_trait_item_fn
    // still holds the params; this adds one (harmlessly redundant, for the fn's own
    // top-level block) or more (for real nesting) layers on top.
    fn visit_block(&mut self, i: &'ast Block) {
        self.push_scope();
        visit::visit_block(self, i);
        self.pop_scope();
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
                self.current_line_hint = line_of(i);
                match &qualifier {
                    // A UFCS call names its type explicitly - credit only that exact
                    // type's target, never every same-named target (e.g.
                    // `i32::checked_div(x, y)` must not also credit i8/i16/.../isize).
                    // An internal per-type helper module like `u32_specs` (see
                    // std_specs/num.rs's own "Put in separate module to avoid name
                    // collisions" comment) needs no special-casing here: no real
                    // target's owning_type is ever a module name like "u32_specs",
                    // so record_hit_for_type's exact match already excludes it.
                    Some(q) => self.record_hit_for_type(&name, q),
                    None if self.distinct_owning_types(&name) <= 1 => self.record_hit(&name),
                    None => {}
                }
            }
        }
        visit::visit_expr_call(self, i);
    }

    fn visit_expr_method_call(&mut self, i: &'ast ExprMethodCall) {
        if self.ghost_depth > 0 {
            let name = i.method.to_string();
            self.current_line_hint = line_of(i);
            let receiver_type = match &*i.receiver {
                Expr::Path(p) if p.path.segments.len() == 1 => self
                    .lookup_var_type(&p.path.segments[0].ident.to_string())
                    .map(|s| s.to_string()),
                Expr::Lit(l) => literal_type_head(&l.lit),
                _ => None,
            };
            // Unlike UFCS/bare calls, a method call's dispatch genuinely depends on
            // the receiver's runtime type, which any two vstd types could share a
            // method name over - so, no exception for "only one vstd candidate"
            // here: an unresolved receiver credits nothing, full stop. Confirmed
            // this matters in practice, not just in theory: str::is_empty's only
            // in-corpus "evidence" before this rule turned out to be a Set/mask
            // value and an unrelated slice, never an actual str.
            if let Some(ty) = receiver_type {
                self.record_hit_for_type(&name, &ty);
            }
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
            let mut collector = TargetCollector {
                file: rel.clone(),
                targets: Vec::new(),
                current_impl_self_type: None,
            };
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
                type_scopes: Vec::new(),
                current_impl_self_type: None,
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
