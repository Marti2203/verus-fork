//! EXPERIMENTAL. A real CFG + forward "may already be assigned" dataflow analysis
//! for the delayed-init reassignment check (see ast_simplify.rs's DelayedInitChecker
//! and issue #2865), instead of that module's branch-reset heuristic. This exists to
//! evaluate whether the extra rigor is worth it (see the discussion on PR #2867) - it
//! is NOT wired into the real pipeline.
//!
//! Unlike the heuristic, this correctly handles loops: a no-init/non-mut variable
//! reassigned on every loop iteration is a real violation, which the heuristic's
//! "reset to fresh on every loop-body entry" deliberately misses to avoid false
//! positives elsewhere. This CFG makes loops an explicit back-edge, so a proper
//! fixed-point dataflow pass naturally catches it.
//!
//! Scope: only local variables reachable via a `Place::Local` assignment target are
//! tracked. Closures are not treated as separate analysis units (their bodies are
//! walked inline, as if part of the surrounding straight-line code) - capturing and
//! mutating an outer no-init variable from within a closure is not specially modeled.
//! `let ... else { ... }` declarations are treated as if the `else` branch doesn't
//! exist. These are accepted simplifications for an experiment, not a claim of full
//! correctness.

use crate::ast::{
    ArmX, Expr, ExprX, Function, Pattern, PatternX, Place, PlaceX, Stmt, StmtX, VarIdent, VirErr,
};
use crate::ast_visitor::{AstVisitor, NoScoper};
use crate::def::user_local_name;
use crate::messages::{Span, error};
use crate::visitor::Walk;
use std::collections::{HashMap, HashSet};

type BlockId = usize;

enum Op {
    /// A declaration of `x` is (re-)executed here. Resets `x`'s "already assigned"
    /// tracking - crucial for a declaration inside a loop body: each iteration
    /// re-declares a fresh `x`, so an assignment from a *previous* iteration must
    /// not count as "already assigned" for *this* iteration's copy.
    Declare(VarIdent),
    /// An assignment to `x` is (re-)executed here.
    Assign(VarIdent, Span),
}

#[derive(Default)]
struct Block {
    /// In program order; the dataflow pass replays these against the block's
    /// (fixed-point-computed) entry state.
    ops: Vec<Op>,
    succs: Vec<BlockId>,
    /// True for the first block of an `if`/`match` branch: its entry state is
    /// always empty, regardless of what predecessors' exit states say. Branches
    /// are alternatives, not continuations - assigning once per branch (e.g.
    /// resolving a prophecy variable) is fine even if the path leading into the
    /// conditional already "used up" a variable's one free slot. Loop bodies do
    /// NOT get this treatment: a loop's back edge is the same path repeating, not
    /// an alternative, so a per-iteration reassignment is a real violation (see
    /// `Op::Declare` for why a loop's own re-declared locals still reset per
    /// iteration despite this).
    branch_start: bool,
}

struct CfgBuilder {
    blocks: Vec<Block>,
    /// No-initializer, non-`mut` local variables - the only ones this check cares
    /// about. Populated as declarations are encountered during the walk.
    eligible: HashSet<VarIdent>,
    /// Loop label id -> (break target, continue target).
    loop_targets: HashMap<usize, (BlockId, BlockId)>,
    /// The block execution continues in, or None if the current path is dead
    /// (a prior return/break/continue already left it).
    current: Option<BlockId>,
}

impl CfgBuilder {
    fn new() -> Self {
        CfgBuilder {
            blocks: Vec::new(),
            eligible: HashSet::new(),
            loop_targets: HashMap::new(),
            current: None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        self.blocks.push(Block::default());
        self.blocks.len() - 1
    }

    fn new_branch_block(&mut self) -> BlockId {
        self.blocks.push(Block { branch_start: true, ..Block::default() });
        self.blocks.len() - 1
    }

    fn add_succ(&mut self, from: BlockId, to: BlockId) {
        self.blocks[from].succs.push(to);
    }

    /// Registers eligible (no-init, non-`mut`) bindings in `pattern`, and emits a
    /// `Declare` op at block `at` for each one found, so the dataflow pass resets
    /// its "already assigned" tracking at this exact point (see `Op::Declare`).
    fn register_eligible_pattern(&mut self, pattern: &Pattern, has_init: bool, at: BlockId) {
        match &pattern.x {
            PatternX::Wildcard(_) | PatternX::Expr(_) | PatternX::Range(..) => {}
            PatternX::Var(b) => {
                if !has_init && b.user_mut == Some(false) {
                    self.eligible.insert(b.name.clone());
                    self.blocks[at].ops.push(Op::Declare(b.name.clone()));
                }
            }
            PatternX::Binding { binding, sub_pat } => {
                if !has_init && binding.user_mut == Some(false) {
                    self.eligible.insert(binding.name.clone());
                    self.blocks[at].ops.push(Op::Declare(binding.name.clone()));
                }
                self.register_eligible_pattern(sub_pat, has_init, at);
            }
            PatternX::Constructor(_, _, binders) => {
                for binder in binders.iter() {
                    self.register_eligible_pattern(&binder.a, has_init, at);
                }
            }
            PatternX::Or(pat1, pat2) => {
                self.register_eligible_pattern(pat1, has_init, at);
                self.register_eligible_pattern(pat2, has_init, at);
            }
            PatternX::MutRef(p) | PatternX::ImmutRef(p) => {
                self.register_eligible_pattern(p, has_init, at);
            }
        }
    }

    fn assign_target(place: &Place) -> Option<VarIdent> {
        if crate::ast_util::place_has_deref_mut(place) {
            return None;
        }
        let local = crate::ast_util::place_get_local(place)?;
        let PlaceX::Local(x) = &local.x else { unreachable!() };
        Some(x.clone())
    }
}

impl AstVisitor<Walk, VirErr, NoScoper> for CfgBuilder {
    fn visit_typ(&mut self, _typ: &crate::ast::Typ) -> Result<(), VirErr> {
        Ok(())
    }

    fn visit_place(&mut self, place: &Place) -> Result<(), VirErr> {
        // Places can embed expressions (PlaceX::Temporary/WithExpr, array indices)
        // that could themselves contain control flow - must recurse properly.
        self.visit_place_rec(place)
    }

    fn visit_pattern(&mut self, _pattern: &Pattern) -> Result<(), VirErr> {
        // Handled explicitly at StmtX::Decl and match-arm sites.
        Ok(())
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> Result<(), VirErr> {
        if self.current.is_none() {
            return Ok(());
        }
        match &stmt.x {
            StmtX::Decl { pattern, init, .. } => {
                // Visit the initializer first (it may itself embed control flow and
                // move `current`), then register/reset at wherever we land - the
                // binding only becomes valid after its initializer finishes.
                if let Some(p) = init {
                    self.visit_place(p)?;
                }
                if let Some(cur) = self.current {
                    self.register_eligible_pattern(pattern, init.is_some(), cur);
                }
                Ok(())
            }
            StmtX::Expr(_) => self.visit_stmt_rec(stmt),
        }
    }

    fn visit_expr(&mut self, expr: &Expr) -> Result<(), VirErr> {
        let Some(cur) = self.current else {
            return Ok(());
        };
        match &expr.x {
            ExprX::Assign { place, .. }
            | ExprX::BorrowMut(place)
            | ExprX::TwoPhaseBorrowMut(place)
            | ExprX::BorrowMutTracked(place) => {
                // Recurse first, in case the place embeds its own control flow (e.g.
                // an array index expression) - order matches evaluating the place
                // before performing the assignment. Re-fetch `current` afterward:
                // visiting the place may have created new blocks.
                self.visit_place(place)?;
                if let Some(cur) = self.current
                    && let Some(x) = Self::assign_target(place)
                    && self.eligible.contains(&x)
                {
                    self.blocks[cur].ops.push(Op::Assign(x, expr.span.clone()));
                }
                Ok(())
            }
            ExprX::If(cond, thn, els) => {
                self.visit_expr(cond)?;
                let Some(cur) = self.current else { return Ok(()) };

                let thn_start = self.new_branch_block();
                self.add_succ(cur, thn_start);
                self.current = Some(thn_start);
                self.visit_expr(thn)?;
                let thn_end = self.current;

                let els_end = if let Some(els) = els {
                    let els_start = self.new_branch_block();
                    self.add_succ(cur, els_start);
                    self.current = Some(els_start);
                    self.visit_expr(els)?;
                    self.current
                } else {
                    Some(cur)
                };

                self.current = match (thn_end, els_end) {
                    (None, None) => None,
                    (Some(a), None) => Some(a),
                    (None, Some(b)) => Some(b),
                    (Some(a), Some(b)) => {
                        let merge = self.new_block();
                        self.add_succ(a, merge);
                        self.add_succ(b, merge);
                        Some(merge)
                    }
                };
                Ok(())
            }
            ExprX::Match(_place, arms, _) => {
                let mut merge: Option<BlockId> = None;
                for arm in arms.iter() {
                    let ArmX { pattern: _, guard, body } = &arm.x;
                    let arm_start = self.new_branch_block();
                    self.add_succ(cur, arm_start);
                    self.current = Some(arm_start);
                    self.visit_expr(guard)?;
                    if self.current.is_some() {
                        self.visit_expr(body)?;
                    }
                    if let Some(end) = self.current {
                        let m = match merge {
                            Some(m) => m,
                            None => {
                                let m = self.new_block();
                                merge = Some(m);
                                m
                            }
                        };
                        self.add_succ(end, m);
                    }
                }
                self.current = merge;
                Ok(())
            }
            ExprX::Loop { label, cond, body, .. } => {
                let header = self.new_block();
                self.add_succ(cur, header);
                let after = self.new_block();
                self.loop_targets.insert(label.id, (after, header));

                self.current = Some(header);
                if let Some(c) = cond {
                    self.visit_expr(c)?;
                }
                let body_entry = self.current;
                if let Some(be) = body_entry {
                    self.add_succ(be, after); // loop may exit here (cond false / 0 iters)
                    let body_start = self.new_block();
                    self.add_succ(be, body_start);
                    self.current = Some(body_start);
                    self.visit_expr(body)?;
                    if let Some(body_end) = self.current {
                        self.add_succ(body_end, header); // back edge
                    }
                }

                self.loop_targets.remove(&label.id);
                self.current = Some(after);
                Ok(())
            }
            ExprX::BreakOrContinue { label, is_break } => {
                if let Some((break_b, continue_b)) = self.loop_targets.get(&label.id) {
                    let target = if *is_break { *break_b } else { *continue_b };
                    self.add_succ(cur, target);
                }
                self.current = None;
                Ok(())
            }
            ExprX::Return(e) => {
                if let Some(e) = e {
                    self.visit_expr(e)?;
                }
                self.current = None;
                Ok(())
            }
            _ => self.visit_expr_rec(expr),
        }
    }
}

pub fn check_delayed_init_reassignment_cfg(function: &Function) -> Result<(), VirErr> {
    let mut builder = CfgBuilder::new();
    let entry = builder.new_block();
    builder.current = Some(entry);
    builder.visit_function(function)?;

    let n = builder.blocks.len();
    // Predecessors, derived from the recorded successor edges.
    let mut preds: Vec<Vec<BlockId>> = vec![Vec::new(); n];
    for (b, block) in builder.blocks.iter().enumerate() {
        for &s in &block.succs {
            preds[s].push(b);
        }
    }

    // Fixed-point "may already be assigned" forward dataflow. Per variable, each
    // block's transfer function is either "pass through unchanged" (untouched by
    // this block) or "constant" (the last Declare/Assign op touching it in this
    // block decides, regardless of entry) - both monotonic, so simple iteration
    // to a fixed point still terminates despite Declare removing entries (unlike a
    // pure union-only lattice, this one isn't monotonically growing across
    // iterations, but each block's transfer function is monotonic in its input,
    // which is what convergence actually requires).
    let mut entry_sets: Vec<HashSet<VarIdent>> = vec![HashSet::new(); n];
    let block_exit = |entry: &HashSet<VarIdent>, block: &Block| -> HashSet<VarIdent> {
        let mut working = entry.clone();
        for op in &block.ops {
            match op {
                Op::Declare(x) => {
                    working.remove(x);
                }
                Op::Assign(x, _) => {
                    working.insert(x.clone());
                }
            }
        }
        working
    };
    loop {
        let mut changed = false;
        for b in 0..n {
            // A branch's entry is always empty, regardless of what predecessors say
            // (see `Block::branch_start`) - so there's nothing to recompute here.
            if builder.blocks[b].branch_start {
                continue;
            }
            let mut new_entry = HashSet::new();
            for &p in &preds[b] {
                let exit = block_exit(&entry_sets[p], &builder.blocks[p]);
                for x in exit {
                    new_entry.insert(x);
                }
            }
            if new_entry != entry_sets[b] {
                entry_sets[b] = new_entry;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    // Final reporting pass, using the converged entry sets.
    for b in 0..n {
        let mut working = entry_sets[b].clone();
        for op in &builder.blocks[b].ops {
            match op {
                Op::Declare(x) => {
                    working.remove(x);
                }
                Op::Assign(x, span) => {
                    if !working.insert(x.clone()) {
                        let name = user_local_name(x);
                        return Err(error(
                            span,
                            format!("variable `{name:}` is not marked mutable"),
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}
