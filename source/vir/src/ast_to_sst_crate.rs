use crate::ast::{Fun, Function, Krate, VirErr};
use crate::ast_to_sst_func::function_to_sst;
use crate::context::Ctx;
use crate::sst::{FunctionSst, KrateSst, KrateSstX};
use crate::sst_elaborate::{
    elaborate_function_bv, elaborate_function_rewrite_recursive, elaborate_function1,
};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub fn ast_to_sst_krate(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    bucket_funs: &HashSet<Fun>,
    krate: &Krate,
    compute_only_functions: &HashMap<Fun, Function>,
) -> Result<KrateSst, VirErr> {
    let mut func_workmap: HashMap<Fun, FunctionSst> = HashMap::new();
    for function in krate.functions.iter() {
        let vis = function.x.visibility.clone();
        let module = ctx.module_path();
        if !crate::ast_util::is_visible_to(&vis, &module) || function.x.attrs.is_decrease_by {
            continue;
        }

        let function_sst = function_to_sst(ctx, diagnostics, bucket_funs, function)?;

        assert!(!func_workmap.contains_key(&function.x.name));
        func_workmap.insert(function.x.name.clone(), function_sst);
    }

    let mut sst_infos: HashMap<Fun, FunctionSst> = HashMap::new();
    let mut functions: Vec<FunctionSst> = Vec::new();
    for scc_rep in ctx.global.func_call_sccs.iter() {
        let mut scc_functions: Vec<FunctionSst> = Vec::new();
        for node in ctx.global.func_call_graph.get_scc_nodes(&scc_rep) {
            if let crate::recursion::Node::Fun(f) = &node {
                if let Some(mut func_sst) = func_workmap.remove(f) {
                    elaborate_function1(ctx, diagnostics, &sst_infos, &mut func_sst)?;
                    scc_functions.push(func_sst);
                }
            }
        }
        for func_sst in scc_functions.into_iter() {
            if func_sst.x.axioms.spec_axioms.is_some() {
                assert!(!sst_infos.contains_key(&func_sst.x.name));
                sst_infos.insert(func_sst.x.name.clone(), func_sst.clone());
            }
            functions.push(func_sst.clone());
        }
    }
    assert!(func_workmap.len() == 0);

    // Give the interpreter its own, correctly-elaborated view of functions needed
    // only by a `by (compute)` assertion (see prune.rs's functions_reachable_for_compute).
    // Elaborated with the same SCC ordering as everything above (so they may reference
    // the normal functions above, and each other, and get their own nested compute
    // asserts elaborated correctly) - but deliberately never published into
    // `functions`/ctx.func_sst_map, so their axioms never reach the shared bucket-wide
    // AIR context every other, unrelated query in this bucket draws from.
    let mut compute_workmap: HashMap<Fun, FunctionSst> = HashMap::new();
    for (name, function) in compute_only_functions.iter() {
        if !sst_infos.contains_key(name) {
            let function_sst = function_to_sst(ctx, diagnostics, bucket_funs, function)?;
            compute_workmap.insert(name.clone(), function_sst);
        }
    }
    let mut compute_sst_infos: HashMap<Fun, FunctionSst> = sst_infos.clone();
    let mut compute_functions: Vec<FunctionSst> = Vec::new();
    for scc_rep in ctx.global.func_call_sccs.iter() {
        let mut scc_functions: Vec<FunctionSst> = Vec::new();
        for node in ctx.global.func_call_graph.get_scc_nodes(&scc_rep) {
            if let crate::recursion::Node::Fun(f) = &node {
                if let Some(mut func_sst) = compute_workmap.remove(f) {
                    elaborate_function1(ctx, diagnostics, &compute_sst_infos, &mut func_sst)?;
                    scc_functions.push(func_sst);
                }
            }
        }
        for func_sst in scc_functions.into_iter() {
            if func_sst.x.axioms.spec_axioms.is_some() {
                compute_sst_infos.insert(func_sst.x.name.clone(), func_sst.clone());
            }
            compute_functions.push(func_sst);
        }
    }
    assert!(compute_workmap.len() == 0);

    let sst_map = Arc::new(compute_sst_infos);
    for func_sst in &mut functions {
        elaborate_function_rewrite_recursive(ctx, diagnostics, sst_map.clone(), func_sst)?;
        elaborate_function_bv(ctx, sst_map.clone(), func_sst)?;

        assert!(!ctx.func_sst_map.contains_key(&func_sst.x.name));
        ctx.func_sst_map.insert(func_sst.x.name.clone(), func_sst.clone());
    }
    for func_sst in &mut compute_functions {
        elaborate_function_rewrite_recursive(ctx, diagnostics, sst_map.clone(), func_sst)?;
        elaborate_function_bv(ctx, sst_map.clone(), func_sst)?;
        // Deliberately not inserted into ctx.func_sst_map / krate_sst.functions.
    }

    let krate_sst = Arc::new(KrateSstX {
        functions,
        datatypes: krate.datatypes.clone(),
        opaque_types: krate.opaque_types.clone(),
        traits: krate.traits.clone(),
        trait_impls: krate.trait_impls.clone(),
        assoc_type_impls: krate.assoc_type_impls.clone(),
        reveal_groups: krate.reveal_groups.clone(),
    });
    Ok(krate_sst)
}
