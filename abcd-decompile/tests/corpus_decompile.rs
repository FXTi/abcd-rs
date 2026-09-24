//! Opt-in corpus gate for Stage B + emission v1 (d-P3,
//! design/decompile.md §7): decompile every function of every corpus
//! fixture to JS text.
//!
//! Assertions:
//!
//! - **Per-function success**: every function of every fixture
//!   decompiles (top-level + closures + class members). Zero panics —
//!   a panic anywhere fails the gate.
//! - **Determinism**: two independent `decompile_module` runs over the
//!   same module are byte-identical.
//! - **Fallback-comment histogram**: per-op fallback/elided comment
//!   counts, printed verbatim (the honesty volume).
//! - **Fold firing counts**: the desugar folds' firing counters plus
//!   the structurer's escape-hatch counters, printed verbatim.
//! - **Irreducible zero**: the d-P1 gate proved the corpus reducible;
//!   the state-machine fallback must fire ZERO times here.
//! - **node --check bonus sanity**: when `node` exists, a sample of
//!   outputs is syntax-checked (reported, non-fatal — d-P4 owns the
//!   full recompile gate).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-decompile --test corpus_decompile --release -- --ignored --nocapture
//! ```

mod common;

use std::collections::BTreeMap;

use abcd_analysis::dataflow::UseDefChains;
use abcd_decompile::emit::{DecompileStats, EmitOptions, consumed_functions, decompile_module};
use abcd_ir::{FuncId, Op};

/// Functions legitimately NOT emitted: their defining
/// `DefineFunc`/`DefineClass` op is dead — its result has no users, or
/// only `Mov`/`AllocClosure` passthrough users that are themselves
/// dead (dead-code elimination, not a drop).
fn dead_dropped_functions(module: &abcd_ir::Module) -> usize {
    let mut dead = std::collections::BTreeSet::new();
    for fi in 0..module.functions.len() {
        let func = FuncId::new(fi as u32);
        let chains = UseDefChains::build(module, func);
        let Some(f) = module.func(func) else {
            continue;
        };
        // A value is dead when every transitive user (through
        // Mov/AllocClosure passthroughs) is itself dead.
        let value_dead = |chains: &UseDefChains, v: abcd_ir::ValueId| -> bool {
            let mut stack = vec![v];
            let mut seen = std::collections::BTreeSet::new();
            while let Some(x) = stack.pop() {
                if !seen.insert(x) {
                    continue;
                }
                for user in chains.users_of(x) {
                    let Some(inst) = module.inst(*user) else {
                        return false;
                    };
                    match &inst.op {
                        Op::Mov { .. } | Op::AllocClosure { .. } => {
                            if let Some(r) = inst.result {
                                stack.push(r);
                            }
                        }
                        _ => return false,
                    }
                }
                // Phi users are real uses (the value flows on).
                if !chains.phi_users(x).is_empty() {
                    return false;
                }
            }
            true
        };
        for &b in &f.blocks {
            let Some(block) = module.block(b) else {
                continue;
            };
            for &iid in &block.insts {
                let Some(inst) = module.inst(iid) else {
                    continue;
                };
                let body = match &inst.op {
                    Op::DefineFunc { body, .. } => Some(*body),
                    Op::DefineClass { ctor, .. } | Op::DefineSendableClass { ctor, .. } => {
                        Some(*ctor)
                    }
                    _ => None,
                };
                if let (Some(body), Some(result)) = (body, inst.result)
                    && value_dead(&chains, result)
                {
                    dead.insert(body);
                }
            }
        }
    }
    dead.len()
}
use abcd_lift::lift_file;

/// The node --check sample size (first N fixtures, manifest order).
const NODE_SAMPLE: usize = 40;

fn merge_stats(a: &mut DecompileStats, b: &DecompileStats) {
    a.functions += b.functions;
    a.functions_with_fallbacks += b.functions_with_fallbacks;
    for (op, n) in &b.fallback_comments {
        *a.fallback_comments.entry(op).or_insert(0) += n;
    }
    for (op, n) in &b.elided_comments {
        *a.elided_comments.entry(op).or_insert(0) += n;
    }
    a.classes += b.classes;
    a.class_methods += b.class_methods;
    a.closures += b.closures;
    a.structure.ifs += b.structure.ifs;
    a.structure.loops_while += b.structure.loops_while;
    a.structure.loops_do_while += b.structure.loops_do_while;
    a.structure.loops_while_true += b.structure.loops_while_true;
    a.structure.labeled_exits += b.structure.labeled_exits;
    a.structure.alternates += b.structure.alternates;
    a.structure.irreducible_fallbacks += b.structure.irreducible_fallbacks;
    a.structure.state_machine_blocks += b.structure.state_machine_blocks;
    a.structure.try_catches += b.structure.try_catches;
    a.structure.try_cuts += b.structure.try_cuts;
    a.structure.try_splits += b.structure.try_splits;
    a.structure.multi_catch += b.structure.multi_catch;
    a.structure.handler_shims += b.structure.handler_shims;
    a.structure.try_join_hoists += b.structure.try_join_hoists;
    a.structure.exit_phi_after_loop += b.structure.exit_phi_after_loop;
    a.structure.cross_arm_notes += b.structure.cross_arm_notes;
    a.structure.cross_arm_folds += b.structure.cross_arm_folds;
    a.structure.cross_arm_dup_blocks += b.structure.cross_arm_dup_blocks;
    a.structure.break_target_notes += b.structure.break_target_notes;
    a.folds.for_of += b.folds.for_of;
    a.folds.for_await_of += b.folds.for_await_of;
    a.folds.for_in += b.folds.for_in;
    a.folds.object_lit += b.folds.object_lit;
    a.folds.array_lit += b.folds.array_lit;
    a.folds.rest += b.folds.rest;
    a.folds.switch += b.folds.switch;
    a.folds.finally_fold += b.folds.finally_fold;
    a.folds.scope_fold += b.folds.scope_fold;
    a.folds.gen_driver_sites += b.folds.gen_driver_sites;
    a.folds.gen_driver_entry += b.folds.gen_driver_entry;
    a.folds.gen_driver_bound += b.folds.gen_driver_bound;
    a.folds.async_driver += b.folds.async_driver;
    a.folds.async_machine_sites += b.folds.async_machine_sites;
    a.folds.async_machine_bound += b.folds.async_machine_bound;
    a.folds.agen_entry += b.folds.agen_entry;
    a.folds.agen_yields += b.folds.agen_yields;
    a.folds.agen_bound += b.folds.agen_bound;
    a.folds.agen_awaits += b.folds.agen_awaits;
    a.folds.agen_await_bound += b.folds.agen_await_bound;
    a.folds.agen_returns += b.folds.agen_returns;
    a.function_bodies += b.function_bodies;
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_decompile_gate() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut stats = DecompileStats::default();
    let mut fixtures = 0usize;
    let mut functions_total = 0usize;
    let mut bytes = 0usize;
    let mut dead_total = 0usize;
    let mut node_outputs: Vec<(String, String)> = Vec::new();
    let mut ts_outputs: Vec<(String, String)> = Vec::new();

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;
        functions_total += module.functions.len();

        // Determinism: two independent runs are byte-identical.
        let d1 = decompile_module(&module, &EmitOptions::default());
        let d2 = decompile_module(&module, &EmitOptions::default());
        assert_eq!(d1.text, d2.text, "non-deterministic output in {relative}");
        bytes += d1.text.len();
        if node_outputs.len() < NODE_SAMPLE {
            node_outputs.push((relative.clone(), d1.text.clone()));
        }
        // The d-P8 `--ts` flag: signatures survive only on ≤11-format
        // files (fact #A7) — collect a TS sample from those.
        if ts_outputs.len() < NODE_SAMPLE
            && (relative.starts_with("9.0.0.0/") || relative.starts_with("11.0.2.0/"))
        {
            let ts = decompile_module(
                &module,
                &EmitOptions {
                    ts: true,
                    ..Default::default()
                },
            );
            ts_outputs.push((relative.clone(), ts.text));
        }
        // Per-function coverage: every function is either emitted or
        // dead-dropped (its defining op is itself dead) — nothing is
        // silently dropped.
        let _ = consumed_functions(&module);
        let dead = dead_dropped_functions(&module);
        dead_total += dead;
        assert!(
            d1.stats.function_bodies + dead >= module.functions.len(),
            "function bodies emitted ({}) + dead-dropped ({dead}) < functions ({}) in {relative}",
            d1.stats.function_bodies,
            module.functions.len(),
        );
        merge_stats(&mut stats, &d1.stats);
    }

    eprintln!("DECOMPILE-GATE fixtures={fixtures} functions_total={functions_total}");
    eprintln!(
        "DECOMPILE-GATE function_bodies={} (top={} closures={} class_methods={}) classes={}",
        stats.function_bodies, stats.functions, stats.closures, stats.class_methods, stats.classes
    );
    eprintln!("DECOMPILE-GATE output_bytes={bytes} dead_dropped_functions={dead_total}");
    eprintln!(
        "DECOMPILE-GATE functions_with_fallbacks={}",
        stats.functions_with_fallbacks
    );

    eprintln!(
        "FOLDS for_of={} for_await_of={} for_in={} object_lit={} array_lit={} rest={} switch={} finally_fold={} scope_fold={} gen_driver_sites={} gen_driver_entry={} gen_driver_bound={} async_driver={} async_machine_sites={} async_machine_bound={} agen_entry={} agen_yields={} agen_bound={} agen_awaits={} agen_await_bound={} agen_returns={} yield_star_sites={} yield_star_bound={} dead_exit_throw={}",
        stats.folds.for_of,
        stats.folds.for_await_of,
        stats.folds.for_in,
        stats.folds.object_lit,
        stats.folds.array_lit,
        stats.folds.rest,
        stats.folds.switch,
        stats.folds.finally_fold,
        stats.folds.scope_fold,
        stats.folds.gen_driver_sites,
        stats.folds.gen_driver_entry,
        stats.folds.gen_driver_bound,
        stats.folds.async_driver,
        stats.folds.async_machine_sites,
        stats.folds.async_machine_bound,
        stats.folds.agen_entry,
        stats.folds.agen_yields,
        stats.folds.agen_bound,
        stats.folds.agen_awaits,
        stats.folds.agen_await_bound,
        stats.folds.agen_returns,
        stats.folds.yield_star_sites,
        stats.folds.yield_star_bound,
        stats.folds.dead_exit_throw
    );
    eprintln!(
        "STRUCT ifs={} while={} do_while={} while_true={} labeled_exits={} alternates={}",
        stats.structure.ifs,
        stats.structure.loops_while,
        stats.structure.loops_do_while,
        stats.structure.loops_while_true,
        stats.structure.labeled_exits,
        stats.structure.alternates
    );
    eprintln!(
        "STRUCT try_catches={} try_cuts={} try_splits={} multi_catch={} handler_shims={} try_join_hoists={} exit_phi_after_loop={}",
        stats.structure.try_catches,
        stats.structure.try_cuts,
        stats.structure.try_splits,
        stats.structure.multi_catch,
        stats.structure.handler_shims,
        stats.structure.try_join_hoists,
        stats.structure.exit_phi_after_loop
    );
    eprintln!(
        "STRUCT irreducible_fallbacks={} state_machine_blocks={} cross_arm_notes={} cross_arm_folds={} cross_arm_dup_blocks={} break_target_notes={}",
        stats.structure.irreducible_fallbacks,
        stats.structure.state_machine_blocks,
        stats.structure.cross_arm_notes,
        stats.structure.cross_arm_folds,
        stats.structure.cross_arm_dup_blocks,
        stats.structure.break_target_notes
    );

    eprintln!("FALLBACK-COMMENT histogram (op=count):");
    for (op, n) in &stats.fallback_comments {
        eprintln!("FALLBACK {op} = {n}");
    }
    eprintln!("ELIDED-COMMENT histogram (op=count):");
    for (op, n) in &stats.elided_comments {
        eprintln!("ELIDED {op} = {n}");
    }

    // The d-P1 gate proved the corpus reducible: the escape hatch must
    // stay silent here.
    assert_eq!(
        stats.structure.irreducible_fallbacks, 0,
        "irreducible fallback fired on the reducible corpus"
    );

    // Bonus sanity: node --check on the sample (reported, non-fatal).
    let node = std::process::Command::new("which")
        .arg("node")
        .output()
        .ok()
        .filter(|o| o.status.success());
    match node {
        None => eprintln!(
            "NODE-CHECK node not found on this host — skipped (d-P4 owns the recompile gate)"
        ),
        Some(which) => {
            let node_path = String::from_utf8_lossy(&which.stdout).trim().to_string();
            eprintln!("NODE-CHECK using {node_path}");
            let dir = std::env::temp_dir().join("abcd-dp3-nodecheck");
            std::fs::create_dir_all(&dir).expect("tempdir");
            let mut ok = 0usize;
            let mut bad: Vec<String> = Vec::new();
            for (rel, text) in &node_outputs {
                let out = dir.join("out.js");
                std::fs::write(&out, text).expect("write sample");
                let check = std::process::Command::new(&node_path)
                    .arg("--check")
                    .arg(&out)
                    .output()
                    .expect("run node --check");
                if check.status.success() {
                    ok += 1;
                } else {
                    bad.push(format!(
                        "{rel}: {}",
                        String::from_utf8_lossy(&check.stderr)
                            .lines()
                            .nth(1)
                            .unwrap_or("?")
                    ));
                }
            }
            eprintln!(
                "NODE-CHECK ok={ok} bad={} of {}",
                bad.len(),
                node_outputs.len()
            );
            for b in &bad {
                eprintln!("NODE-CHECK-FAIL {b}");
            }
            // The d-P8 TS sample: `node --check` does not parse TS, so
            // validity is proven through node's own type-stripping API
            // (`node:module.stripTypeScriptTypes` — the annotations are
            // erasable by construction) plus a `vm.Script` parse of the
            // stripped output. Reported, non-fatal.
            if !ts_outputs.is_empty() {
                let mut ok = 0usize;
                let mut bad: Vec<String> = Vec::new();
                let probe = dir.join("ts-probe.mjs");
                std::fs::write(
                    &probe,
                    "import { stripTypeScriptTypes } from 'node:module';\n\
                     import { Script } from 'node:vm';\n\
                     import { readFileSync } from 'node:fs';\n\
                     const src = readFileSync(process.argv[2], 'utf8');\n\
                     const js = stripTypeScriptTypes(src, { mode: 'strip' });\n\
                     new Script(js);\n",
                )
                .expect("write ts probe");
                for (rel, text) in &ts_outputs {
                    let out = dir.join("out.ts");
                    std::fs::write(&out, text).expect("write ts sample");
                    let check = std::process::Command::new(&node_path)
                        .arg(&probe)
                        .arg(&out)
                        .output()
                        .expect("run ts probe");
                    if check.status.success() {
                        ok += 1;
                    } else {
                        bad.push(format!(
                            "{rel}: {}",
                            String::from_utf8_lossy(&check.stderr)
                                .lines()
                                .next()
                                .unwrap_or("?")
                        ));
                    }
                }
                eprintln!("TS-CHECK ok={ok} bad={} of {}", bad.len(), ts_outputs.len());
                for b in &bad {
                    eprintln!("TS-CHECK-FAIL {b}");
                }
            }
        }
    }
    let _ = BTreeMap::<&str, usize>::new();
}
