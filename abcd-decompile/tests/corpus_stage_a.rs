//! Opt-in corpus gate for Stage A expression recovery (d-P2,
//! design/decompile.md §7): run [`abcd_decompile::recover_func`] + the
//! debug dump over every function of every corpus fixture.
//!
//! Assertions:
//!
//! - **Coverage histogram**: per-op outcome counts (expressed / plumbing
//!   / elided / fallback / dead-pure) keyed by the §5 fitness table,
//!   printed verbatim; every instruction gets exactly one outcome.
//! - **The hard 7**: `IteratorReturn`, `IteratorThrow`,
//!   `DefineSendableClass`, `ResumeGenerator`, `GetResumeMode`,
//!   `AsyncResolve`, `AsyncReject` MUST land as documented fallbacks
//!   (fallback + dead-pure only) — no silent expression.
//! - **No unexpected fallbacks**: ops OUTSIDE the hard-7 (and the
//!   documented `ThrowDeleteSuperProperty` N-class fallback) must never
//!   hit a fallback outcome.
//! - **Determinism**: two independent `dump_module` runs over the same
//!   module are byte-identical.
//! - **Zero panics**: the whole corpus runs to completion.
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-decompile --test corpus_stage_a --release -- --ignored --nocapture
//! ```

mod common;

use std::collections::BTreeMap;

use abcd_decompile::dump::dump_module;
use abcd_decompile::fitness::Fitness;
use abcd_decompile::recover::{OpStat, Outcome, recover_func};
use abcd_ir::FuncId;
use abcd_lift::lift_file;

/// Ops whose fallback outcome is DOCUMENTED (the §5 hard 7 + the
/// N-class `ThrowDeleteSuperProperty`, whose member expression the op
/// does not carry).
const DOCUMENTED_FALLBACK_OPS: &[&str] = &[
    "IteratorReturn",
    "IteratorThrow",
    "DefineSendableClass",
    "ResumeGenerator",
    "GetResumeMode",
    "AsyncResolve",
    "AsyncReject",
    "ThrowDeleteSuperProperty",
];

const OUTCOME_NAMES: [&str; 5] = ["expressed", "plumbing", "elided", "fallback", "dead_pure"];

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn corpus_stage_a_gate() {
    let root = common::corpus_root();
    let paths = common::manifest_paths(&root);
    assert_eq!(paths.len(), 2787, "expected the full 2787-fixture corpus");

    let mut fixtures = 0usize;
    let mut functions = 0usize;
    let mut histogram: BTreeMap<&'static str, OpStat> = BTreeMap::new();
    let mut instructions = 0usize;
    let mut outcome_total = 0usize;

    for relative in &paths {
        let data = std::fs::read(root.join(relative)).expect("read fixture");
        let file = abcd_file::decode(&data).expect("decode fixture");
        let module = lift_file(&file).expect("lift fixture");
        fixtures += 1;

        // Determinism: two independent dumps are byte-identical.
        let dump1 = dump_module(&module);
        let dump2 = dump_module(&module);
        assert_eq!(dump1, dump2, "non-deterministic dump in {relative}");

        for fi in 0..module.functions.len() {
            let func = FuncId::new(fi as u32);
            let rf = recover_func(&module, func);
            functions += 1;
            // Every instruction of the function gets exactly one outcome.
            let f = module.func(func).expect("func");
            let func_insts: usize = f
                .blocks
                .iter()
                .map(|b| module.block(*b).map(|bl| bl.insts.len()).unwrap_or(0))
                .sum();
            instructions += func_insts;
            let func_outcomes: usize = rf
                .histogram
                .values()
                .map(|s| s.counts.iter().sum::<usize>())
                .sum();
            assert_eq!(
                func_insts, func_outcomes,
                "instruction/outcome mismatch in {relative} {func:?}"
            );
            outcome_total += func_outcomes;
            for (op, stat) in rf.histogram {
                let entry = histogram.entry(op).or_default();
                entry.fitness = stat.fitness;
                for (i, c) in stat.counts.iter().enumerate() {
                    entry.counts[i] += c;
                }
            }
        }
    }

    eprintln!("STAGE-A-GATE fixtures={fixtures} functions={functions}");
    eprintln!("STAGE-A-GATE instructions={instructions} outcomes={outcome_total}");

    // The verbatim coverage histogram, grouped by fitness class.
    let mut by_class: BTreeMap<Fitness, Vec<(&str, &OpStat)>> = BTreeMap::new();
    for (op, stat) in &histogram {
        by_class
            .entry(stat.fitness.expect("fitness recorded"))
            .or_default()
            .push((op, stat));
    }
    for (class, rows) in &by_class {
        let mut totals = [0usize; 5];
        for (_, stat) in rows {
            for (i, c) in stat.counts.iter().enumerate() {
                totals[i] += c;
            }
        }
        eprintln!(
            "COVERAGE class={class:?} ops={} total={} expressed={} plumbing={} \
             elided={} fallback={} dead_pure={}",
            rows.len(),
            totals.iter().sum::<usize>(),
            totals[0],
            totals[1],
            totals[2],
            totals[3],
            totals[4]
        );
        for (op, stat) in rows {
            eprintln!(
                "COVERAGE op={op} total={} expressed={} plumbing={} elided={} \
                 fallback={} dead_pure={}",
                stat.counts.iter().sum::<usize>(),
                stat.counts[0],
                stat.counts[1],
                stat.counts[2],
                stat.counts[3],
                stat.counts[4]
            );
        }
    }

    // The hard-7 report: exactly which driver-plumbing ops landed as
    // documented fallbacks, and how many.
    eprintln!("HARD-7 report (documented fallback nodes, d-P2):");
    for op in DOCUMENTED_FALLBACK_OPS {
        let stat = histogram.get(*op);
        let (total, counts) = match stat {
            Some(s) => (s.counts.iter().sum::<usize>(), s.counts),
            None => (0, [0; 5]),
        };
        let parts: Vec<String> = counts
            .iter()
            .enumerate()
            .filter(|(_, c)| **c > 0)
            .map(|(i, c)| format!("{}={c}", OUTCOME_NAMES[i]))
            .collect();
        eprintln!("HARD-7 {op} total={total} ({})", parts.join(" "));
    }

    // Gate 1: ops outside the documented set must never fall back.
    for (op, stat) in &histogram {
        let fallbacks = stat.get(Outcome::Fallback);
        if fallbacks > 0 && !DOCUMENTED_FALLBACK_OPS.contains(op) {
            panic!("unexpected fallback for {op}: {fallbacks}");
        }
    }

    // Gate 2: hard-7 ops are ONLY ever fallback or dead-pure.
    for op in DOCUMENTED_FALLBACK_OPS {
        if let Some(stat) = histogram.get(op) {
            assert_eq!(
                stat.get(Outcome::Expressed)
                    + stat.get(Outcome::Plumbing)
                    + stat.get(Outcome::Elided),
                0,
                "hard op {op} was silently expressed/plumbing/elided"
            );
        }
    }
}
