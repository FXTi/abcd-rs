//! Opt-in corpus print-sink smoke (task §7a; analysis-strategy §5.5
//! smoke tier): over all 1149 runtime-passed fixtures —
//!
//! 1. seed the configurable source (ALL params of `func_main_0`, the abc
//!    module entry point — documented in the README: the entry point's
//!    parameters are the corpus' uniform "environment input" stand-in,
//!    and every fixture has one),
//! 2. run the taint analysis with the top-20 builtin summaries and
//!    `print` as the sink,
//! 3. report the flows-into-print count + the miss-counter summary,
//! 4. run TWICE per fixture and assert identical reports
//!    (determinism).
//!
//! Run:
//!
//! ```text
//! cargo test -p abcd-rs --test lift-taint --release -- --ignored --nocapture corpus_taint_smoke
//! ```
//!
//! Migrated from `abcd-taint/tests/corpus_taint_smoke.rs` to the root
//! package's `tests/lift-taint/` target; the shared helpers moved to the
//! root package's `tests/common/`.

use crate::common;

use abcd_taint::{SinkSpec, SourceSpec, TaintConfig, TaintReport};
use rayon::prelude::*;

/// The smoke configuration (the documented source choice). A
/// sensitivity mode seeds ALL functions' params
/// (`ABCD_TAINT_SMOKE_SOURCE=all-params`) — the positive control that
/// taint physically reaches `print` on real bytecode (the corpus
/// fixtures are self-contained and rarely route entry params into
/// `print`, so the registered config's flow count is legitimately low).
fn smoke_config() -> TaintConfig {
    // all-params sensitivity: `"*"` seeds every function's params (the
    // driver treats the name as a wildcard).
    let source_name = match std::env::var("ABCD_TAINT_SMOKE_SOURCE").as_deref() {
        Ok("all-params") => "*",
        _ => "func_main_0",
    };
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: source_name.to_owned(),
            params: None, // all params — including params[0] = this
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: true,
        // A/B/C switch (the probe runner's knob, mirrored): run the
        // smoke at a selected oracle rung for per-rung corpus numbers.
        alias_rung: match std::env::var("ABCD_TAINT_RUNG").as_deref() {
            Ok("0") => 0,
            Ok("1") => 1,
            _ => 2,
        },
        ..TaintConfig::default()
    }
}

/// A name-resolved, comparable stats snapshot.
fn stats_snapshot(r: &TaintReport) -> String {
    format!("{:?}", r.stats)
}

/// One fixture's order-independent contribution to the smoke aggregate.
struct FixtureOut {
    hits: usize,
    path_edges: usize,
    gap_resolved: usize,
    gap_unresolved: usize,
    lookups: usize,
    negative_cache_hits: usize,
    sites_body_step: usize,
    sites_native_keep: usize,
    sites_unknown: usize,
    misses: std::collections::BTreeMap<String, usize>,
    hits_by_name: std::collections::BTreeMap<String, usize>,
}

#[test]
#[ignore = "requires exported GHCR corpus and python3"]
fn taint_smoke_all_fixtures() {
    let root = common::corpus_root();
    let paths = common::runtime_passed_paths(&root);
    assert_eq!(
        paths.len(),
        1149,
        "expected the 1149 runtime-passed fixtures"
    );

    let config = smoke_config();
    // Parallel per-fixture taint runs (rayon): the per-fixture
    // determinism asserts stay inside the map; only order-independent
    // counts and name-keyed maps come back for the serial fold.
    let per_fixture: Vec<FixtureOut> = paths
        .par_iter()
        .map(|relative| {
            let module = common::lift_fixture(&root, relative);
            let a = abcd_taint::run_taint(&module, &config);
            let b = abcd_taint::run_taint(&module, &config);
            assert_eq!(
                a.hits.len(),
                b.hits.len(),
                "determinism (hit count): {relative}"
            );
            assert_eq!(a.hits, b.hits, "determinism (hits): {relative}");
            assert_eq!(
                stats_snapshot(&a),
                stats_snapshot(&b),
                "determinism (counters): {relative}"
            );
            assert_eq!(
                a.summaries_applied, b.summaries_applied,
                "determinism (applied summaries): {relative}"
            );
            FixtureOut {
                hits: a.hits.len(),
                path_edges: a.path_edges,
                gap_resolved: a.gap_sites_resolved,
                gap_unresolved: a.gap_sites_unresolved,
                lookups: a.stats.lookups,
                negative_cache_hits: a.stats.negative_cache_hits,
                sites_body_step: a.stats.sites_body_step,
                sites_native_keep: a.stats.sites_native_keep,
                sites_unknown: a.stats.sites_unknown,
                misses: a.summary_misses,
                hits_by_name: a.summary_hits,
            }
        })
        .collect();

    let mut total_hits = 0usize;
    let mut fixtures_with_flows = 0usize;
    let mut total_edges = 0usize;
    let mut gap_resolved = 0usize;
    let mut gap_unresolved = 0usize;
    let mut agg = abcd_taint::RegistryStats::default();
    let mut miss_log: std::collections::BTreeMap<String, usize> = Default::default();
    let mut hit_log: std::collections::BTreeMap<String, usize> = Default::default();

    for f in per_fixture {
        total_hits += f.hits;
        total_edges += f.path_edges;
        gap_resolved += f.gap_resolved;
        gap_unresolved += f.gap_unresolved;
        if f.hits > 0 {
            fixtures_with_flows += 1;
        }
        agg.lookups += f.lookups;
        agg.negative_cache_hits += f.negative_cache_hits;
        agg.sites_body_step += f.sites_body_step;
        agg.sites_native_keep += f.sites_native_keep;
        agg.sites_unknown += f.sites_unknown;
        for (name, n) in f.misses {
            *miss_log.entry(name).or_insert(0) += n;
        }
        for (name, n) in f.hits_by_name {
            *hit_log.entry(name).or_insert(0) += n;
        }
    }

    eprintln!("SMOKE fixtures=1149 fixtures_with_flows={fixtures_with_flows}");
    eprintln!("TAINT-FLOWS hits={total_hits}");
    eprintln!(
        "TAINT-COUNTERS lookups={} neg_cache_hits={} body_step={} native_keep={} unknown={}",
        agg.lookups,
        agg.negative_cache_hits,
        agg.sites_body_step,
        agg.sites_native_keep,
        agg.sites_unknown,
    );
    eprintln!("TAINT-PATH-EDGES total={total_edges}");
    eprintln!("TAINT-GAPS resolved={gap_resolved} unresolved={gap_unresolved}");
    // Top-N of the miss/hit logs to print (default 10 — the README's
    // quoted table). `ABCD_TAINT_SMOKE_TOPN` widens the cut for
    // backlog-hygiene work (the miss log IS the summary backlog; the
    // full tail classifies the non-actionable entries).
    let topn: usize = std::env::var("ABCD_TAINT_SMOKE_TOPN")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(10);
    let mut misses: Vec<(String, usize)> = miss_log.into_iter().collect();
    misses.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    eprintln!(
        "TAINT-SUMMARY-MISSES top{}={:?}",
        topn,
        &misses[..misses.len().min(topn)]
    );
    let mut hits: Vec<(String, usize)> = hit_log.into_iter().collect();
    hits.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    eprintln!(
        "TAINT-SUMMARY-HITS top{}={:?}",
        topn,
        &hits[..hits.len().min(topn)]
    );
    eprintln!("SMOKE-DETERMINISM runs=2 identical=true");
    assert!(agg.lookups > 0, "the corpus contains call sites");
    // W5 (q-P2, maintainer-approved 2026-09-25): the design invariant is
    // ZERO hits on the self-contained corpus — the fixtures never route
    // entry params into `print`, so any hit is a false positive. Gate it
    // (was: printed only, an FP regression would have been silent).
    assert_eq!(
        total_hits, 0,
        "corpus taint smoke: any hit on the self-contained corpus is a false positive"
    );
}

#[test]
#[ignore = "requires local-only modules.abc (gitignored)"]
fn modules_abc_ohos_prepared_and_pta_smoke() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("modules.abc");
    if !path.is_file() {
        eprintln!(
            "skipping modules.abc ohos prepared+pta gate: {} absent",
            path.display()
        );
        return;
    }
    let start = std::time::Instant::now();
    let raw: std::sync::Arc<[u8]> =
        std::sync::Arc::from(std::fs::read(&path).expect("read modules.abc"));
    let file = abcd_file::decode_lazy(raw).expect("pure-Rust decode_lazy modules.abc");
    let config = abcd_taint::ohos_preset();
    let ir = abcd_lift::lift_file_with_options(
        &file,
        &abcd_lift::LiftOptions {
            retain_tail_capacity: config.ohos_lifecycle,
            parallel: true,
        },
    )
    .expect("parallel lift modules.abc");
    drop(file);

    // #71 / #74 / #75 / #76: zero-clone in-place harness append + context symbol
    // interning + explicit `harness_func` tracking.
    let prepared = abcd_taint::PreparedModule::owned(ir, &config);
    let module = prepared.module();
    let links = prepared.links();
    let harness_fid = prepared.harness().and_then(|h| h.func);
    assert!(
        harness_fid.is_some(),
        "ohos_lifecycle must synthesize an explicit harness_func on modules.abc (#75)"
    );
    assert!(
        (0..module.sym.len())
            .any(|i| module.sym.resolve(abcd_ir::Sym::new(i as u32)) == Some("context")),
        "context symbol interned during harness append must persist on PreparedModule::module() (#74)"
    );

    // #78 / #84: CallGraph + root-sliced Rung-2 PTA must converge uncapped within 30s in --release.
    let bg = abcd_analysis::callgraph::CallGraph::build_with_links(module, links);
    let pta_cfg = abcd_analysis::dataflow::pta::PtaConfig {
        harness_func: harness_fid,
        ..Default::default()
    };
    let roots: Vec<abcd_ir::FuncId> = harness_fid.into_iter().collect();
    let pta_out = abcd_analysis::dataflow::pta::analyze_with_links_and_roots(
        module,
        links,
        &bg,
        &pta_cfg,
        Some(&roots),
    );
    assert!(
        !pta_out.stats().capped,
        "harness-rooted Rung-2 PTA on modules.abc must finish uncapped"
    );
    let elapsed = start.elapsed();
    let max_secs = if cfg!(debug_assertions) { 180 } else { 30 };
    assert!(
        elapsed.as_secs() < max_secs,
        "modules.abc prepared+pta pipeline regressed in wall-clock time: {elapsed:?} (budget < {max_secs}s)"
    );
    eprintln!(
        "MODULES-ABC-OHOS-PREPARED-PTA funcs={} pta_activations={} elapsed={elapsed:?}",
        module.functions.len(),
        pta_out.stats().activations,
    );
}

/// Full unbounded IFDS taint gate on `modules.abc` (`54,515` functions);
/// tracked by upstream `abcd-analysis` / `abcd-lift` architectural issues
/// `#97` (ArkUI `@State`/`ObservedProperty*PU` CHA), `#98` (demand-driven PTA),
/// `#99` (source-cone unbalanced returns + `IfdsConfig::step_budget`), and
/// `#100` (non-throwing `Exceptional` CFG edge pruning).
#[test]
#[ignore = "full unbounded modules.abc IFDS benchmark tracked by #97-#100"]
fn modules_abc_ohos_taint_full_ifds_gate() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("modules.abc");
    if !path.is_file() {
        return;
    }
    let start = std::time::Instant::now();
    let raw: std::sync::Arc<[u8]> =
        std::sync::Arc::from(std::fs::read(&path).expect("read modules.abc"));
    let file = abcd_file::decode_lazy(raw).expect("pure-Rust decode_lazy modules.abc");
    let config = abcd_taint::ohos_preset();
    let ir = abcd_lift::lift_file_with_options(
        &file,
        &abcd_lift::LiftOptions {
            retain_tail_capacity: config.ohos_lifecycle,
            parallel: true,
        },
    )
    .expect("parallel lift modules.abc");
    drop(file);

    let prepared = abcd_taint::PreparedModule::owned(ir, &config);
    let report = abcd_taint::run_taint_prepared(&prepared, &config);
    let elapsed = start.elapsed();

    for hit in &report.hits {
        if let abcd_taint::TaintBase::Global(sym) = hit.fact.base {
            assert!(
                prepared.module().sym.resolve(sym).is_some(),
                "every Global(sym) in SinkHit must resolve in PreparedModule::module() (#74)"
            );
        }
    }
    let max_secs = if cfg!(debug_assertions) { 300 } else { 60 };
    assert!(
        elapsed.as_secs() < max_secs,
        "modules.abc taint --preset ohos regressed in wall-clock time: {elapsed:?} (budget < {max_secs}s)"
    );
}
