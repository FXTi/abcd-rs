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
//! cargo test -p abcd-taint --test corpus_taint_smoke --release -- --ignored --nocapture
//! ```

mod common;

use abcd_taint::{SinkSpec, SourceSpec, TaintConfig, TaintReport};

/// The smoke configuration (the documented source choice).
fn smoke_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None, // all params — including params[0] = this
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: true,
        ..TaintConfig::default()
    }
}

/// A name-resolved, comparable stats snapshot.
fn stats_snapshot(r: &TaintReport) -> String {
    format!("{:?}", r.stats)
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

    let mut total_hits = 0usize;
    let mut fixtures_with_flows = 0usize;
    let mut total_edges = 0usize;
    let mut agg = abcd_taint::RegistryStats::default();
    let mut miss_log: std::collections::BTreeMap<String, usize> = Default::default();
    let mut hit_log: std::collections::BTreeMap<String, usize> = Default::default();

    for relative in &paths {
        let module = common::lift_fixture(&root, relative);
        let a = abcd_taint::run_taint(&module, &smoke_config());
        let b = abcd_taint::run_taint(&module, &smoke_config());
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

        total_hits += a.hits.len();
        total_edges += a.path_edges;
        if !a.hits.is_empty() {
            fixtures_with_flows += 1;
        }
        agg.lookups += a.stats.lookups;
        agg.negative_cache_hits += a.stats.negative_cache_hits;
        agg.sites_body_step += a.stats.sites_body_step;
        agg.sites_native_keep += a.stats.sites_native_keep;
        agg.sites_unknown += a.stats.sites_unknown;
        for (name, n) in &a.summary_misses {
            *miss_log.entry(name.clone()).or_insert(0) += n;
        }
        for (name, n) in &a.summary_hits {
            *hit_log.entry(name.clone()).or_insert(0) += n;
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
    let mut misses: Vec<(String, usize)> = miss_log.into_iter().collect();
    misses.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    eprintln!(
        "TAINT-SUMMARY-MISSES top10={:?}",
        &misses[..misses.len().min(10)]
    );
    let mut hits: Vec<(String, usize)> = hit_log.into_iter().collect();
    hits.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    eprintln!("TAINT-SUMMARY-HITS top10={:?}", &hits[..hits.len().min(10)]);
    eprintln!("SMOKE-DETERMINISM runs=2 identical=true");
    assert!(agg.lookups > 0, "the corpus contains call sites");
}
