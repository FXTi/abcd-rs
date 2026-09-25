//! The 5-family precision probe suite (analysis-strategy.md §5.5 — the
//! ladder-trigger baseline). Each family is a hand-crafted mini-module
//! with known ground truth and expected FP/FN annotations; the suite
//! prints `PROBE <family> tp=.. fp=.. fn=..` lines and asserts them.
//!
//! Families (per the task):
//! 1. straight-line local propagation;
//! 2. heap store/load through the same alloc site;
//! 3. dynamic dispatch (phi of two closures — name-based resolution
//!    over-approximates);
//! 4. interprocedural call/return;
//! 5. exception-only path (throw → handler is the ONLY path).
//!
//! Every probe seeds `func_main_0`'s params and sinks `print`, matching
//! the corpus smoke configuration so the numbers are comparable.

mod common;

use abcd_ir::{BlockId, CallKind, Edge, EdgeKind, Module, Op};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// Probe counts: true/false positives and false negatives.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Counts {
    tp: usize,
    fp: usize,
    fn_: usize,
}

fn probe_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: true,
        ..TaintConfig::default()
    }
}

/// Evaluate a module against `(expected_tainted_sinks, expected_clean_sinks)`
/// plus the exact set of expected hit marker lines (W4: hit IDENTITY, not
/// just the count — a wrong-sink hit with the right count must fail).
fn evaluate(module: &Module, family: &str, expected: Counts, expected_lines: &[u32]) {
    let report = abcd_taint::run_taint(module, &probe_config());
    let actual = Counts {
        tp: report.hits.len(),
        fp: 0, // each probe's clean sink checks below count these
        fn_: 0,
    };
    // The probes encode their clean-sink expectations in `expected.fp`
    // as "tolerated FP"; the hit-count equality IS the check.
    eprintln!(
        "PROBE {family} tp={} fp={} fn={} (expected tp={} fp={} fn={})",
        actual.tp, actual.fp, actual.fn_, expected.tp, expected.fp, expected.fn_
    );
    assert_eq!(
        report.hits.len(),
        expected.tp + expected.fp,
        "{family}: hits = tp+fp"
    );
    let mut lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    lines.sort_unstable();
    let mut want: Vec<u32> = expected_lines.to_vec();
    want.sort_unstable();
    assert_eq!(lines, want, "{family}: hit identity (sink marker lines)");
}

/// `print(x)` over `value` in block `b`, with a distinguishing marker
/// line number so multi-sink probes can tell hits apart.
fn print_call_at(
    m: &mut Module,
    b: BlockId,
    value: abcd_ir::ValueId,
    line: u32,
) -> abcd_ir::InstId {
    let print = try_get_global(m, b, "print");
    push_inst_loc(
        m,
        b,
        Op::Call {
            callee: print,
            this: None,
            args: vec![value],
            kind: CallKind::Dynamic,
        },
        Some(abcd_ir::Loc {
            line,
            column: Some(1),
        }),
    )
}

/// Family 1 — straight-line local: param → Mov → binop → print.
/// Ground truth: 1 flow, no imprecision. tp=1 fp=0 fn=0.
#[test]
fn probe_straight_line_local() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let one = load_number(&mut m, entry, 1.0);
    let q = emit(&mut m, entry, Op::Mov { src: p });
    let r = add(&mut m, entry, q, one);
    print_call_at(&mut m, entry, r, 10);
    emit_void(&mut m, entry, Op::Return { value: None });

    evaluate(
        &m,
        "straight-line-local",
        Counts {
            tp: 1,
            fp: 0,
            fn_: 0,
        },
        &[10],
    );
}

/// Family 2 — heap store/load through the same alloc site, with a
/// non-aliasing twin site as the FP control.
/// Ground truth: the same-site load is tainted (tp=1); the distinct-site
/// load is clean (fp=0 — rung-0 site keying separates them); fn=0.
#[test]
fn probe_heap_store_load_same_alloc_site() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let secret = intern(&mut m, "secret");
    let obj = alloc_object(&mut m, entry);
    emit_void(
        &mut m,
        entry,
        Op::StoreProp {
            object: obj,
            name: secret,
            value: p,
        },
    );
    // The FP control: a DIFFERENT alloc site, same field name, never
    // stored into.
    let other = alloc_object(&mut m, entry);
    let x = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: obj,
            name: secret,
        },
    );
    let y = emit(
        &mut m,
        entry,
        Op::LoadProp {
            object: other,
            name: secret,
        },
    );
    print_call_at(&mut m, entry, x, 20); // tainted
    print_call_at(&mut m, entry, y, 21); // clean — a hit here is an FP
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &probe_config());
    let lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    eprintln!(
        "PROBE heap-same-site tp={} fp={} fn=0 (hit lines {lines:?})",
        report.hits.len(),
        0
    );
    assert_eq!(lines, vec![20], "only the same-site load flows");
}

/// Family 3 — dynamic dispatch: the callee is a phi of two closures
/// (`f1` identity, `f2` constant); value-flow resolution targets BOTH.
/// Ground truth: 1 flow exists (through f1). The f2 path is an
/// over-approximation inherent to set-valued resolution — at sink
/// granularity there is no FP (the flow is real); the annotation
/// records the over-approximation axis for the rung-1→2 trigger
/// (analysis-strategy §5.5: "FP concentration shifts to dispatch").
/// tp=1 fp=0 fn=0.
#[test]
fn probe_dynamic_dispatch() {
    let mut m = mk_module();
    let f1 = add_func_named(&mut m, "identity");
    {
        let b = entry_of(&m, f1);
        add_param(&mut m, f1, 0);
        let x = add_param(&mut m, f1, 1);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let f2 = add_func_named(&mut m, "constant");
    {
        let b = entry_of(&m, f2);
        add_param(&mut m, f2, 0);
        add_param(&mut m, f2, 1);
        let c = load_string(&mut m, b, "clean");
        emit_void(&mut m, b, Op::Return { value: Some(c) });
    }

    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let t = add_block(&mut m, f);
    let e = add_block(&mut m, f);
    let join = add_block(&mut m, f);
    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: t,
            false_dest: e,
        },
    );
    let d1 = emit(
        &mut m,
        t,
        Op::DefineFunc {
            body: f1,
            captures: vec![],
            length: 1,
        },
    );
    let c1 = emit(&mut m, t, Op::AllocClosure { func: d1 });
    emit_void(&mut m, t, Op::Branch { dest: join });
    let d2 = emit(
        &mut m,
        e,
        Op::DefineFunc {
            body: f2,
            captures: vec![],
            length: 1,
        },
    );
    let c2 = emit(&mut m, e, Op::AllocClosure { func: d2 });
    emit_void(&mut m, e, Op::Branch { dest: join });
    link(&mut m, entry, t);
    link(&mut m, entry, e);
    link(&mut m, t, join);
    link(&mut m, e, join);
    let g = emit(
        &mut m,
        join,
        Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: t,
                        kind: EdgeKind::Normal,
                    },
                    c1,
                ),
                (
                    Edge {
                        from: e,
                        kind: EdgeKind::Normal,
                    },
                    c2,
                ),
            ],
        },
    );
    let r = emit(
        &mut m,
        join,
        Op::Call {
            callee: g,
            this: None,
            args: vec![p],
            kind: CallKind::Dynamic,
        },
    );
    print_call_at(&mut m, join, r, 30);
    emit_void(&mut m, join, Op::Return { value: None });

    evaluate(
        &m,
        "dynamic-dispatch",
        Counts {
            tp: 1,
            fp: 0,
            fn_: 0,
        },
        &[30],
    );
}

/// Family 4 — interprocedural call/return: a direct call to a helper
/// that returns its argument. tp=1 fp=0 fn=0.
#[test]
fn probe_interprocedural_call_return() {
    let mut m = mk_module();
    let helper = add_func_named(&mut m, "helper");
    {
        let b = entry_of(&m, helper);
        add_param(&mut m, helper, 0);
        let x = add_param(&mut m, helper, 1);
        emit_void(&mut m, b, Op::Return { value: Some(x) });
    }
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let h = {
        let c = m.consts.push(abcd_ir::Const::MethodRef(helper));
        emit(&mut m, entry, Op::LoadConst(c))
    };
    let r = emit(
        &mut m,
        entry,
        Op::Call {
            callee: h,
            this: None,
            args: vec![p],
            kind: CallKind::Direct,
        },
    );
    print_call_at(&mut m, entry, r, 40);
    emit_void(&mut m, entry, Op::Return { value: None });

    let report = abcd_taint::run_taint(&m, &probe_config());
    eprintln!(
        "PROBE interprocedural-call-return tp={} fp=0 fn=0",
        report.hits.len()
    );
    assert_eq!(report.hits.len(), 1);
    // The reconstructed path must cross the call and return.
    let path = &report.hits[0].path;
    let ops: Vec<&str> = path.iter().map(|s| s.op.as_str()).collect();
    assert!(ops.contains(&"Call"), "path crosses the call: {ops:?}");
    assert!(ops.contains(&"Return"), "path crosses the return: {ops:?}");
}

/// Family 5 — exception-only path: the ONLY route from source to sink
/// is `throw p` → catch binding → print. A normal-path clean sink is
/// the FP control. tp=1 fp=0 fn=0.
#[test]
fn probe_exception_only_path() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "func_main_0");
    let entry = entry_of(&m, f);
    add_param(&mut m, f, 0);
    let p = add_param(&mut m, f, 1);
    let thrower = add_block(&mut m, f);
    let after = add_block(&mut m, f);
    let handler = add_block(&mut m, f);
    let exc = add_exception_param(&mut m, handler);

    emit_void(
        &mut m,
        entry,
        Op::CondBranch {
            cond: p,
            true_dest: thrower,
            false_dest: after,
        },
    );
    emit_void(&mut m, thrower, Op::Throw { value: p });
    // The normal path: prints a constant — clean.
    let clean = load_string(&mut m, after, "clean");
    print_call_at(&mut m, after, clean, 51);
    emit_void(&mut m, after, Op::Return { value: None });
    // The handler: prints the caught value — tainted (exceptional path).
    print_call_at(&mut m, handler, exc, 55);
    emit_void(&mut m, handler, Op::Return { value: None });
    link(&mut m, entry, thrower);
    link(&mut m, entry, after);
    add_try(&mut m, f, vec![thrower], handler, exc);

    let report = abcd_taint::run_taint(&m, &probe_config());
    let lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    eprintln!(
        "PROBE exception-only tp={} fp=0 fn=0 (hit lines {lines:?})",
        report.hits.len()
    );
    assert_eq!(lines, vec![55], "only the exceptional path flows");
}

// ────────────────────────────────────────────────────────────────────
// The COMPILED probe suite (t-P1; analysis-strategy.md §5.5 — the
// ladder-trigger instrument). Hand-written JS sources with known ground
// truth live in probes-taint/src/ (+ annotations.json); they are
// compiled by scripts/gen-taint-probes.py into the GITIGNORED
// probes-taint/out/ with the GHCR image's es2abc (24.0.0.0, baseline,
// script mode — the pin and rationale are in annotations.json).
//
// The suite EXTENDS the five hand-built mini-module families above:
// same axes, real bytecode. Its ground truth is runtime-checked by the
// generator (every probe runs clean on the image's VM).
//
// Expectations per sink line (see annotations.json):
//   tp    — real flow, MUST hit (a miss is a regression);
//   clean — no flow, MUST NOT hit (a hit is an FP regression);
//   fp    — no flow, the CURRENT rung HITS (expected FP; closes_at_rung
//           records the ladder rung that should kill it);
//   fn    — real flow, the current rung MISSES (known FN; closes_at_rung
//           records the rung that should catch it).
// Deviations in EITHER direction fail the suite: an expected-fp/fn that
// stops reproducing means the ladder moved and the annotations must be
// updated deliberately. That is what makes this the ladder TRIGGER.
//
// The suite runs at the default alias rung (1 — the on-demand engine,
// t-P2). ABCD_TAINT_RUNG=0 selects the rung-0 oracle for A/B evidence
// (against rung-1 annotations it fails loudly — by design).
//
// Run:
//   python3 scripts/gen-taint-probes.py   # once, needs docker
//   cargo test -p abcd-taint --test probes --release -- \
//       --ignored --nocapture probe_suite_compiled
// ────────────────────────────────────────────────────────────────────

mod compiled {
    use abcd_taint::{SinkSpec, SourceSpec, TaintConfig, TaintReport};
    use std::path::{Path, PathBuf};

    /// One sink expectation from annotations.json.
    #[derive(Debug)]
    struct SinkExpect {
        line: u32,
        expect: String,         // tp | clean | fp | fn
        closes_at_rung: String, // "", "1", "2"
    }

    /// One probe row.
    #[derive(Debug)]
    struct Probe {
        id: String,
        family: String,
        sinks: Vec<SinkExpect>,
        summaries_applied: Vec<String>,
        named_misses: Vec<String>,
        body_step_min: usize,
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .canonicalize()
            .expect("repo root")
    }

    /// Parse annotations.json with python3's stdlib JSON (the same
    /// pattern as common::runtime_passed_paths — keeps dev-deps at
    /// abcd-file/abcd-lift only). Emits a TSV the arms below parse:
    ///   CONFIG \t source \t sink
    ///   PROBE  \t id \t family
    ///   SINK   \t id \t line \t expect \t closes_at_rung
    ///   COUNTER\t id \t summary_applied|named_miss|body_step_min \t value
    fn load_annotations(root: &Path) -> (Vec<Probe>, String, String) {
        let script = r#"
import json, sys
a = json.load(open(sys.argv[1], encoding="utf-8"))
src = next(iter(a["source"].values()))
snk = next(iter(a["sink"].values()))
print(f"CONFIG\t{src}\t{snk}")
for p in a["probes"]:
    print(f"PROBE\t{p['id']}\t{p['family']}")
    for s in p["sinks"]:
        closes = s.get("closes_at_rung")
        closes = "" if closes is None else str(closes)
        print(f"SINK\t{p['id']}\t{s['line']}\t{s['expect']}\t{closes}")
    for kind, values in p.get("expect_counters", {}).items():
        if not isinstance(values, list):
            values = [values]
        for v in values:
            print(f"COUNTER\t{p['id']}\t{kind}\t{v}")
"#;
        let out = std::process::Command::new("python3")
            .arg("-c")
            .arg(script)
            .arg(root.join("probes-taint/src/annotations.json"))
            .output()
            .expect("python3 is required by corpus tooling");
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
        let text = String::from_utf8(out.stdout).expect("UTF-8 annotations");
        let mut probes: Vec<Probe> = Vec::new();
        let mut config = (String::new(), String::new());
        for line in text.lines() {
            let f: Vec<&str> = line.split('\t').collect();
            match f[0] {
                "CONFIG" => config = (f[1].to_owned(), f[2].to_owned()),
                "PROBE" => probes.push(Probe {
                    id: f[1].to_owned(),
                    family: f[2].to_owned(),
                    sinks: Vec::new(),
                    summaries_applied: Vec::new(),
                    named_misses: Vec::new(),
                    body_step_min: 0,
                }),
                "SINK" => probes
                    .last_mut()
                    .expect("SINK after PROBE")
                    .sinks
                    .push(SinkExpect {
                        line: f[2].parse().unwrap(),
                        expect: f[3].to_owned(),
                        closes_at_rung: f[4].to_owned(),
                    }),
                "COUNTER" => {
                    let p = probes.last_mut().expect("COUNTER after PROBE");
                    match f[2] {
                        "summaries_applied" => p.summaries_applied.push(f[3].to_owned()),
                        "named_misses" => p.named_misses.push(f[3].to_owned()),
                        "body_step_min" => p.body_step_min = f[3].parse().unwrap(),
                        other => panic!("unknown counter kind {other}"),
                    }
                }
                other => panic!("bad annotations record {other}"),
            }
        }
        (probes, config.0, config.1)
    }

    fn compiled_config(source: &str, sink: &str) -> TaintConfig {
        TaintConfig {
            sources: vec![SourceSpec::GlobalLoad {
                name: source.to_owned(),
            }],
            sinks: vec![SinkSpec::Call {
                name: sink.to_owned(),
            }],
            builtin_summaries: true,
            // A/B/C switch: ABCD_TAINT_RUNG=0/1/2 selects the oracle
            // rung (the annotations encode the CURRENT rung's
            // expectations — rung 2 — so lower rungs fail loudly; that
            // IS the A/B/C evidence of what each rung bought).
            alias_rung: match std::env::var("ABCD_TAINT_RUNG").as_deref() {
                Ok("0") => 0,
                Ok("1") => 1,
                _ => 2,
            },
            ..TaintConfig::default()
        }
    }

    /// The set of 1-based source lines the run hit (synthetic
    /// u32::MAX-located instructions carry no line).
    fn hit_lines(report: &TaintReport) -> Vec<u32> {
        let mut lines: Vec<u32> = report
            .hits
            .iter()
            .filter_map(|h| h.loc.map(|l| l.line))
            .filter(|&l| l != u32::MAX)
            .map(|l| l + 1)
            .collect();
        lines.sort_unstable();
        lines.dedup();
        lines
    }

    #[test]
    #[ignore = "requires probes-taint/out (run scripts/gen-taint-probes.py first) and python3"]
    fn probe_suite_compiled() {
        let root = repo_root();
        let (probes, source, sink) = load_annotations(&root);
        assert_eq!((source.as_str(), sink.as_str()), ("TAINT", "print"));
        assert!(
            root.join("probes-taint/out/manifest.json").is_file(),
            "probes-taint/out missing — run `python3 scripts/gen-taint-probes.py` first"
        );
        let config = compiled_config(&source, &sink);

        let mut violations: Vec<String> = Vec::new();
        let mut families: Vec<(String, usize, usize, usize, usize)> = Vec::new(); // name, cases, tp, fp, fn
        let mut totals = (0usize, 0usize, 0usize);

        for probe in &probes {
            let data = std::fs::read(
                root.join("probes-taint/out")
                    .join(format!("{}.abc", probe.id)),
            )
            .unwrap_or_else(|e| panic!("{}: read compiled probe: {e}", probe.id));
            let file = abcd_file::decode(&data).expect("decode probe");
            let module = abcd_lift::lift_file(&file).expect("lift probe");
            let report = abcd_taint::run_taint(&module, &config);
            let hits = hit_lines(&report);

            let mut tp = 0usize;
            let mut fp = 0usize;
            let mut fn_ = 0usize;
            let mut annotated = Vec::new();
            for s in &probe.sinks {
                annotated.push(s.line);
                let hit = hits.contains(&s.line);
                match (s.expect.as_str(), hit) {
                    ("tp", true) => tp += 1,
                    ("tp", false) => violations.push(format!(
                        "{}:{}: expected TP missed (regression)",
                        probe.id, s.line
                    )),
                    ("clean", false) => {}
                    ("clean", true) => violations.push(format!(
                        "{}:{}: FP regression — clean sink hit",
                        probe.id, s.line
                    )),
                    ("fp", true) => fp += 1,
                    ("fp", false) => violations.push(format!(
                        "{}:{}: expected-FP no longer reproduces (closes_at_rung {}) — \
                         the ladder moved; update annotations.json",
                        probe.id, s.line, s.closes_at_rung
                    )),
                    ("fn", false) => fn_ += 1,
                    ("fn", true) => violations.push(format!(
                        "{}:{}: expected-FN closed (closes_at_rung {}) — \
                         the ladder climbed; update annotations.json",
                        probe.id, s.line, s.closes_at_rung
                    )),
                    (other, _) => panic!("{}: bad expect {other}", probe.id),
                }
            }
            for &l in &hits {
                if !annotated.contains(&l) {
                    violations.push(format!(
                        "{}:{}: hit on an UNANNOTATED sink line (FP regression?)",
                        probe.id, l
                    ));
                }
            }
            for name in &probe.summaries_applied {
                if !report.summaries_applied.iter().any(|(_, n)| n == name) {
                    violations.push(format!(
                        "{}: summary {name} never applied (counter regression)",
                        probe.id
                    ));
                }
            }
            for name in &probe.named_misses {
                if !report.summary_misses.contains_key(name) {
                    violations.push(format!(
                        "{}: {name} missing from the named-miss log (counter regression)",
                        probe.id
                    ));
                }
            }
            if report.stats.sites_body_step < probe.body_step_min {
                violations.push(format!(
                    "{}: body_step {} < {} (counter regression)",
                    probe.id, report.stats.sites_body_step, probe.body_step_min
                ));
            }

            eprintln!(
                "PROBE-CASE {} hits={hits:?} tp={tp} fp={fp} fn={fn_}",
                probe.id
            );
            totals.0 += tp;
            totals.1 += fp;
            totals.2 += fn_;
            match families.iter_mut().find(|(n, ..)| n == &probe.family) {
                Some((_, cases, ftp, ffp, ffn)) => {
                    *cases += 1;
                    *ftp += tp;
                    *ffp += fp;
                    *ffn += fn_;
                }
                None => families.push((probe.family.clone(), 1, tp, fp, fn_)),
            }
        }

        eprintln!(
            "PROBE-SUITE probes={} (rung {})",
            probes.len(),
            config.alias_rung
        );
        for (name, cases, tp, fp, fn_) in &families {
            eprintln!("PROBE-FAMILY {name} cases={cases} tp={tp} fp={fp} fn={fn_}");
        }
        eprintln!(
            "PROBE-TOTAL tp={} fp={} fn={} violations={}",
            totals.0,
            totals.1,
            totals.2,
            violations.len()
        );
        assert!(
            violations.is_empty(),
            "probe suite regressions:\n{}",
            violations.join("\n")
        );
    }
}
