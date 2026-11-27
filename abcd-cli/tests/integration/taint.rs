//! `taint` tests: TOML config → analysis → rendered hits, over
//! synthesized .abc files (zero binary fixtures).

use crate::common;
use abcd_cli::input::{self, ModuleSelection};
use abcd_cli::{taint, taint_config};
use abcd_file::{AccessFlags, Builder, CodeEntity, SourceLang, Type};
use abcd_isa::{Bytecode, EntityId, Imm, Reg};

/// `func_main_0() { print(TAINT); }` — a `TryGetGlobal("TAINT")` source
/// flowing straight into the `print` sink's argument.
fn taint_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = print
        Bytecode::Sta(Reg(0)),                            // 1: v0 = print
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = TAINT (source)
        Bytecode::Sta(Reg(1)),                            // 3: v1 = tainted
        Bytecode::Lda(Reg(0)),                            // 4: acc = print
        Bytecode::Callarg1(Imm(0), Reg(1)),               // 5: print(v1)
        Bytecode::Returnundefined,                        // 6
    ])
    .unwrap();
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    let print = b.add_string("print");
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(print))
        .unwrap();
    let taint = b.add_string("TAINT");
    b.relocate_code_id(m, offsets[2], 0, CodeEntity::String(taint))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("taint_abc must finalize")
}

/// `func_main_0() { print(id(TAINT)); }` — the source reaches the sink
/// only if the call to `id` propagates argument→return (via a summary
/// or the native-identity fallback).
fn id_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = id
        Bytecode::Sta(Reg(0)),                            // 1: v0 = id
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = TAINT (source)
        Bytecode::Sta(Reg(1)),                            // 3: v1 = tainted
        Bytecode::Lda(Reg(0)),                            // 4
        Bytecode::Callarg1(Imm(0), Reg(1)),               // 5: acc = id(v1)
        Bytecode::Sta(Reg(2)),                            // 6: v2 = id result
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 7: acc = print
        Bytecode::Sta(Reg(3)),                            // 8: v3 = print
        Bytecode::Lda(Reg(3)),                            // 9
        Bytecode::Callarg1(Imm(0), Reg(2)),               // 10: print(v2)
        Bytecode::Returnundefined,                        // 11
    ])
    .unwrap();
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    for (insn, name) in [(0usize, "id"), (2, "TAINT"), (7, "print")] {
        let s = b.add_string(name);
        b.relocate_code_id(m, offsets[insn], 0, CodeEntity::String(s))
            .unwrap();
    }
    b.deduplicate();
    b.finalize().expect("id_abc must finalize")
}

const TAINT_TO_PRINT: &str = r#"
[[sources]]
kind = "global_load"
name = "TAINT"

[[sinks]]
kind = "call"
name = "print"
"#;

fn run(abc: &[u8], config: &str) -> taint::TaintCliReport {
    let cfg = taint_config::parse(config).unwrap();
    let modules = input::load_bytes(abc, "probe.abc", ModuleSelection::Single).unwrap();
    taint::report(&modules[0], &cfg).unwrap()
}

// ---- hits ----

#[test]
fn global_source_reaches_named_sink() {
    let report = run(&taint_abc(), TAINT_TO_PRINT);
    assert_eq!(report.hits.len(), 1, "{report:?}");
    let hit = &report.hits[0];
    assert_eq!(hit.sink, "print");
    assert_eq!(hit.position, "arg 0");
    assert_eq!(hit.seed.function_name, "func_main_0");
    assert!(!hit.path.is_empty(), "a hit always carries its sink step");
    // The path ends at the sink call instruction.
    assert_eq!(hit.path.last().unwrap().inst, hit.call);
    assert_eq!(hit.path.last().unwrap().op, "Call");
}

#[test]
fn unconfigured_sink_name_does_not_hit() {
    let config = TAINT_TO_PRINT.replace("print", "eval");
    let report = run(&taint_abc(), &config);
    assert_eq!(report.hits.len(), 0, "{report:?}");
}

#[test]
fn text_report_renders_hit_path_and_counters() {
    let text = taint::render_text(&run(&taint_abc(), TAINT_TO_PRINT));
    assert!(
        text.contains("module:          probe (probe.abc)"),
        "{text}"
    );
    assert!(text.contains("hits: 1"), "{text}");
    assert!(text.contains("sink print (call i"), "{text}");
    assert!(text.contains("arg 0"), "{text}");
    assert!(text.contains("seed: fn 0 func_main_0"), "{text}");
    assert!(text.contains("path:"), "{text}");
    assert!(text.contains("stats: lookups="), "{text}");
    assert!(text.contains("summary hits:"), "{text}");
}

#[test]
fn json_report_is_machine_readable() {
    let out = taint::render(&[run(&taint_abc(), TAINT_TO_PRINT)], true).unwrap();
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(v["module"], "probe");
    assert_eq!(v["config"]["builtin_summaries"], true);
    assert_eq!(v["config"]["seed_all_functions"], true);
    assert_eq!(v["config"]["ohos_lifecycle"], true);
    assert_eq!(v["config"]["alias_rung"], 2);
    assert_eq!(v["pta_root_sliced"], false);
    let hits = v["hits"].as_array().unwrap();
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0]["sink"], "print");
    assert_eq!(hits[0]["position"], "arg 0");
    assert!(hits[0]["call"].is_u64());
    assert!(hits[0]["fact"].is_string());
    assert!(hits[0]["seed"]["function"].is_u64());
    assert_eq!(hits[0]["seed"]["function_name"], "func_main_0");
    let path = hits[0]["path"].as_array().unwrap();
    assert!(!path.is_empty());
    assert!(path[0]["inst"].is_u64());
    assert!(path[0]["op"].is_string());
    assert!(v["stats"]["lookups"].is_u64());
    assert!(v["summary_hits"].is_object());
    assert!(v["summary_misses"].is_object());
    assert!(v["path_edges"].is_u64());
    assert!(v["alias_rung_used"].is_u64());
}

// ---- extra summaries change the outcome ----

#[test]
fn extra_summary_carries_taint_through_a_call() {
    // Without a summary and without the native-identity fallback, the
    // taint dies at the unknown `id` call.
    let bare = format!("native_identity = false\nbuiltin_summaries = false\n{TAINT_TO_PRINT}");
    let report = run(&id_abc(), &bare);
    assert_eq!(
        report.hits.len(),
        0,
        "no propagation without a model: {report:?}"
    );

    // A user summary `id(param:0) -> return` carries it through.
    let with_summary = format!(
        "{bare}\n[[extra_summaries]]\nname = \"id\"\narity = 1\nflows = [ {{ from = \"param:0\", to = \"return\" }} ]\n"
    );
    let report = run(&id_abc(), &with_summary);
    assert_eq!(report.hits.len(), 1, "summary propagates: {report:?}");
    assert_eq!(report.hits[0].sink, "print");
    assert_eq!(report.config.extra_summaries, 1);
}

// ---- config handling ----

#[test]
fn empty_config_runs_clean_with_zero_hits() {
    // Explicit behavior: an empty TOML is the driver's defaults with no
    // sources and no sinks — the analysis runs and finds nothing.
    let report = run(&common::tiny_abc(), "");
    assert_eq!(report.hits.len(), 0);
    assert!(report.config.builtin_summaries);
    assert!(report.config.seed_all_functions);
    assert_eq!(report.config.alias_rung, 2);
}

#[test]
fn bad_toml_is_a_user_error_with_position() {
    let err = taint_config::parse("[[sources]\nkind = \"call\"").unwrap_err();
    assert_eq!(err.exit_code(), 1, "config errors are user errors");
    let msg = err.to_string();
    assert!(msg.contains("line"), "{msg}");
    assert!(msg.contains("column"), "{msg}");
}

#[test]
fn wrong_toml_type_is_a_user_error() {
    let err = taint_config::parse("seed_all_functions = \"yes\"").unwrap_err();
    assert_eq!(err.exit_code(), 1);
}

#[test]
fn missing_config_file_is_a_user_error() {
    let dir = common::tempdir("taint-missing");
    let err = taint::load_config(&dir.join("nope.toml")).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("cannot read"), "{err}");
}

#[test]
fn load_config_round_trips_a_file() {
    let dir = common::tempdir("taint-load");
    let path = dir.join("taint.toml");
    std::fs::write(&path, TAINT_TO_PRINT).unwrap();
    let cfg = taint::load_config(&path).unwrap();
    assert_eq!(cfg.sources.len(), 1);
    assert_eq!(cfg.sinks.len(), 1);
}

#[test]
fn unparsable_config_file_is_a_user_error_naming_the_path() {
    let dir = common::tempdir("taint-badcfg");
    let path = dir.join("bad.toml");
    std::fs::write(&path, "kind = [").unwrap();
    let err = taint::load_config(&path).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    let msg = err.to_string();
    assert!(msg.contains("bad.toml"), "{msg}");
    assert!(msg.contains("invalid taint config"), "{msg}");
}

#[test]
fn invalid_flow_endpoints_are_user_errors_at_each_position() {
    // The `from` endpoint of a flow.
    let err = taint_config::parse(
        r#"[[extra_summaries]]
        name = "x"
        flows = [ { from = "bogus", to = "base" } ]
        "#,
    )
    .unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("bogus"), "{err}");
    // The `from` endpoint of an alias flow.
    let err = taint_config::parse(
        r#"[[extra_summaries]]
        name = "x"
        alias_flows = [ { from = "param:0", to = "bogus" } ]
        "#,
    )
    .unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("bogus"), "{err}");
    // A `clears` endpoint.
    let err = taint_config::parse(
        r#"[[extra_summaries]]
        name = "x"
        clears = [ "bogus" ]
        "#,
    )
    .unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("bogus"), "{err}");
}

// ---- analysis failures ----

#[test]
fn corrupt_abc_is_a_tool_error() {
    let cfg = taint_config::parse(TAINT_TO_PRINT).unwrap();
    let mut bad = common::tiny_abc();
    bad.truncate(16);
    let modules = input::load_bytes(&bad, "bad.abc", ModuleSelection::Single).unwrap();
    let err = taint::report(&modules[0], &cfg).unwrap_err();
    assert_eq!(err.exit_code(), 2, "decode failure is a tool error");
}

#[test]
fn lift_failure_is_a_tool_error() {
    let cfg = taint_config::parse(TAINT_TO_PRINT).unwrap();
    let modules = input::load_bytes(
        &common::lift_fail_abc(),
        "liftfail.abc",
        ModuleSelection::Single,
    )
    .unwrap();
    let err = taint::report(&modules[0], &cfg).unwrap_err();
    assert_eq!(err.exit_code(), 2, "lift failure is a tool error");
    let msg = err.to_string();
    assert!(msg.contains("failed to lift"), "{msg}");
    assert!(msg.contains("jeqnull"), "{msg}");
}

// ---- seed-fact rendering (Fact::Taint arm) ----

/// `f(x) { print(x); }` — a `function_params` source seeds formal 0
/// (register v5: 2 locals + the 3 implicit frame slots), so the hit's
/// seed is a REAL taint fact, not the Λ-fact fallback.
fn params_seed_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Lda(Reg(5)),                            // 0: acc = x
        Bytecode::Sta(Reg(0)),                            // 1: v0 = x
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = print
        Bytecode::Callarg1(Imm(0), Reg(0)),               // 3: print(x)
        Bytecode::Returnundefined,                        // 4
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 2, 4);
    let print = b.add_string("print");
    b.relocate_code_id(m, offsets[2], 0, CodeEntity::String(print))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("params_seed_abc must finalize")
}

const PARAMS_TO_PRINT: &str = r#"
[[sources]]
kind = "function_params"
name = "f"

[[sinks]]
kind = "call"
name = "print"
"#;

#[test]
fn function_params_seed_renders_a_taint_fact_seed() {
    let report = run(&params_seed_abc(), PARAMS_TO_PRINT);
    assert_eq!(report.hits.len(), 1, "{report:?}");
    let hit = &report.hits[0];
    assert_eq!(hit.sink, "print");
    assert_eq!(hit.position, "arg 0");
    assert_eq!(hit.seed.function_name, "f");
    // The seed is the source fact itself (Fact::Taint), not "zero".
    assert!(
        hit.seed.fact.starts_with("local v"),
        "seed fact: {}",
        hit.seed.fact
    );
    let text = taint::render_text(&report);
    assert!(text.contains("seed: fn 0 f, fact local v"), "{text}");
}

// ---- field-chain rendering (FieldKey arms) ----

/// Property stores onto an unknown-provenance parameter (`obj.<key> = TAINT`)
/// carry a non-empty field chain to `print(obj)`: the fact renders
/// `local vN.x` / `local vN[*]` / `local vN[dyn]`. Conversely, chained
/// property reads off a whole-object source (`TAINT.a.b`, `R4-4a`) propagate
/// whole-value taint (`local vN`).
mod field_chain {
    use super::*;

    fn run_store_chain(
        store: Bytecode,
        wire: impl FnOnce(&mut Builder, abcd_file::MethodHandle, &[u32]),
    ) -> String {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let placeholder = EntityId(u16::MAX as u32);
        // `num_vregs = 2, num_args = 5`: `Reg(5)` is formal parameter 0 (`obj`),
        // `Reg(6)` is formal parameter 1 (`key`).
        let (code, offsets) = abcd_isa::encode(&[
            Bytecode::Ldai(Imm(0)),                           // 0: key = 0
            Bytecode::Sta(Reg(0)),                            // 1: v0 = numeric key (0)
            Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = TAINT
            store,                                            // 3: obj.<key> = acc
            Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 4: acc = print
            Bytecode::Callarg1(Imm(0), Reg(5)),               // 5: print(obj)
            Bytecode::Returnundefined,                        // 6
        ])
        .unwrap();
        let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 2, 5);
        let taint = b.add_string("TAINT");
        b.relocate_code_id(m, offsets[2], 0, CodeEntity::String(taint))
            .unwrap();
        wire(&mut b, m, &offsets);
        let print = b.add_string("print");
        b.relocate_code_id(m, offsets[4], 0, CodeEntity::String(print))
            .unwrap();
        b.deduplicate();
        let abc = b.finalize().expect("field-chain fixture must finalize");
        let report = run(&abc, TAINT_TO_PRINT);
        assert_eq!(report.hits.len(), 1, "{report:?}");
        report.hits[0].fact.clone()
    }

    #[test]
    fn named_field_chain_renders_the_key() {
        let placeholder = EntityId(u16::MAX as u32);
        let fact = run_store_chain(
            Bytecode::Stobjbyname(Imm(0), placeholder, Reg(5)),
            |b, m, offsets| {
                let x = b.add_string("x");
                b.relocate_code_id(m, offsets[3], 0, CodeEntity::String(x))
                    .unwrap();
            },
        );
        assert!(fact.ends_with(".x"), "fact: {fact}");
        assert!(fact.starts_with("local v"), "fact: {fact}");
    }

    #[test]
    fn index_load_renders_the_any_index_chain() {
        let fact = run_store_chain(Bytecode::Stobjbyindex(Imm(0), Reg(5), Imm(7)), |_, _, _| {});
        assert!(fact.ends_with("[*]"), "fact: {fact}");

        // `Stobjbyvalue` with a known-numeric register (`Ldai(Imm(0))` in `Reg(0)`)
        // narrows to `FieldKey::AnyIndex` (`[*]`).
        let numeric_dyn =
            run_store_chain(Bytecode::Stobjbyvalue(Imm(0), Reg(5), Reg(0)), |_, _, _| {});
        assert!(numeric_dyn.ends_with("[*]"), "fact: {numeric_dyn}");
    }

    #[test]
    fn dynamic_load_renders_the_any_dynamic_chain() {
        let fact = run_store_chain(Bytecode::Stobjbyvalue(Imm(0), Reg(5), Reg(6)), |_, _, _| {});
        assert!(fact.ends_with("[dyn]"), "fact: {fact}");
    }

    #[test]
    fn two_step_property_read_on_whole_object_source_reaches_sink() {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let placeholder = EntityId(u16::MAX as u32);
        let (code, offsets) = abcd_isa::encode(&[
            Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = TAINT
            Bytecode::Ldobjbyname(Imm(0), placeholder),       // 1: acc = acc.a
            Bytecode::Ldobjbyname(Imm(1), placeholder),       // 2: acc = acc.b
            Bytecode::Sta(Reg(0)),                            // 3: v0 = TAINT.a.b
            Bytecode::Tryldglobalbyname(Imm(2), placeholder), // 4: acc = print
            Bytecode::Callarg1(Imm(3), Reg(0)),               // 5: print(v0)
            Bytecode::Returnundefined,                        // 6
        ])
        .unwrap();
        let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 3);
        for (insn, s) in [(0, "TAINT"), (1, "a"), (2, "b"), (4, "print")] {
            let sid = b.add_string(s);
            b.relocate_code_id(m, offsets[insn], 0, CodeEntity::String(sid))
                .unwrap();
        }
        b.deduplicate();
        let abc = b.finalize().unwrap();
        let report = run(&abc, TAINT_TO_PRINT);
        assert_eq!(report.hits.len(), 1, "{report:?}");
        assert!(report.hits[0].fact.starts_with("local v"));
    }
}

// ---- source locations (debug info → loc arms) ----

/// `func_main_0() { print(TAINT); }` with a line-42 debug program, so the
/// hit and its path steps carry source locations. `column` adds a
/// pc-0 column entry (running semantics cover the whole body). The
/// SET_FILE + source-lang pair is required: a line program that never
/// sets a file is dropped by the vendored extractor (N55).
fn debug_taint_abc(column: Option<u32>) -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = print
        Bytecode::Sta(Reg(0)),                            // 1: v0 = print
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = TAINT
        Bytecode::Sta(Reg(1)),                            // 3: v1 = tainted
        Bytecode::Lda(Reg(0)),                            // 4
        Bytecode::Callarg1(Imm(0), Reg(1)),               // 5: print(v1)
        Bytecode::Returnundefined,                        // 6
    ])
    .unwrap();
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    let print = b.add_string("print");
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(print))
        .unwrap();
    let taint = b.add_string("TAINT");
    b.relocate_code_id(m, offsets[2], 0, CodeEntity::String(taint))
        .unwrap();
    let lnp = b.create_lnp();
    let debug = b.create_debug_info(lnp, 42);
    let src = b.add_string("main.js");
    b.lnp_emit_set_file(lnp, debug, src);
    if let Some(col) = column {
        b.lnp_emit_column(lnp, debug, 0, col);
    }
    b.lnp_emit_end(lnp);
    b.method_set_debug_info(m, debug);
    b.deduplicate();
    b.finalize().expect("debug_taint_abc must finalize")
}

#[test]
fn debug_info_flows_into_hit_and_path_locations() {
    let report = run(&debug_taint_abc(Some(7)), TAINT_TO_PRINT);
    assert_eq!(report.hits.len(), 1, "{report:?}");
    let hit = &report.hits[0];
    let loc = hit.location.expect("the sink call carries a location");
    assert_eq!(loc.line, 42);
    assert_eq!(loc.column, Some(7));
    // The path's sink step carries the same location.
    let sink_step = hit.path.last().expect("a hit always carries its sink step");
    assert_eq!(
        sink_step.location.map(|l| (l.line, l.column)),
        Some((42, Some(7)))
    );
    let text = taint::render_text(&report);
    assert!(text.contains("at line 42, col 7"), "{text}");
    assert!(text.contains(" (line 42, col 7)\n"), "{text}");
}

#[test]
fn debug_info_without_column_renders_line_only() {
    let report = run(&debug_taint_abc(None), TAINT_TO_PRINT);
    let loc = report.hits[0]
        .location
        .expect("the sink call carries a location");
    assert_eq!(loc.line, 42);
    assert_eq!(loc.column, None);
    let text = taint::render_text(&report);
    assert!(text.contains("at line 42\n"), "{text}");
}

// ---- hand-built reports (renderer edge shapes) ----

/// A minimal one-hit report; `location`/`path` are the variable parts.
fn hand_built_report(
    location: Option<taint::LocReport>,
    path: Vec<taint::PathStepReport>,
) -> taint::TaintCliReport {
    taint::TaintCliReport {
        module: "m".to_string(),
        provenance: "m.abc".to_string(),
        config: taint::ConfigReport {
            sources: vec!["GlobalLoad { name: \"TAINT\" }".to_string()],
            sinks: vec!["Call { name: \"print\" }".to_string()],
            builtin_summaries: false,
            extra_summaries: 0,
            seed_all_functions: true,
            follow_returns_past_seeds: true,
            native_identity: true,
            ohos_lifecycle: true,
            max_field_chain: 5,
            alias_rung: 2,
            pta_step_budget: None,
        },
        hits: vec![taint::HitReport {
            sink: "print".to_string(),
            call: 9,
            location,
            position: "arg 0".to_string(),
            fact: "local v3".to_string(),
            seed: taint::SeedReport {
                function: 0,
                function_name: "func_main_0".to_string(),
                fact: "zero".to_string(),
            },
            path,
        }],
        stats: taint::StatsReport {
            lookups: 0,
            negative_cache_hits: 0,
            sites_body_step: 0,
            sites_native_keep: 0,
            sites_unknown: 0,
        },
        summary_hits: Default::default(),
        summary_misses: Default::default(),
        summaries_applied: Vec::new(),
        path_edges: 0,
        gap_sites_resolved: 0,
        gap_sites_unresolved: 0,
        alias_rung_used: 2,
        pta_root_sliced: false,
    }
}

#[test]
fn text_render_handles_a_hit_with_no_path() {
    // The empty-path edge of `if !h.path.is_empty()`: real hits always
    // carry the sink step, but the renderer must not invent one. (The
    // hand-built report also carries builtin_summaries = false, pinning
    // the "off" arm of the summaries line.)
    let text = taint::render_text(&hand_built_report(None, Vec::new()));
    assert!(text.contains("hits: 1"), "{text}");
    assert!(
        text.contains("summaries:       off builtin, 0 extra"),
        "{text}"
    );
    assert!(
        text.contains("sink print (call i9, arg 0) fact: local v3"),
        "{text}"
    );
    assert!(!text.contains("path:"), "{text}");
}

#[test]
fn text_render_shows_locations_without_columns() {
    let loc = taint::LocReport {
        line: 5,
        column: None,
    };
    let text = taint::render_text(&hand_built_report(
        Some(loc),
        vec![taint::PathStepReport {
            inst: 9,
            location: Some(loc),
            op: "Call".to_string(),
        }],
    ));
    assert!(text.contains("at line 5\n"), "{text}");
    assert!(text.contains("i9  Call (line 5)\n"), "{text}");
}

#[test]
fn json_render_of_multiple_reports_is_an_array() {
    let reports = [
        hand_built_report(None, Vec::new()),
        hand_built_report(None, Vec::new()),
    ];
    let out = taint::render(&reports, true).unwrap();
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    let arr = v.as_array().unwrap();
    assert_eq!(arr.len(), 2);
    assert_eq!(arr[0]["module"], "m");
    assert_eq!(arr[1]["hits"][0]["sink"], "print");
}

#[test]
fn text_render_mode_joins_multiple_reports() {
    let reports = [
        hand_built_report(None, Vec::new()),
        hand_built_report(None, Vec::new()),
    ];
    let out = taint::render(&reports, false).unwrap();
    assert_eq!(
        out.matches("module:          m (m.abc)").count(),
        2,
        "{out}"
    );
}

// ---- config: alias_flows ----

#[test]
fn alias_flows_register_as_aliasing_flows() {
    let cfg = taint_config::parse(
        r#"[[extra_summaries]]
        name = "set"
        alias_flows = [ { from = "param:0", to = "base" } ]
        "#,
    )
    .unwrap();
    let (name, arity, summary) = &cfg.extra_summaries[0];
    assert_eq!(name, "set");
    assert_eq!(*arity, None);
    assert_eq!(summary.flows.len(), 1);
    assert!(summary.flows[0].is_alias, "alias_flows set is_alias");
    assert_eq!(summary.flows[0].from, abcd_taint::Endpoint::Param(0));
    assert_eq!(summary.flows[0].to, abcd_taint::Endpoint::Base);
}

// ---- `--preset ohos` & `--link-modules` (#27) ----

#[test]
fn preset_ohos_resolves_and_rejects_unknown_presets() {
    let cfg = taint::resolve_config(None, Some("ohos")).unwrap();
    assert!(!cfg.sources.is_empty());
    assert!(!cfg.sinks.is_empty());
    assert!(cfg.ohos_lifecycle);

    let err = taint::resolve_config(None, Some("unknown_preset")).unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("unknown taint preset"), "{err}");
}

#[test]
fn report_linked_connects_cross_module_exports_to_ohos_sink() {
    use abcd_file::ModuleRecordDef;

    let placeholder = EntityId(u16::MAX as u32);

    // Module 1 (`shared/sec`): exports `getOAID()` result in slot 0.
    let sec_abc = {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let es_rec = b.add_class("L_ESModuleRecord;");
        let es_field = b.class_add_field(es_rec, "sec", Type::U32, AccessFlags::PUBLIC);
        let req_oaid = b.add_string("@ohos.identifier.oaid");
        let s_get = b.add_string("getOAID");
        let s_tok = b.add_string("tok");
        let lit = b.add_literal_array("sec_mod");
        b.literal_array_add_module_data(
            lit,
            &[req_oaid],
            &[
                ModuleRecordDef::RegularImport {
                    local_name: s_get,
                    import_name: s_get,
                    module_request_idx: 0,
                },
                ModuleRecordDef::LocalExport {
                    local_name: s_tok,
                    export_name: s_tok,
                },
            ],
        )
        .unwrap();
        b.field_set_value_literalarray(es_field, lit).unwrap();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, _) = abcd_isa::encode(&[
            Bytecode::Ldexternalmodulevar(Imm(0)),
            Bytecode::Callarg0(Imm(0)),
            Bytecode::Stmodulevar(Imm(0)),
            Bytecode::Returnundefined,
        ])
        .unwrap();
        b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 2, 3);
        b.deduplicate();
        b.finalize().unwrap()
    };

    // Module 2 (`entry/app`): imports `tok` from `../shared/sec` and logs via `@ohos.hilog.info`.
    let app_abc = {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        b.class_set_source_lang(cls, SourceLang::EcmaScript);
        let es_rec = b.add_class("L_ESModuleRecord;");
        let es_field = b.class_add_field(es_rec, "app", Type::U32, AccessFlags::PUBLIC);
        let req_sec = b.add_string("../shared/sec");
        let req_hl = b.add_string("@ohos.hilog");
        let s_tok = b.add_string("tok");
        let s_hl = b.add_string("hilog");
        let s_def = b.add_string("default");
        let lit = b.add_literal_array("app_mod");
        b.literal_array_add_module_data(
            lit,
            &[req_sec, req_hl],
            &[
                ModuleRecordDef::RegularImport {
                    local_name: s_tok,
                    import_name: s_tok,
                    module_request_idx: 0,
                },
                ModuleRecordDef::RegularImport {
                    local_name: s_hl,
                    import_name: s_def,
                    module_request_idx: 1,
                },
            ],
        )
        .unwrap();
        b.field_set_value_literalarray(es_field, lit).unwrap();
        let proto = b.create_proto(Type::Void, &[]);
        let (code, offsets) = abcd_isa::encode(&[
            Bytecode::Ldexternalmodulevar(Imm(0)),
            Bytecode::Sta(Reg(0)),
            Bytecode::Ldexternalmodulevar(Imm(1)),
            Bytecode::Sta(Reg(1)),
            Bytecode::Ldobjbyname(Imm(0), placeholder),
            Bytecode::Sta(Reg(2)),
            Bytecode::Ldai(Imm(0)),
            Bytecode::Sta(Reg(3)),
            Bytecode::LdaStr(placeholder),
            Bytecode::Sta(Reg(4)),
            Bytecode::Lda(Reg(2)),
            Bytecode::Callthis3(Imm(2), Reg(1), Reg(3), Reg(4), Reg(0)),
            Bytecode::Returnundefined,
        ])
        .unwrap();
        let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 6, 3);
        let s_info = b.add_string("info");
        b.relocate_code_id(m, offsets[4], 0, CodeEntity::String(s_info))
            .unwrap();
        let s_tag = b.add_string("TAG");
        b.relocate_code_id(m, offsets[8], 0, CodeEntity::String(s_tag))
            .unwrap();
        b.deduplicate();
        b.finalize().unwrap()
    };

    let m1 = input::InputModule {
        name: "shared/sec".to_string(),
        abc: std::sync::Arc::from(sec_abc),
        module_json: None,
        provenance: "app.app::sec.hsp".to_string(),
    };
    let m2 = input::InputModule {
        name: "entry/app".to_string(),
        abc: std::sync::Arc::from(app_abc),
        module_json: None,
        provenance: "app.app::entry.hap".to_string(),
    };
    let cfg = taint::resolve_config(None, Some("ohos")).unwrap();
    let rep = taint::report_linked(&[m1, m2], &cfg).unwrap();
    assert_eq!(rep.hits.len(), 1, "{rep:?}");
    assert_eq!(rep.hits[0].sink, "@ohos.hilog.info");
}

// ---- `--alias-rung` & `--pta-budget` / `pta_step_budget` (#34) ----

/// Multi-step heap/closure fixture so Rung-2 PTA performs >1 worklist
/// activation before converging:
/// - `sink_cb(x) { print(x); }`
/// - `invoke(box, val) { let f = box.cb; f(val); }`
/// - `func_main_0() {
///       let box = {};
///       box.cb = sink_cb;
///       invoke(box, TAINT);
///   }`
fn pta_taint_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);

    // `sink_cb(x)`: num_vregs = 2, num_args = 4 => formal 0 (`x`) is Reg(5).
    let (sink_code, sink_offsets) = abcd_isa::encode(&[
        Bytecode::Lda(Reg(5)),                            // 0: acc = x
        Bytecode::Sta(Reg(0)),                            // 1: v0 = x
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 2: acc = print
        Bytecode::Callarg1(Imm(1), Reg(0)),               // 3: print(v0)
        Bytecode::Returnundefined,                        // 4
    ])
    .unwrap();
    let sink_cb = b.class_add_method(cls, "sink_cb", proto, AccessFlags::STATIC, &sink_code, 2, 4);
    let s_print = b.add_string("print");
    b.relocate_code_id(sink_cb, sink_offsets[2], 0, CodeEntity::String(s_print))
        .unwrap();

    // `invoke(box, val)`: num_vregs = 2, num_args = 5 => formal 0 (`box`) is Reg(5), formal 1 (`val`) is Reg(6).
    let (inv_code, inv_offsets) = abcd_isa::encode(&[
        Bytecode::Lda(Reg(5)),                      // 0: acc = box
        Bytecode::Ldobjbyname(Imm(0), placeholder), // 1: acc = box.cb
        Bytecode::Sta(Reg(0)),                      // 2: v0 = f
        Bytecode::Lda(Reg(6)),                      // 3: acc = val
        Bytecode::Sta(Reg(1)),                      // 4: v1 = val
        Bytecode::Lda(Reg(0)),                      // 5: acc = f
        Bytecode::Callarg1(Imm(1), Reg(1)),         // 6: f(v1)
        Bytecode::Returnundefined,                  // 7
    ])
    .unwrap();
    let invoke = b.class_add_method(cls, "invoke", proto, AccessFlags::STATIC, &inv_code, 2, 5);
    let s_cb = b.add_string("cb");
    b.relocate_code_id(invoke, inv_offsets[1], 0, CodeEntity::String(s_cb))
        .unwrap();

    let (main_code, main_offsets) = abcd_isa::encode(&[
        Bytecode::Createemptyobject,                        // 0: acc = {}
        Bytecode::Sta(Reg(0)),                              // 1: v0 = box
        Bytecode::Definefunc(Imm(0), placeholder, Imm(1)),  // 2: acc = sink_cb
        Bytecode::Stobjbyname(Imm(1), placeholder, Reg(0)), // 3: box.cb = sink_cb
        Bytecode::Tryldglobalbyname(Imm(2), placeholder),   // 4: acc = TAINT
        Bytecode::Sta(Reg(1)),                              // 5: v1 = tainted
        Bytecode::Definefunc(Imm(3), placeholder, Imm(2)),  // 6: acc = invoke
        Bytecode::Sta(Reg(2)),                              // 7: v2 = invoke
        Bytecode::Lda(Reg(2)),                              // 8: acc = invoke
        Bytecode::Callargs2(Imm(4), Reg(0), Reg(1)),        // 9: invoke(box, v1)
        Bytecode::Returnundefined,                          // 10
    ])
    .unwrap();
    let main = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::STATIC,
        &main_code,
        4,
        3,
    );
    let s_taint = b.add_string("TAINT");
    b.relocate_code_id(main, main_offsets[2], 0, CodeEntity::Method(sink_cb))
        .unwrap();
    b.relocate_code_id(main, main_offsets[3], 0, CodeEntity::String(s_cb))
        .unwrap();
    b.relocate_code_id(main, main_offsets[4], 0, CodeEntity::String(s_taint))
        .unwrap();
    b.relocate_code_id(main, main_offsets[6], 0, CodeEntity::Method(invoke))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("pta_taint_abc must finalize")
}

#[test]
fn taint_alias_rungs_and_pta_budget_cap_degradation() {
    let abc = pta_taint_abc();

    // Rung 2 with default budget: PTA converges at rung 2 and resolves `box.cb(TAINT)` -> `sink_cb` -> `print`.
    let r2 = run(&abc, &format!("alias_rung = 2\n{TAINT_TO_PRINT}"));
    assert_eq!(r2.config.alias_rung, 2);
    assert_eq!(r2.config.pta_step_budget, None);
    assert_eq!(r2.alias_rung_used, 2);
    assert_eq!(r2.hits.len(), 1, "{r2:?}");
    let r2_text = taint::render_text(&r2);
    assert!(
        r2_text.contains("alias rung:      2 (used 2)\n"),
        "{r2_text}"
    );
    assert!(!r2_text.contains("pta budget:"), "{r2_text}");
    let r2_json: serde_json::Value =
        serde_json::from_str(&taint::render(&[r2], true).unwrap()).unwrap();
    assert!(
        r2_json["config"].get("pta_step_budget").is_none(),
        "{r2_json}"
    );

    // Rung 0 and Rung 1 via TOML: alias_rung_used matches requested rung.
    let r0 = run(&abc, &format!("alias_rung = 0\n{TAINT_TO_PRINT}"));
    assert_eq!(r0.config.alias_rung, 0);
    assert_eq!(r0.alias_rung_used, 0);

    let r1 = run(&abc, &format!("alias_rung = 1\n{TAINT_TO_PRINT}"));
    assert_eq!(r1.config.alias_rung, 1);
    assert_eq!(r1.alias_rung_used, 1);

    // Rung 2 with `pta_step_budget = 1`: budget exhaustion degrades `alias_rung_used` to 1!
    let capped = run(
        &abc,
        &format!("alias_rung = 2\npta_step_budget = 1\n{TAINT_TO_PRINT}"),
    );
    assert_eq!(capped.config.alias_rung, 2);
    assert_eq!(capped.config.pta_step_budget, Some(1));
    assert_eq!(
        capped.alias_rung_used, 1,
        "pta_step_budget = 1 must degrade alias_rung_used to 1"
    );
    let capped_text = taint::render_text(&capped);
    assert!(
        capped_text.contains("alias rung:      2 (used 1)\npta budget:      1\n"),
        "{capped_text}"
    );
    let capped_json: serde_json::Value =
        serde_json::from_str(&taint::render(&[capped], true).unwrap()).unwrap();
    assert_eq!(capped_json["config"]["pta_step_budget"], 1);
    assert_eq!(capped_json["alias_rung_used"], 1);
}

#[test]
fn cli_taint_alias_rung_and_pta_budget_override_config() {
    use abcd_cli::cli::Cli;
    use clap::Parser;

    let dir = common::tempdir("taint-pta-cli");
    let abc_path = dir.join("pta_taint.abc");
    std::fs::write(&abc_path, pta_taint_abc()).unwrap();
    let cfg_path = dir.join("taint.toml");
    std::fs::write(&cfg_path, format!("alias_rung = 2\n{TAINT_TO_PRINT}")).unwrap();

    let abc = abc_path.to_str().unwrap();
    let cfg = cfg_path.to_str().unwrap();

    for argv in [
        &["abcd", "taint", abc, "--config", cfg, "--alias-rung", "0"][..],
        &["abcd", "taint", abc, "--config", cfg, "--alias-rung", "1"][..],
        &[
            "abcd",
            "taint",
            abc,
            "--config",
            cfg,
            "--alias-rung",
            "2",
            "--pta-budget",
            "1",
            "--json",
        ][..],
    ] {
        let cli = Cli::try_parse_from(argv).expect("argv must parse");
        abcd_cli::run(cli).expect("taint dispatch must succeed");
    }
}

#[test]
fn taint_surfaces_pta_root_sliced_ohos_lifecycle_and_any_param_from_summaries() {
    // 1. Build a 513-function .abc (`func_main_0` + 512 unreferenced helpers)
    // so demand-driven Rung-2 PTA root slicing activates (`pta_root_sliced == true`),
    // while also exercising `ohos_lifecycle = false` and `any_param_from:1` summary flows.
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);

    // `func_main_0() { let r = pick_tail("safe", TAINT); print(r); }`
    let (main_code, main_offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = pick_tail
        Bytecode::Sta(Reg(0)),                            // 1: v0 = pick_tail
        Bytecode::LdaStr(placeholder),                    // 2: acc = "safe"
        Bytecode::Sta(Reg(1)),                            // 3: v1 = "safe" (arg 0)
        Bytecode::Tryldglobalbyname(Imm(1), placeholder), // 4: acc = TAINT
        Bytecode::Sta(Reg(2)),                            // 5: v2 = tainted (arg 1)
        Bytecode::Lda(Reg(0)),                            // 6: acc = pick_tail
        Bytecode::Callargs2(Imm(2), Reg(1), Reg(2)),      // 7: acc = pick_tail(v1, v2)
        Bytecode::Sta(Reg(3)),                            // 8: v3 = r
        Bytecode::Tryldglobalbyname(Imm(3), placeholder), // 9: acc = print
        Bytecode::Sta(Reg(4)),                            // 10: v4 = print
        Bytecode::Lda(Reg(4)),                            // 11: acc = print
        Bytecode::Callarg1(Imm(4), Reg(3)),               // 12: print(r)
        Bytecode::Returnundefined,                        // 13
    ])
    .unwrap();
    let main = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::STATIC,
        &main_code,
        6,
        3,
    );
    let s_pick = b.add_string("pick_tail");
    let s_safe = b.add_string("safe");
    let s_taint = b.add_string("TAINT");
    let s_print = b.add_string("print");
    b.relocate_code_id(main, main_offsets[0], 0, CodeEntity::String(s_pick))
        .unwrap();
    b.relocate_code_id(main, main_offsets[2], 0, CodeEntity::String(s_safe))
        .unwrap();
    b.relocate_code_id(main, main_offsets[4], 0, CodeEntity::String(s_taint))
        .unwrap();
    b.relocate_code_id(main, main_offsets[9], 0, CodeEntity::String(s_print))
        .unwrap();

    let (noop, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    for idx in 0..512 {
        b.class_add_method(
            cls,
            &format!("dead_helper_{idx}"),
            proto,
            AccessFlags::STATIC,
            &noop,
            1,
            3,
        );
    }
    b.deduplicate();
    let large_abc = b.finalize().expect("513-fn abc must finalize");

    // `any_param_from:1` propagates arg 1 (`TAINT`) -> `return`, with `native_identity = false`
    // and `ohos_lifecycle = false`.
    let cfg_hit = format!(
        "native_identity = false\nbuiltin_summaries = false\nohos_lifecycle = false\n\
         {TAINT_TO_PRINT}\n\
         [[extra_summaries]]\n\
         name = \"pick_tail\"\n\
         flows = [ {{ from = \"any_param_from:1\", to = \"return\" }} ]\n"
    );
    let rep = run(&large_abc, &cfg_hit);
    assert!(
        rep.pta_root_sliced,
        "513-fn module must set pta_root_sliced"
    );
    assert!(!rep.config.ohos_lifecycle);
    assert_eq!(rep.hits.len(), 1, "{rep:?}");

    let text = taint::render_text(&rep);
    assert!(text.contains("pta root sliced: true\n"), "{text}");

    let json: serde_json::Value =
        serde_json::from_str(&taint::render(&[rep], true).unwrap()).unwrap();
    assert_eq!(json["pta_root_sliced"], true);
    assert_eq!(json["config"]["ohos_lifecycle"], false);

    // Starting at index 2 (`any_param_from:2`) skips arg 1 (`TAINT`), yielding 0 hits.
    let cfg_miss = cfg_hit.replace("any_param_from:1", "any_param_from:2");
    let rep_miss = run(&large_abc, &cfg_miss);
    assert!(rep_miss.pta_root_sliced);
    assert_eq!(rep_miss.hits.len(), 0, "{rep_miss:?}");
}

/// `#74` CLI regression test: an OpenHarmony `UIAbility` `.abc` whose string
/// pool does NOT contain `"context"` (nor `"__abcd_ohos_harness__"`) renders
/// `.context` and `__abcd_ohos_harness__` cleanly — never `<sym N>` or
/// `<unnamed>` — under `abcd taint --preset ohos`.
#[test]
fn issue74_ability_without_context_string_renders_dot_context_never_sym_placeholder() {
    use abcd_file::ModuleRecordDef;

    let placeholder = EntityId(u16::MAX as u32);
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, SourceLang::EcmaScript);

    // Import `@ohos.hilog` so `@ohos.hilog.info` from `--preset ohos` acts as sink.
    let es_rec = b.add_class("L_ESModuleRecord;");
    let es_field = b.class_add_field(es_rec, "entry", Type::U32, AccessFlags::PUBLIC);
    let req_hl = b.add_string("@ohos.hilog");
    let s_hl = b.add_string("hilog");
    let s_def = b.add_string("default");
    let mod_lit = b.add_literal_array("entry_mod");
    b.literal_array_add_module_data(
        mod_lit,
        &[req_hl],
        &[ModuleRecordDef::RegularImport {
            local_name: s_hl,
            import_name: s_def,
            module_request_idx: 0,
        }],
    )
    .unwrap();
    b.field_set_value_literalarray(es_field, mod_lit).unwrap();

    let proto = b.create_proto(Type::Void, &[]);

    // Constructor `EntryAbility(func, new.target, this)`: returns `this` (`Reg(2)`).
    let (ctor_code, _) = abcd_isa::encode(&[Bytecode::Lda(Reg(2)), Bytecode::Return]).unwrap();
    let ctor = b.class_add_method(
        cls,
        "EntryAbility",
        proto,
        AccessFlags::STATIC,
        &ctor_code,
        0,
        3,
    );

    // `onCreate(func, new.target, this, want, launchParam)`:
    // `num_vregs = 6, num_args = 5` => `Reg(8)` = `this`, `Reg(9)` = `want`.
    // Logs BOTH `this` (whose `.context` field is populated by `__abcd_ohos_harness__`)
    // and `want` via `hilog.info(0, "TAG", ...)` WITHOUT mentioning `"context"`!
    let (oc_code, oc_offsets) = abcd_isa::encode(&[
        Bytecode::Ldexternalmodulevar(Imm(0)),      // 0: acc = hilog
        Bytecode::Sta(Reg(0)),                      // 1: v0 = hilog
        Bytecode::Ldobjbyname(Imm(0), placeholder), // 2: acc = hilog.info
        Bytecode::Sta(Reg(1)),                      // 3: v1 = info
        Bytecode::Ldai(Imm(0)),                     // 4: domain = 0
        Bytecode::Sta(Reg(2)),                      // 5: v2 = 0
        Bytecode::LdaStr(placeholder),              // 6: acc = "TAG"
        Bytecode::Sta(Reg(3)),                      // 7: v3 = "TAG"
        Bytecode::Lda(Reg(1)),                      // 8: acc = info
        Bytecode::Callthis3(Imm(2), Reg(0), Reg(2), Reg(3), Reg(8)), // 9: hilog.info(0, "TAG", this)
        Bytecode::Lda(Reg(1)),                                       // 10: acc = info
        Bytecode::Callthis3(Imm(4), Reg(0), Reg(2), Reg(3), Reg(9)), // 11: hilog.info(0, "TAG", want)
        Bytecode::Returnundefined,                                   // 12
    ])
    .unwrap();
    let on_create = b.class_add_method(cls, "onCreate", proto, AccessFlags::STATIC, &oc_code, 6, 5);
    let s_info = b.add_string("info");
    let s_tag = b.add_string("TAG");
    b.relocate_code_id(on_create, oc_offsets[2], 0, CodeEntity::String(s_info))
        .unwrap();
    b.relocate_code_id(on_create, oc_offsets[6], 0, CodeEntity::String(s_tag))
        .unwrap();

    // Class member buffer `[ "onCreate", on_create, affiliate=2, count=1 ]`.
    let members_lit = b.add_literal_array("ability_members");
    let s_oc = b.add_string("onCreate");
    b.literal_array_add_string(members_lit, s_oc);
    b.literal_array_add_method(members_lit, on_create);
    b.literal_array_add_method_affiliate(members_lit, 2);
    b.literal_array_add_integer(members_lit, 1);

    // `func_main_0`: `class EntryAbility extends UIAbility { onCreate(...) { ... } }`
    let (main_code, main_offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = UIAbility
        Bytecode::Sta(Reg(0)),                            // 1: v0 = UIAbility
        Bytecode::Defineclasswithbuffer(Imm(1), placeholder, placeholder, Imm(0), Reg(0)), // 2
        Bytecode::Returnundefined,                        // 3
    ])
    .unwrap();
    let main = b.class_add_method(
        cls,
        "func_main_0",
        proto,
        AccessFlags::STATIC,
        &main_code,
        2,
        3,
    );
    let s_uiab = b.add_string("UIAbility");
    b.relocate_code_id(main, main_offsets[0], 0, CodeEntity::String(s_uiab))
        .unwrap();
    b.relocate_code_id(main, main_offsets[2], 0, CodeEntity::Method(ctor))
        .unwrap();
    b.relocate_code_id(
        main,
        main_offsets[2],
        1,
        CodeEntity::LiteralArray(members_lit),
    )
    .unwrap();

    b.deduplicate();
    let ability_abc = b.finalize().expect("ability fixture must finalize");

    // Precondition: `"context"` is NOT present anywhere in the `.abc` string pool!
    let decoded = abcd_file::decode(&ability_abc).expect("decode ability fixture");
    assert_eq!(
        decoded.strings.get("context"),
        None,
        "fixture must not contain \"context\" in user strings"
    );

    let dir = common::tempdir("issue74-ability-context");
    let abc_path = dir.join("ability.abc");
    std::fs::write(&abc_path, &ability_abc).unwrap();

    // 1. Pure `--preset ohos` subprocess run: `want` hit resolves cleanly on `onCreate`
    //    and emits zero `<sym N>` placeholders.
    let want_out = std::process::Command::new(env!("CARGO_BIN_EXE_abcd"))
        .args(["taint", abc_path.to_str().unwrap(), "--preset", "ohos"])
        .output()
        .expect("spawn abcd taint --preset ohos");
    assert!(
        want_out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&want_out.stderr)
    );
    let want_stdout = String::from_utf8(want_out.stdout).expect("utf8 stdout");
    assert!(want_stdout.contains("@ohos.hilog.info"), "{want_stdout}");
    assert!(want_stdout.contains("onCreate"), "{want_stdout}");
    assert!(!want_stdout.contains("<sym "), "{want_stdout}");
    assert!(!want_stdout.contains("<unnamed>"), "{want_stdout}");

    // 2. `--preset ohos` + `OHOS_CONTEXT_GLOBAL` source: `this` carries `.context`
    //    interned solely by `PreparedModule::owned`'s lifecycle harness, and the CLI
    //    renders `.context` (never `<sym N>`) in both text and `--json` modes!
    let ctx_cfg_path = dir.join("ctx.toml");
    std::fs::write(
        &ctx_cfg_path,
        format!(
            "[[sources]]\nkind = \"global_load\"\nname = {:?}\n",
            abcd_analysis::ohos_lifecycle::OHOS_CONTEXT_GLOBAL,
        ),
    )
    .unwrap();

    for json_flag in [false, true] {
        let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_abcd"));
        cmd.args([
            "taint",
            abc_path.to_str().unwrap(),
            "--preset",
            "ohos",
            "--config",
            ctx_cfg_path.to_str().unwrap(),
        ]);
        if json_flag {
            cmd.arg("--json");
        }
        let out = cmd.output().expect("spawn abcd taint");
        assert!(
            out.status.success(),
            "json={json_flag}, stderr={}",
            String::from_utf8_lossy(&out.stderr)
        );
        let stdout = String::from_utf8(out.stdout).expect("utf8 stdout");
        assert!(
            stdout.contains(".context"),
            "expected rendered `.context` field in json={json_flag}:\n{stdout}"
        );
        assert!(
            !stdout.contains("<sym "),
            "must never render `<sym N>` in json={json_flag}:\n{stdout}"
        );
    }
}
