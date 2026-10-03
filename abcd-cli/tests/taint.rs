//! `taint` tests: TOML config → analysis → rendered hits, over
//! synthesized .abc files (zero binary fixtures).

mod common;

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
    assert_eq!(v["config"]["alias_rung"], 2);
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
    assert!(msg.contains("ldthisbyname"), "{msg}");
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

/// Property reads off the tainted TAINT global carry a field chain to the
/// sink: the fact renders `local vN.x` / `local vN[*]` / `local vN[dyn]`.
mod field_chain {
    use super::*;

    fn run_chain(
        load: Bytecode,
        wire: impl FnOnce(&mut Builder, abcd_file::MethodHandle, &[u32]),
    ) -> String {
        let mut b = Builder::new();
        b.set_api(12, "");
        let cls = b.add_global_class();
        let proto = b.create_proto(Type::Void, &[]);
        let placeholder = EntityId(u16::MAX as u32);
        let (code, offsets) = abcd_isa::encode(&[
            Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = TAINT
            Bytecode::Sta(Reg(0)),                            // 1: v0 = tainted
            Bytecode::Lda(Reg(0)),                            // 2: acc = obj
            load,                                             // 3: acc = obj.<key>
            Bytecode::Sta(Reg(1)),                            // 4: v1 = result
            Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 5: acc = print
            Bytecode::Callarg1(Imm(0), Reg(1)),               // 6: print(v1)
            Bytecode::Returnundefined,                        // 7
        ])
        .unwrap();
        let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
        let taint = b.add_string("TAINT");
        b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(taint))
            .unwrap();
        wire(&mut b, m, &offsets);
        let print = b.add_string("print");
        b.relocate_code_id(m, offsets[5], 0, CodeEntity::String(print))
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
        let fact = run_chain(
            Bytecode::Ldobjbyname(Imm(0), placeholder),
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
        let fact = run_chain(Bytecode::Ldobjbyindex(Imm(0), Imm(7)), |_, _, _| {});
        assert!(fact.ends_with("[*]"), "fact: {fact}");
    }

    #[test]
    fn dynamic_load_renders_the_any_dynamic_chain() {
        let fact = run_chain(Bytecode::Ldobjbyvalue(Imm(0), Reg(0)), |_, _, _| {});
        assert!(fact.ends_with("[dyn]"), "fact: {fact}");
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
            max_field_chain: 5,
            alias_rung: 2,
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
