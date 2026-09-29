//! `taint` tests: TOML config → analysis → rendered hits, over
//! synthesized .abc files (zero binary fixtures).

mod common;

use abcd_cli::input::{self, ModuleSelection};
use abcd_cli::{taint, taint_config};
use abcd_file::{AccessFlags, Builder, CodeEntity, Type};
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
