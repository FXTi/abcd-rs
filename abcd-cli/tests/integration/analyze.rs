//! `analyze` tests over synthesized .abc files (zero binary fixtures).

use crate::common;
use abcd_cli::analyze::{self, AnalyzeOptions};
use abcd_cli::input::{self, ModuleSelection};
use abcd_file::{AccessFlags, Builder, CodeEntity, Type};
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

const ALL: AnalyzeOptions = AnalyzeOptions {
    callgraph: true,
    dominators: true,
    alias_rung: 0,
    pta_budget: None,
};

const NONE: AnalyzeOptions = AnalyzeOptions {
    callgraph: false,
    dominators: false,
    alias_rung: 0,
    pta_budget: None,
};

/// Two methods: `helper() { return undefined; }` and
/// `func_main_0() { helper(); print(); return undefined; }` — one
/// resolved call (closure def chain) and one unknown-callee call.
fn call_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (helper_code, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    let helper = b.class_add_method(
        cls,
        "helper",
        proto,
        AccessFlags::STATIC,
        &helper_code,
        4,
        0,
    );

    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)), // 0: acc = closure(helper)
        Bytecode::Sta(Reg(0)),                             // 1: v0 = helper
        Bytecode::Lda(Reg(0)),                             // 2: acc = helper
        Bytecode::Callarg0(Imm(0)),                        // 3: helper() — resolved
        Bytecode::Tryldglobalbyname(Imm(0), placeholder),  // 4: acc = print
        Bytecode::Sta(Reg(1)),                             // 5: v1 = print
        Bytecode::Lda(Reg(1)),                             // 6: acc = print
        Bytecode::Callarg0(Imm(0)),                        // 7: print() — unknown callee
        Bytecode::Returnundefined,                         // 8
    ])
    .unwrap();
    let main = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    b.relocate_code_id(main, offsets[0], 0, CodeEntity::Method(helper))
        .unwrap();
    let print = b.add_string("print");
    b.relocate_code_id(main, offsets[4], 0, CodeEntity::String(print))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("call_abc must finalize")
}

/// `func_main_0` with a diamond CFG: entry → {then, else} → merge.
/// Dominator tree: the entry immediately dominates all three others.
fn branch_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _) = abcd_isa::encode(&[
        Bytecode::Ldtrue,          // 0
        Bytecode::Jeqz(Label(4)),  // 1: false -> else
        Bytecode::Ldundefined,     // 2: then
        Bytecode::Jmp(Label(5)),   // 3: -> merge
        Bytecode::Ldundefined,     // 4: else
        Bytecode::Returnundefined, // 5: merge
    ])
    .unwrap();
    b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    b.deduplicate();
    b.finalize().expect("branch_abc must finalize")
}

fn analyze(bytes: &[u8], name: &str, opts: AnalyzeOptions) -> analyze::AnalyzeReport {
    let modules = input::load_bytes(bytes, name, ModuleSelection::Single).unwrap();
    analyze::report(&modules[0], opts).unwrap()
}

// ---- summary / text ----

#[test]
fn text_report_has_the_summary_sections() {
    let text = analyze::render_text(&analyze(&common::tiny_abc(), "modules.abc", NONE));
    for line in [
        "module:          modules (modules.abc)",
        "functions:       1 (0 external)",
        "call sites:      0",
        "resolution:      0 internal, 0 external, 0 mixed, 0 unknown",
        "entry:           func_main_0",
    ] {
        assert!(text.contains(line), "missing {line:?} in:\n{text}");
    }
    // No optional sections without the flags.
    assert!(!text.contains("call graph:"), "{text}");
    assert!(!text.contains("dominators:"), "{text}");
}

#[test]
fn json_summary_is_machine_readable() {
    let out = analyze::render(&[analyze(&common::tiny_abc(), "modules.abc", NONE)], true).unwrap();
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(v["module"], "modules");
    assert_eq!(v["summary"]["functions"], 1);
    assert_eq!(v["summary"]["external_functions"], 0);
    assert_eq!(v["summary"]["call_sites"], 0);
    assert_eq!(v["summary"]["resolution"]["unknown"], 0);
    assert_eq!(v["summary"]["entry"], "func_main_0");
    assert!(v["summary"]["blocks"].is_u64());
    assert!(v["summary"]["instructions"].is_u64());
    // Optional sections are absent without the flags.
    assert!(v.get("callgraph").is_none());
    assert!(v.get("dominators").is_none());
}

#[test]
fn json_multi_module_renders_an_array() {
    let reports = [
        analyze(&common::tiny_abc(), "a.abc", NONE),
        analyze(&common::tiny_abc(), "b.abc", NONE),
    ];
    let out = analyze::render(&reports, true).unwrap();
    let v: serde_json::Value = serde_json::from_str(&out).unwrap();
    assert_eq!(v.as_array().unwrap().len(), 2);
}

// ---- --callgraph ----

#[test]
fn callgraph_section_lists_resolved_and_unknown_sites() {
    let report = analyze(&call_abc(), "calls.abc", ALL);
    let s = &report.summary;
    assert_eq!(s.functions, 2);
    assert_eq!(s.call_sites, 2);
    assert_eq!(s.resolution.resolved_internal, 1);
    assert_eq!(s.resolution.unknown, 1);

    let cg = report.callgraph.as_ref().unwrap();
    let main = cg
        .functions
        .iter()
        .find(|f| f.function == "func_main_0")
        .expect("func_main_0 listed");
    assert_eq!(main.sites.len(), 2, "{main:?}");

    let resolved = main
        .sites
        .iter()
        .find(|s| s.edge_kind == "resolved_value_flow")
        .expect("one resolved site");
    assert!(resolved.resolution_complete);
    assert_eq!(resolved.kind, "dynamic");
    assert_eq!(resolved.targets.len(), 1);
    assert_eq!(resolved.targets[0].name, "helper");
    assert!(!resolved.targets[0].external);

    let unknown = main
        .sites
        .iter()
        .find(|s| s.edge_kind == "unknown_callees")
        .expect("one unknown site");
    assert!(unknown.targets.is_empty());
    assert!(!unknown.resolution_complete);
}

#[test]
fn callgraph_text_renders_sites_per_function() {
    let text = analyze::render_text(&analyze(&call_abc(), "calls.abc", ALL));
    assert!(text.contains("call graph:"), "{text}");
    assert!(text.contains("func_main_0:"), "{text}");
    assert!(text.contains("helper"), "{text}");
    assert!(text.contains("<unknown callees>"), "{text}");
    assert!(text.contains("[resolved_value_flow]"), "{text}");
    assert!(text.contains("[unknown_callees]"), "{text}");
}

// ---- --dominators ----

#[test]
fn dominators_section_reports_the_tree() {
    let report = analyze(&branch_abc(), "branch.abc", ALL);
    let trees = report.dominators.as_ref().unwrap();
    assert_eq!(trees.len(), 1);
    let t = &trees[0];
    assert_eq!(t.function, "func_main_0");
    assert_eq!(t.blocks, 4);
    assert_eq!(t.reachable, 4);
    assert_eq!(t.nodes.len(), 4);
    // The diamond: exactly one root (the entry, depth 0) and every other
    // block immediately dominated by it (depth 1).
    let roots: Vec<_> = t.nodes.iter().filter(|n| n.idom.is_none()).collect();
    assert_eq!(roots.len(), 1, "{t:?}");
    assert_eq!(roots[0].depth, 0);
    let root_block = roots[0].block;
    for n in t.nodes.iter().filter(|n| n.idom.is_some()) {
        assert_eq!(n.idom, Some(root_block), "{t:?}");
        assert_eq!(n.depth, 1, "{t:?}");
    }
}

#[test]
fn dominators_text_renders_the_indented_tree() {
    let text = analyze::render_text(&analyze(&branch_abc(), "branch.abc", ALL));
    assert!(text.contains("dominators:"), "{text}");
    assert!(
        text.contains("func_main_0 (4 blocks, 4 reachable):"),
        "{text}"
    );
    // Three nodes carry an `<-` idom annotation.
    assert_eq!(text.matches(" <- b").count(), 3, "{text}");
}

#[test]
fn dominators_of_tiny_abc_is_a_single_root() {
    let report = analyze(&common::tiny_abc(), "modules.abc", ALL);
    let t = &report.dominators.as_ref().unwrap()[0];
    assert_eq!(t.reachable, 1);
    assert_eq!(t.nodes.len(), 1);
    assert_eq!(t.nodes[0].idom, None);
}

// ---- errors ----

#[test]
fn corrupt_abc_is_a_tool_error() {
    let mut bad = common::tiny_abc();
    bad.truncate(16);
    let modules = input::load_bytes(&bad, "bad.abc", ModuleSelection::Single).unwrap();
    let err = analyze::report(&modules[0], NONE).unwrap_err();
    assert_eq!(err.exit_code(), 2, "decode failure is a tool error");
}

#[test]
fn lift_failure_is_a_tool_error() {
    let modules = input::load_bytes(
        &common::lift_fail_abc(),
        "liftfail.abc",
        ModuleSelection::Single,
    )
    .unwrap();
    let err = analyze::report(&modules[0], NONE).unwrap_err();
    assert_eq!(err.exit_code(), 2, "lift failure is a tool error");
    let msg = err.to_string();
    assert!(msg.contains("failed to lift"), "{msg}");
    assert!(msg.contains("ldthisbyname"), "{msg}");
}

// ---- call-kind tags ----

/// `func_main_0() { f.apply(t, a); super-calls…; new-calls…; callinit; }` —
/// one call per non-`Dynamic` `CallKind` the lift produces (`Dynamic` is
/// covered by `call_abc`, and `Direct` has no lift-side producer). All
/// callees stay unknown; the kind tags are what matters.
fn call_kinds_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Tryldglobalbyname(Imm(0), placeholder), // 0: acc = f
        Bytecode::Sta(Reg(0)),                            // 1: v0 = f
        Bytecode::Ldundefined,                            // 2
        Bytecode::Sta(Reg(1)),                            // 3: v1 = undefined
        Bytecode::Ldundefined,                            // 4
        Bytecode::Sta(Reg(2)),                            // 5: v2 = undefined
        Bytecode::Lda(Reg(0)),                            // 6: acc = f
        Bytecode::Apply(Imm(0), Reg(1), Reg(2)),          // 7: f.apply(v1, v2)
        Bytecode::Lda(Reg(0)),                            // 8
        Bytecode::Supercallthisrange(Imm(0), Imm(1), Reg(1)), // 9: super f(v1)
        Bytecode::Lda(Reg(0)),                            // 10
        Bytecode::Supercallarrowrange(Imm(0), Imm(1), Reg(1)), // 11: arrow super f(v1)
        Bytecode::Lda(Reg(0)),                            // 12
        Bytecode::Supercallspread(Imm(0), Reg(2)),        // 13: super f(...v2)
        Bytecode::Lda(Reg(0)),                            // 14
        Bytecode::CallruntimeSupercallforwardallargs(Reg(1)), // 15
        Bytecode::Lda(Reg(0)),                            // 16
        Bytecode::Sta(Reg(3)),                            // 17: v3 = f
        Bytecode::Newobjrange(Imm(0), Imm(1), Reg(3)),    // 18: new f()
        Bytecode::Lda(Reg(0)),                            // 19: acc = f
        Bytecode::Newobjapply(Imm(0), Reg(3)),            // 20: new f(...v3)
        Bytecode::Lda(Reg(0)),                            // 21: acc = f
        Bytecode::CallruntimeCallinit(Imm(0), Reg(3)),    // 22: callinit f(v3)
        Bytecode::Returnundefined,                        // 23
    ])
    .unwrap();
    let m = b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 8, 0);
    let f = b.add_string("f");
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(f))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("call_kinds_abc must finalize")
}

#[test]
fn callgraph_reports_every_liftable_call_kind() {
    let report = analyze(&call_kinds_abc(), "kinds.abc", ALL);
    assert_eq!(report.summary.call_sites, 8);
    assert_eq!(report.summary.resolution.unknown, 8);
    let cg = report.callgraph.as_ref().unwrap();
    let main = cg
        .functions
        .iter()
        .find(|f| f.function == "func_main_0")
        .expect("func_main_0 listed");
    let kinds: Vec<&str> = main.sites.iter().map(|s| s.kind.as_str()).collect();
    assert_eq!(
        kinds,
        [
            "apply",
            "super",
            "super_arrow",
            "super_spread",
            "super_forward_all_args",
            "new",
            "new_spread",
            "class_init",
        ],
        "{main:?}"
    );
    let text = analyze::render_text(&report);
    for tag in [
        "apply call [",
        "super call [",
        "super_arrow call [",
        "super_spread call [",
        "super_forward_all_args call [",
        "new call [",
        "new_spread call [",
        "class_init call [",
    ] {
        assert!(text.contains(tag), "missing {tag:?} in:\n{text}");
    }
}

// ---- external call targets ----

#[test]
fn callgraph_text_renders_external_targets() {
    // The external-target tag lives in the renderer: a hand-built report
    // drives it (every report field is public). A synthesized .abc cannot
    // carry an external class member — the Builder writes foreign methods
    // to the foreign region where decode does not surface them as members
    // (abcd-file/tests/foreign_items.rs), and the lift reserves function
    // slots for class members only.
    let report = analyze::AnalyzeReport {
        module: "m".to_string(),
        provenance: "m.abc".to_string(),
        input_bytes: 0,
        summary: analyze::SummaryReport {
            functions: 2,
            external_functions: 1,
            blocks: 1,
            instructions: 1,
            call_sites: 1,
            resolution: analyze::ResolutionReport {
                resolved_internal: 0,
                resolved_external: 1,
                resolved_mixed: 0,
                unknown: 0,
            },
            entry: None,
        },
        pta: None,
        callgraph: Some(analyze::CallgraphReport {
            functions: vec![analyze::FunctionCallgraph {
                function_index: 0,
                function: "func_main_0".to_string(),
                sites: vec![analyze::CallSiteReport {
                    inst: 3,
                    kind: "dynamic".to_string(),
                    edge_kind: "resolved_value_flow".to_string(),
                    resolution_complete: true,
                    targets: vec![analyze::CallTarget {
                        index: 1,
                        name: "native_ext".to_string(),
                        external: true,
                    }],
                }],
            }],
        }),
        dominators: None,
    };
    let text = analyze::render_text(&report);
    assert!(text.contains("fn 1 native_ext (external)"), "{text}");
    assert!(text.contains("entry:           (none)"), "{text}");
}

// ---- entry convention ----

/// tiny_abc but the method is named `f`: no `func_main_0` convention.
fn no_entry_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = abcd_isa::encode(&[Bytecode::Return]).unwrap();
    b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 4, 0);
    b.deduplicate();
    b.finalize().expect("no_entry fixture must finalize")
}

#[test]
fn missing_entry_function_renders_none() {
    let report = analyze(&no_entry_abc(), "noentry.abc", NONE);
    assert_eq!(report.summary.entry, None);
    let text = analyze::render_text(&report);
    assert!(text.contains("entry:           (none)"), "{text}");
}

#[test]
fn render_in_text_mode_produces_the_text_report() {
    let out = analyze::render(&[analyze(&common::tiny_abc(), "modules.abc", NONE)], false).unwrap();
    assert!(
        out.contains("module:          modules (modules.abc)"),
        "{out}"
    );
    assert!(out.contains("entry:           func_main_0"), "{out}");
}

// ---- --pta, --alias-rung 0|1|2, --pta-budget (#34) ----

/// Five methods exercising progressive Rung 0 < Rung 1 < Rung 2 call-graph
/// refinement:
/// - `local_target() { return undefined; }`
/// - `remote_target() { return undefined; }`
/// - `run_cb(cb) { cb(); return undefined; }` (Rung 1 formal-param closure)
/// - `invoke(box) { let g = box.cb; g(); return undefined; }` (Rung 2 heap PTA)
/// - `func_main_0() {
///       run_cb(local_target);
///       let remote_box = {}; remote_box.cb = remote_target;
///       invoke(remote_box);
///   }`
fn pta_calls_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);

    let (ret_undef, _) = abcd_isa::encode(&[Bytecode::Returnundefined]).unwrap();
    let local_target = b.class_add_method(
        cls,
        "local_target",
        proto,
        AccessFlags::STATIC,
        &ret_undef,
        2,
        0,
    );
    let remote_target = b.class_add_method(
        cls,
        "remote_target",
        proto,
        AccessFlags::STATIC,
        &ret_undef,
        2,
        0,
    );

    // `run_cb(cb)`: num_vregs = 1, num_args = 4 => formal 0 (`cb`) is Reg(4).
    let (run_cb_code, _) = abcd_isa::encode(&[
        Bytecode::Lda(Reg(4)),      // 0: acc = cb
        Bytecode::Callarg0(Imm(0)), // 1: cb()
        Bytecode::Returnundefined,  // 2
    ])
    .unwrap();
    let run_cb = b.class_add_method(
        cls,
        "run_cb",
        proto,
        AccessFlags::STATIC,
        &run_cb_code,
        1,
        4,
    );

    // `invoke(box)`: num_vregs = 2, num_args = 4 => formal 0 (`box`) is Reg(5).
    let (invoke_code, invoke_offsets) = abcd_isa::encode(&[
        Bytecode::Lda(Reg(5)),                      // 0: acc = box
        Bytecode::Ldobjbyname(Imm(0), placeholder), // 1: acc = box.cb
        Bytecode::Sta(Reg(0)),                      // 2: v0 = g
        Bytecode::Lda(Reg(0)),                      // 3: acc = g
        Bytecode::Callarg0(Imm(1)),                 // 4: g()
        Bytecode::Returnundefined,                  // 5
    ])
    .unwrap();
    let invoke = b.class_add_method(
        cls,
        "invoke",
        proto,
        AccessFlags::STATIC,
        &invoke_code,
        2,
        4,
    );
    let s_cb = b.add_string("cb");
    b.relocate_code_id(invoke, invoke_offsets[1], 0, CodeEntity::String(s_cb))
        .unwrap();

    let (main_code, main_offsets) = abcd_isa::encode(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)), // 0: acc = local_target
        Bytecode::Sta(Reg(0)),                             // 1: v0 = local_target
        Bytecode::Definefunc(Imm(1), placeholder, Imm(1)), // 2: acc = run_cb
        Bytecode::Sta(Reg(1)),                             // 3: v1 = run_cb
        Bytecode::Lda(Reg(1)),                             // 4: acc = run_cb
        Bytecode::Callarg1(Imm(2), Reg(0)),                // 5: run_cb(local_target)
        Bytecode::Createemptyobject,                       // 6: acc = {}
        Bytecode::Sta(Reg(2)),                             // 7: v2 = remote_box
        Bytecode::Definefunc(Imm(3), placeholder, Imm(0)), // 8: acc = remote_target
        Bytecode::Stobjbyname(Imm(4), placeholder, Reg(2)), // 9: remote_box.cb = remote_target
        Bytecode::Definefunc(Imm(5), placeholder, Imm(1)), // 10: acc = invoke
        Bytecode::Sta(Reg(3)),                             // 11: v3 = invoke
        Bytecode::Lda(Reg(3)),                             // 12: acc = invoke
        Bytecode::Callarg1(Imm(6), Reg(2)),                // 13: invoke(remote_box)
        Bytecode::Returnundefined,                         // 14
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
    b.relocate_code_id(main, main_offsets[0], 0, CodeEntity::Method(local_target))
        .unwrap();
    b.relocate_code_id(main, main_offsets[2], 0, CodeEntity::Method(run_cb))
        .unwrap();
    b.relocate_code_id(main, main_offsets[8], 0, CodeEntity::Method(remote_target))
        .unwrap();
    b.relocate_code_id(main, main_offsets[9], 0, CodeEntity::String(s_cb))
        .unwrap();
    b.relocate_code_id(main, main_offsets[10], 0, CodeEntity::Method(invoke))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("pta_calls_abc must finalize")
}

#[test]
fn alias_rungs_progressively_refine_call_graph_and_report_pta_telemetry() {
    let abc = pta_calls_abc();

    // Rung 0: base CallGraph::build — `run_cb` and `invoke` resolve; `cb()` and `g()` stay unknown.
    let r0 = analyze(
        &abc,
        "pta.abc",
        AnalyzeOptions {
            callgraph: true,
            dominators: false,
            alias_rung: 0,
            pta_budget: None,
        },
    );
    assert_eq!(r0.pta, None);
    assert_eq!(r0.summary.call_sites, 4);
    assert_eq!(r0.summary.resolution.resolved_internal, 2);
    assert_eq!(r0.summary.resolution.unknown, 2);
    let r0_text = analyze::render_text(&r0);
    assert!(!r0_text.contains("pta:"), "{r0_text}");
    let r0_json: serde_json::Value =
        serde_json::from_str(&analyze::render(&[r0], true).unwrap()).unwrap();
    assert!(r0_json.get("pta").is_none(), "{r0_json}");

    // Rung 1: Rung1AliasOracle + refine_with_points_to resolves formal-param `cb()` in `run_cb`,
    // leaving interprocedural heap `box.cb` in `invoke` for Rung 2; no PTA block emitted.
    let r1 = analyze(
        &abc,
        "pta.abc",
        AnalyzeOptions {
            callgraph: true,
            dominators: false,
            alias_rung: 1,
            pta_budget: None,
        },
    );
    assert_eq!(r1.pta, None);
    assert_eq!(r1.summary.call_sites, 4);
    assert_eq!(r1.summary.resolution.resolved_internal, 3);
    assert_eq!(r1.summary.resolution.unknown, 1);
    let r1_text = analyze::render_text(&r1);
    assert!(!r1_text.contains("pta:"), "{r1_text}");

    // Rung 2 (`--pta` / `--alias-rung 2`): interprocedural PTA resolves all 4 sites.
    let r2 = analyze(
        &abc,
        "pta.abc",
        AnalyzeOptions {
            callgraph: true,
            dominators: false,
            alias_rung: 2,
            pta_budget: None,
        },
    );
    let pta = r2.pta.expect("rung 2 emits PtaReport");
    assert_eq!(pta.alias_rung_used, 2);
    assert!(!pta.capped);
    assert!(pta.activations > 1, "{pta:?}");
    assert!(pta.facts > 0, "{pta:?}");
    assert!(pta.call_edges_resolved >= 2, "{pta:?}");
    assert_eq!(r2.summary.call_sites, 4);
    assert_eq!(r2.summary.resolution.resolved_internal, 4);
    assert_eq!(r2.summary.resolution.unknown, 0);

    let r2_text = analyze::render_text(&r2);
    assert!(r2_text.contains("pta:             rung 2,"), "{r2_text}");
    assert!(!r2_text.contains(", capped"), "{r2_text}");
    let r2_json: serde_json::Value =
        serde_json::from_str(&analyze::render(&[r2], true).unwrap()).unwrap();
    assert_eq!(r2_json["pta"]["alias_rung_used"], 2);
    assert_eq!(r2_json["pta"]["capped"], false);
}

#[test]
fn pta_budget_cap_degrades_alias_rung_used_to_one() {
    let abc = pta_calls_abc();
    let r1 = analyze(
        &abc,
        "pta.abc",
        AnalyzeOptions {
            callgraph: true,
            dominators: false,
            alias_rung: 1,
            pta_budget: None,
        },
    );
    assert_eq!(r1.summary.resolution.resolved_internal, 3);
    assert_eq!(r1.summary.resolution.unknown, 1);
    let capped = analyze(
        &abc,
        "pta.abc",
        AnalyzeOptions {
            callgraph: true,
            dominators: false,
            alias_rung: 2,
            pta_budget: Some(1),
        },
    );
    let pta = capped.pta.expect("capped rung 2 still emits PtaReport");
    assert!(pta.capped, "{pta:?}");
    assert_eq!(pta.alias_rung_used, 1, "{pta:?}");
    assert_eq!(
        capped.summary.resolution.resolved_internal, r1.summary.resolution.resolved_internal,
        "capped PTA must degrade CallGraph to Rung 1"
    );
    assert_eq!(
        capped.summary.resolution.unknown,
        r1.summary.resolution.unknown
    );
    let text = analyze::render_text(&capped);
    assert!(text.contains("pta:             rung 1,"), "{text}");
    assert!(text.contains(", capped\n"), "{text}");
}

#[test]
fn invalid_alias_rung_in_analyze_options_is_a_user_error() {
    let modules = input::load_bytes(&common::tiny_abc(), "m.abc", ModuleSelection::Single).unwrap();
    let err = analyze::report(
        &modules[0],
        AnalyzeOptions {
            callgraph: false,
            dominators: false,
            alias_rung: 3,
            pta_budget: None,
        },
    )
    .unwrap_err();
    assert_eq!(err.exit_code(), 1);
    assert!(err.to_string().contains("invalid alias_rung"), "{err}");
}

#[test]
fn cli_analyze_pta_and_alias_rung_dispatch_end_to_end() {
    use abcd_cli::cli::Cli;
    use clap::Parser;

    let dir = common::tempdir("analyze-pta-cli");
    let abc_path = dir.join("pta.abc");
    std::fs::write(&abc_path, pta_calls_abc()).unwrap();
    let abc = abc_path.to_str().unwrap();

    for argv in [
        &["abcd", "analyze", abc, "--pta"][..],
        &["abcd", "analyze", abc, "--pta", "--json"][..],
        &["abcd", "analyze", abc, "--alias-rung", "0"][..],
        &["abcd", "analyze", abc, "--alias-rung", "1"][..],
        &["abcd", "analyze", abc, "--alias-rung", "2"][..],
        &[
            "abcd",
            "analyze",
            abc,
            "--pta",
            "--pta-budget",
            "1",
            "--callgraph",
        ][..],
    ] {
        let cli = Cli::try_parse_from(argv).expect("argv must parse");
        abcd_cli::run(cli).expect("analyze dispatch must succeed");
    }
}
