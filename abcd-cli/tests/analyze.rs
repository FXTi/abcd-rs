//! `analyze` tests over synthesized .abc files (zero binary fixtures).

mod common;

use abcd_cli::analyze::{self, AnalyzeOptions};
use abcd_cli::input::{self, ModuleSelection};
use abcd_file::{AccessFlags, Builder, CodeEntity, Type};
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

const ALL: AnalyzeOptions = AnalyzeOptions {
    callgraph: true,
    dominators: true,
};

const NONE: AnalyzeOptions = AnalyzeOptions {
    callgraph: false,
    dominators: false,
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
