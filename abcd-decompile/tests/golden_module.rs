//! G2 golden tests (d-P9): module-var slot↔name resolution.
//!
//! The file format carries no slot↔name table, but two FILE FACTS pin a
//! module-var slot to its source-level binding name (never fabricated):
//!
//! 1. **TDZ guard name** — es2abc emits `throw.undefinedifholewithname
//!    "<name>"` after every read of a module-level `let`/`const` binding;
//!    the IR pairs [`Op::LoadModuleVar`] with
//!    [`Op::ThrowUndefinedIfHoleWithName`], whose `name` IS the binding
//!    name.
//! 2. **Stored named definition** — a top-level `function f`/`class C`
//!    declaration compiles to `definefunc`/`defineclass` + `stmodulevar`
//!    into the declaration's OWN slot, so a [`Op::StoreModuleVar`] whose
//!    value traces (through `Mov`/`AllocClosure` passthroughs) to a
//!    `DefineFunc`/`DefineClass` binds the slot to that definition's
//!    name.
//!
//! Conflicting evidence poisons the slot (it keeps the synthetic
//! `m{index}` fallback — honesty over coverage). Resolved names let the
//! `export { … }` records reference module-scope bindings that actually
//! EXIST in the emitted text (the dream-gate module fixtures).

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_ir::module::{ExportDecl, FunctionKind};
use abcd_ir::{Const, Op};

use common::*;

/// Decompile and strip the two-line header comment.
fn decompiled(m: &abcd_ir::Module) -> String {
    let d = decompile_module(m, &EmitOptions::default());
    let mut lines: Vec<&str> = d.text.lines().collect();
    assert!(lines.len() >= 2, "header missing:\n{}", d.text);
    let mut out = lines.split_off(2).join("\n");
    if !out.is_empty() {
        out.push('\n');
    }
    out
}

/// g01 — the test-constant-propagation shape: a plain-const module
/// variable named ONLY by its TDZ guards. Slot 0 resolves to `moduleVar`
/// (the `export { moduleVar }` record's local name), so the module-scope
/// `let moduleVar;` binding exists for the export to reference.
#[test]
fn g01_tdz_guard_names_slot() {
    let mut m = mk_module();
    let foo = add_func_named(&mut m, "foo");
    {
        let b = entry_of(&m, foo);
        let v = emit(&mut m, b, Op::LoadModuleVar { index: 0 });
        let name = intern(&mut m, "moduleVar");
        emit_void(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName { name, value: v },
        );
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }
    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        let one = load_number(&mut m, b, 1.0);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: one,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let local = intern(&mut m, "moduleVar");
    m.exports.push(ExportDecl::Local {
        local_name: local,
        export_name: local,
    });

    let got = decompiled(&m);
    let want = r#"let moduleVar;
function foo() {
  const moduleVar$1 = moduleVar;
  /* elided ThrowUndefinedIfHoleWithName: TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60) */
  return moduleVar$1;
}
function func_main_0() {
  moduleVar = 1.0;
  return;
}
export { moduleVar };
"#;
    assert_eq!(got, want);
}

/// g02 — the module-exports shape: slots named by their stored
/// definitions (`function add` through `AllocClosure`, `class Box`
/// direct) plus a const slot named by its TDZ guard (`answer`). The
/// default export's ModuleExportName `default` is NOT a binding — it
/// prints verbatim (`export { Box as default }`, never `default_`).
#[test]
fn g02_defined_names_and_default_export() {
    let mut m = mk_module();
    let ctor = add_func_kind(&mut m, "Box", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        let this = add_param(&mut m, ctor);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    let add_fn = add_func_named(&mut m, "add");
    {
        let b = entry_of(&m, add_fn);
        let a = add_param(&mut m, add_fn);
        let bb = add_param(&mut m, add_fn);
        let s = add(&mut m, b, a, bb);
        emit_void(&mut m, b, Op::Return { value: Some(s) });
    }
    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        // function add → slot 1 (through the AllocClosure passthrough).
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: add_fn,
                captures: vec![],
                length: 2,
            },
        );
        let cl = emit(&mut m, b, Op::AllocClosure { func: df });
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: cl,
            },
        );
        // const 42 → slot 2 (nameless; the TDZ guard names it).
        let c42 = load_number(&mut m, b, 42.0);
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 2,
                value: c42,
            },
        );
        // class Box → slot 0 (direct DefineClass store).
        let members = const_id(&mut m, Const::ArrayLiteral(vec![]));
        let cls = emit(
            &mut m,
            b,
            Op::DefineClass {
                ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 0,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cls,
            },
        );
        // print(answer): load slot 2 with its TDZ guard, then return it.
        let v = emit(&mut m, b, Op::LoadModuleVar { index: 2 });
        let name = intern(&mut m, "answer");
        emit_void(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName { name, value: v },
        );
        emit_void(&mut m, b, Op::Return { value: Some(v) });
    }
    for (local, export) in [("Box", "default"), ("add", "add"), ("answer", "answer")] {
        let local_name = intern(&mut m, local);
        let export_name = intern(&mut m, export);
        m.exports.push(ExportDecl::Local {
            local_name,
            export_name,
        });
    }

    let got = decompiled(&m);
    let want = r#"let Box;
let add;
let answer;
function func_main_0() {
  add = function add(p1) {
  return this + p1;
};
  answer = 42.0;
  class Box$1 {
    constructor() {
      return this;
    }
  }
  Box = Box$1;
  const answer$1 = answer;
  /* elided ThrowUndefinedIfHoleWithName: TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60) */
  return answer$1;
}
export { Box as default };
export { add };
export { answer };
"#;
    assert_eq!(got, want);
}

/// g03 — conflicting evidence poisons the slot: two TDZ guards naming
/// the same slot differently are contradictory (a slot has exactly one
/// binding), so the slot keeps its synthetic `m{index}` fallback and the
/// unresolved export prints verbatim (today's honest shape).
#[test]
fn g03_conflicting_names_fall_back() {
    let mut m = mk_module();
    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        let v0 = emit(&mut m, b, Op::LoadModuleVar { index: 0 });
        let a = intern(&mut m, "alpha");
        emit_void(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName { name: a, value: v0 },
        );
        let v1 = emit(&mut m, b, Op::LoadModuleVar { index: 0 });
        let bsym = intern(&mut m, "beta");
        emit_void(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName {
                name: bsym,
                value: v1,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(v1) });
    }
    let local = intern(&mut m, "alpha");
    m.exports.push(ExportDecl::Local {
        local_name: local,
        export_name: local,
    });

    let got = decompiled(&m);
    let want = r#"let m0;
function func_main_0() {
  /* elided ThrowUndefinedIfHoleWithName: TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60) */
  const m0$1 = m0;
  /* elided ThrowUndefinedIfHoleWithName: TDZ guard (compile-time name); emitted source has no TDZ-hole reads (§5 row 60) */
  return m0$1;
}
export { alpha };
"#;
    assert_eq!(got, want);
}

/// g04 — one binding name claimed by TWO slots is contradictory (one
/// binding = one slot): both slots keep their synthetic fallbacks.
#[test]
fn g04_duplicate_name_across_slots_falls_back() {
    let mut m = mk_module();
    let f = add_func_named(&mut m, "dup");
    {
        let b = entry_of(&m, f);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        let df0 = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: f,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: df0,
            },
        );
        let df1 = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: f,
                captures: vec![],
                length: 0,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: df1,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }

    let got = decompiled(&m);
    assert!(
        got.contains("let m0;\nlet m1;"),
        "both slots keep synthetic fallbacks:\n{got}"
    );
    assert!(got.contains("m0 ="), "slot 0 store unnamed:\n{got}");
    assert!(got.contains("m1 ="), "slot 1 store unnamed:\n{got}");
}

/// g05 — the 12.0.6+/13/24 es2panda internal-name scheme: module-scope
/// definitions carry tagged internal names (`#*#add` for a function,
/// `#~@0=#Box` for a class ctor — es2panda `util/helpers.h` tag
/// constants). The slot↔name channel demangles them (segment after the
/// LAST `#`), so the export records' local names resolve.
#[test]
fn g05_mangled_internal_names_demangle() {
    let mut m = mk_module();
    let ctor = add_func_kind(&mut m, "#~@0=#Box", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        let this = add_param(&mut m, ctor);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    let add_fn = add_func_named(&mut m, "#*#add");
    {
        let b = entry_of(&m, add_fn);
        emit_void(&mut m, b, Op::Return { value: None });
    }
    let main = add_func_named(&mut m, "func_main_0");
    {
        let b = entry_of(&m, main);
        let df = emit(
            &mut m,
            b,
            Op::DefineFunc {
                body: add_fn,
                captures: vec![],
                length: 0,
            },
        );
        let cl = emit(&mut m, b, Op::AllocClosure { func: df });
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 1,
                value: cl,
            },
        );
        let members = const_id(&mut m, Const::ArrayLiteral(vec![]));
        let cls = emit(
            &mut m,
            b,
            Op::DefineClass {
                ctor,
                heritage: None,
                members,
                member_attrs: vec![],
                count: 0,
            },
        );
        emit_void(
            &mut m,
            b,
            Op::StoreModuleVar {
                index: 0,
                value: cls,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    for (local, export) in [("Box", "default"), ("add", "add")] {
        let local_name = intern(&mut m, local);
        let export_name = intern(&mut m, export);
        m.exports.push(ExportDecl::Local {
            local_name,
            export_name,
        });
    }

    let got = decompiled(&m);
    assert!(
        got.contains("let Box;\nlet add;\n"),
        "slots resolve to demangled binding names:\n{got}"
    );
    assert!(
        got.contains("add = function"),
        "slot 1 store uses the demangled name:\n{got}"
    );
    assert!(
        got.contains("Box = ___0__Box;"),
        "slot 0 store uses the demangled binding (class keeps its verbatim display name):\n{got}"
    );
    assert!(
        got.contains("export { Box as default };\nexport { add };\n"),
        "exports resolve:\n{got}"
    );
}
