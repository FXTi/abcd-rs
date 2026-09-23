//! B2 golden tests (d-P6): the class member-buffer attribute payloads
//! (`MemberAttrs` — static/instance placement + the buffer-tag kind)
//! drive class-body reconstruction, and the es2abc instance-initializer
//! lowering folds back into `#field = <const>;` class-field
//! declarations.
//!
//! Vendor grounding (arkcompiler_ets_runtime-master,
//! `ecmascript/jspandafile/class_info_extractor.cpp:36-42,78`): the
//! buffer's trailing i32 is the non-static member count; pairs
//! at-or-past it install on the class object (static).

mod common;

use abcd_decompile::emit::{EmitOptions, decompile_module};
use abcd_ir::module::{FunctionKind, Modifiers};
use abcd_ir::op::MemberAttrs;
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

/// A three-slot es2abc-shaped function (STATIC; params =
/// [func][new.target][this]) returning its this-role slot.
fn add_es2abc_fn(m: &mut abcd_ir::Module, name: &str, kind: FunctionKind) -> abcd_ir::FuncId {
    let f = add_func_kind(m, name, kind);
    m.func_mut(f).unwrap().modifiers = Modifiers::STATIC;
    let b = entry_of(m, f);
    add_param(m, f); // func
    add_param(m, f); // new.target
    let this = add_param(m, f); // this
    emit_void(m, b, Op::Return { value: Some(this) });
    f
}

/// b01 — static/instance placement from MemberAttrs: the member past
/// the buffer's nonStaticNum boundary prints with the `static` prefix.
#[test]
fn b01_static_method_placement() {
    let mut m = mk_module();
    let ctor = add_func_kind(&mut m, "A", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        let this = add_param(&mut m, ctor);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    let method = add_func_kind(&mut m, "move", FunctionKind::Function);
    {
        let b = entry_of(&m, method);
        let this = add_param(&mut m, method);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    let statik = add_func_kind(&mut m, "has", FunctionKind::Function);
    {
        let b = entry_of(&m, statik);
        let this = add_param(&mut m, statik);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let move_sym = intern(&mut m, "move");
    let has_sym = intern(&mut m, "has");
    // { string:"move", method, affiliate, string:"has", method,
    //   affiliate, i32:1 } — one instance member (move), one static
    // (has).
    let members = const_id(
        &mut m,
        Const::ArrayLiteral(vec![
            Const::String(move_sym),
            Const::MethodRef(method),
            Const::number(0.0),
            Const::String(has_sym),
            Const::MethodRef(statik),
            Const::number(1.0),
            Const::number(1.0),
        ]),
    );
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: vec![
                MemberAttrs {
                    is_static: false,
                    kind: FunctionKind::Function,
                },
                MemberAttrs {
                    is_static: true,
                    kind: FunctionKind::Function,
                },
            ],
            count: 0,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = decompiled(&m);
    let want = r#"function f() {
  class A {
    constructor() {
      return this;
    }
    move() {
      return this;
    }
    static has() {
      return this;
    }
    /* 3 member-buffer metadata entries skipped (name/method pairs consumed; numeric payloads are runtime metadata) */
  }
  return A;
}
"#;
    assert_eq!(got, want);
}

/// b02 — the buffer-tag kind wins over the lifted FunctionData kind:
/// a member whose buffer entry carries the GETTER tag prints `get x()`.
#[test]
fn b02_getter_kind_from_buffer_tag() {
    let mut m = mk_module();
    let ctor = add_func_kind(&mut m, "A", FunctionKind::Constructor);
    {
        let b = entry_of(&m, ctor);
        let this = add_param(&mut m, ctor);
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    // The FunctionData kind is a plain Function — the BUFFER's getter
    // tag (the MemberAttrs projection) is the placement truth.
    let getter = add_func_kind(&mut m, "x", FunctionKind::Function);
    {
        let b = entry_of(&m, getter);
        let _this = add_param(&mut m, getter);
        let one = load_number(&mut m, b, 1.0);
        emit_void(&mut m, b, Op::Return { value: Some(one) });
    }
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let x_sym = intern(&mut m, "x");
    let members = const_id(
        &mut m,
        Const::ArrayLiteral(vec![
            Const::String(x_sym),
            Const::MethodRef(getter),
            Const::number(0.0),
            Const::number(1.0),
        ]),
    );
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: vec![MemberAttrs {
                is_static: false,
                kind: FunctionKind::Getter,
            }],
            count: 0,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = decompiled(&m);
    let want = r#"function f() {
  class A {
    constructor() {
      return this;
    }
    get x() {
      return 1.0;
    }
    /* 2 member-buffer metadata entries skipped (name/method pairs consumed; numeric payloads are runtime metadata) */
  }
  return A;
}
"#;
    assert_eq!(got, want);
}

/// b03 — the es2abc instance-initializer fold: a ctor invoking (via the
/// lexical environment) an initializer that is only constant
/// `DefinePrivate` definitions folds to `#field = <const>;`
/// declarations, and the ctor's call is elided (JS class fields
/// initialize at construction — when the ctor ran the initializer).
#[test]
fn b03_instance_initializer_class_field_fold() {
    let mut m = mk_module();
    // The initializer: `this.#p0_0 = 4.0; return;` (es2abc shape).
    let init = add_func_kind(&mut m, "instance_initializer", FunctionKind::Function);
    m.func_mut(init).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, init);
        add_param(&mut m, init); // func
        add_param(&mut m, init); // new.target
        let this = add_param(&mut m, init); // this
        let four = load_number(&mut m, b, 4.0);
        emit_void(
            &mut m,
            b,
            Op::DefinePrivate {
                level: 0,
                slot: 0,
                obj: this,
                value: four,
            },
        );
        emit_void(&mut m, b, Op::Return { value: None });
    }
    // The ctor: `v0_1.call(this); return this;` (the callinit shape).
    let ctor = add_func_kind(&mut m, "A", FunctionKind::Constructor);
    m.func_mut(ctor).unwrap().modifiers = Modifiers::STATIC;
    {
        let b = entry_of(&m, ctor);
        add_param(&mut m, ctor); // func
        add_param(&mut m, ctor); // new.target
        let this = add_param(&mut m, ctor); // this
        let callee = emit(&mut m, b, Op::GetLexVar { level: 0, slot: 1 });
        let _unused = emit(
            &mut m,
            b,
            Op::Call {
                callee,
                this: Some(this),
                args: vec![],
                kind: abcd_ir::op::CallKind::Dynamic,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(this) });
    }
    // The parent: wire the initializer into the lexenv slot and define
    // the class.
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let df = emit(
        &mut m,
        b,
        Op::DefineFunc {
            body: init,
            captures: vec![],
            length: 0,
        },
    );
    let closure = emit(&mut m, b, Op::AllocClosure { func: df });
    emit_void(
        &mut m,
        b,
        Op::PutLexVar {
            level: 0,
            slot: 1,
            value: closure,
        },
    );
    let members = const_id(&mut m, Const::ArrayLiteral(vec![Const::number(0.0)]));
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = decompiled(&m);
    // The class body carries the folded field declaration; the ctor's
    // initializer call is an elided comment, never a call.
    assert!(
        got.contains("#p0_0 = 4.0; /* es2abc instance-initializer fold */"),
        "folded field declaration:\n{got}"
    );
    assert!(
        got.contains("elided Call: instance-initializer call"),
        "the ctor call elided:\n{got}"
    );
    assert!(
        !got.contains(".call(this)"),
        "no residual initializer call:\n{got}"
    );
    // The class body must NOT declare the bare `#p0_0;` too (a
    // duplicate private declaration is a SyntaxError).
    let class_body = got.split("class A").nth(1).expect("class A");
    let class_body = class_body.split('}').next().unwrap();
    assert!(
        !class_body.contains("#p0_0;\n"),
        "no duplicate bare declaration:\n{class_body}"
    );
}

/// b04 — a private brand read by a member but never initialized keeps
/// the bare `#name;` declaration (no fold without the exact pattern).
#[test]
fn b04_private_brand_bare_declaration_without_fold() {
    let mut m = mk_module();
    let ctor = add_es2abc_fn(&mut m, "A", FunctionKind::Constructor);
    let _ = ctor;
    // `has(o) { return #p0_0 in o; }` — brand test, no initializer.
    let has = add_func_kind(&mut m, "has", FunctionKind::Function);
    m.func_mut(has).unwrap().modifiers = Modifiers::STATIC;
    let obj;
    {
        let b = entry_of(&m, has);
        add_param(&mut m, has); // func
        add_param(&mut m, has); // new.target
        let _this = add_param(&mut m, has); // this
        obj = add_param(&mut m, has); // o
        let t = emit(
            &mut m,
            b,
            Op::TestPrivate {
                level: 0,
                slot: 0,
                obj,
            },
        );
        emit_void(&mut m, b, Op::Return { value: Some(t) });
    }
    let f = add_func_named(&mut m, "f");
    let b = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let has_sym = intern(&mut m, "has");
    let members = const_id(
        &mut m,
        Const::ArrayLiteral(vec![
            Const::String(has_sym),
            Const::MethodRef(has),
            Const::number(1.0),
            Const::number(0.0),
        ]),
    );
    let cls = emit(
        &mut m,
        b,
        Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: vec![MemberAttrs {
                is_static: true,
                kind: FunctionKind::Function,
            }],
            count: 0,
        },
    );
    emit_void(&mut m, b, Op::Return { value: Some(cls) });

    let got = decompiled(&m);
    assert!(got.contains("#p0_0;"), "bare brand declaration:\n{got}");
    assert!(
        got.contains("static has(p3)"),
        "static placement + the formal:\n{got}"
    );
    assert!(
        got.contains("#p0_0 in p3"),
        "the brand test in class context:\n{got}"
    );
}
