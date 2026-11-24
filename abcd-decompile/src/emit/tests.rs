#[allow(unused_imports)]
use super::{decl::*, expr::*, *};
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, InstId, ValueId};
use abcd_ir::module::ClassData;

// ── Hand-built module scaffolding (mirrors tests/common) ─────────

fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData::new(name, name));
    m
}

/// A fresh function with one empty entry block.
fn add_fn(m: &mut Module, name: &str) -> FuncId {
    let sym = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        sym,
        FunctionKind::Function,
    ));
    let b = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(id).unwrap().blocks.push(b);
    id
}

/// A fresh function whose entry block is `[return]`.
fn add_ret_fn(m: &mut Module, name: &str) -> FuncId {
    let id = add_fn(m, name);
    let b = entry_of(m, id);
    push_inst(m, b, Op::Return { value: None });
    id
}

fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    let inst = push_inst(m, b, op);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

fn add_param(m: &mut Module, f: FuncId) -> ValueId {
    let idx = m.func(f).unwrap().params.len() as u16;
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().params.push(val);
    val
}

// ── Emitter scaffolding ──────────────────────────────────────────

fn emitter<'m>(module: &'m Module, opts: &'m EmitOptions) -> Emitter<'m> {
    Emitter {
        module,
        index: None,
        opts,
        stats: DecompileStats::default(),
        fn_names: Legalizer::new(),
        current_fn_has_fallback: false,
        current_kind: FunctionKind::Function,
        class_depth: 0,
        hoisted: BTreeSet::new(),
        prepared: BTreeMap::new(),
    }
}

/// Print one expression at precedence 0 with default options.
fn ex(module: &Module, e: &Expr) -> String {
    let opts = EmitOptions::default();
    let mut em = emitter(module, &opts);
    let mut s = String::new();
    em.expr(e, 0, &mut s);
    s
}

fn id(s: &str) -> Expr {
    Expr::Ident(s.to_string())
}

fn num(x: f64) -> Expr {
    Expr::Lit(Lit::Number(x.to_bits()))
}

fn bx(e: Expr) -> Box<Expr> {
    Box::new(e)
}

// ── Unary leaf arms (2077-2088, 2109-2111, 2121-2123) ────────────

#[test]
fn unary_leaf_arms() {
    let m = mk_module();
    assert_eq!(
        ex(
            &m,
            &Expr::Unary {
                op: UnOp::LogicalNot,
                operand: bx(id("x")),
            },
        ),
        "!x"
    );
    assert_eq!(
        ex(
            &m,
            &Expr::Unary {
                op: UnOp::Void,
                operand: bx(id("x")),
            },
        ),
        "void x"
    );
    // A unary operand of the `+`-forms is parenthesized (the
    // `++x`/`--x` ambiguity rule).
    let unary_minus = || Expr::Unary {
        op: UnOp::Minus,
        operand: bx(id("x")),
    };
    assert_eq!(
        ex(
            &m,
            &Expr::Unary {
                op: UnOp::ToNumeric,
                operand: bx(unary_minus()),
            },
        ),
        "+(-x) /*ToNumeric*/"
    );
    assert_eq!(
        ex(
            &m,
            &Expr::Unary {
                op: UnOp::Minus,
                operand: bx(unary_minus()),
            },
        ),
        "-(-x)"
    );
}

// ── `**` with a unary left operand (1476-1478) ───────────────────

#[test]
fn exp_unary_left_parens() {
    let m = mk_module();
    let e = Expr::Binary {
        op: BinOp::Exp,
        left: bx(Expr::Unary {
            op: UnOp::Minus,
            operand: bx(id("x")),
        }),
        right: bx(id("y")),
    };
    assert_eq!(ex(&m, &e), "(-x) ** y");
}

// ── RegExp emission (1491-1500; the emit-level regex golden) ─────

#[test]
fn regexp_emission() {
    let m = mk_module();
    // Plain pool identity: `/` is escaped.
    let e = Expr::RegExp {
        pattern: "a/b".to_string(),
        flags: "gi".to_string(),
    };
    assert_eq!(ex(&m, &e), "/a\\/b/gi");
    let e2 = Expr::RegExp {
        pattern: "\\uD800/b".to_string(),
        flags: String::new(),
    };
    assert_eq!(ex(&m, &e2), "/\\uD800\\/b/");
}

// ── ObjectBuild entry arms (1520-1525, 1530-1533, 1551) ──────────

#[test]
fn object_build_computed_and_proto() {
    let m = mk_module();
    let e = Expr::ObjectBuild {
        entries: vec![
            ObjEntry::Computed(id("k"), num(1.0)),
            ObjEntry::Proto(id("p")),
        ],
    };
    assert_eq!(ex(&m, &e), "{[k]: 1.0, __proto__: p}");
}

#[test]
fn object_build_method_nonclosure() {
    let m = mk_module();
    // A non-closure method value prints as `key: value` (no
    // [[HomeObject]] concern); an illegal key takes string form.
    let e = Expr::ObjectBuild {
        entries: vec![
            ObjEntry::Method("m".to_string(), Expr::Lit(Lit::Null)),
            ObjEntry::Method("1x".to_string(), Expr::Lit(Lit::Null)),
        ],
    };
    assert_eq!(ex(&m, &e), "{m: null, \"1x\": null}");
}

// ── Anonymous non-arrow closure (1638-1639) ──────────────────────

#[test]
fn anonymous_non_arrow_closure() {
    let mut m = mk_module();
    let f = add_ret_fn(&mut m, "f");
    let e = Expr::Closure {
        body: f,
        name: String::new(),
        kind: FunctionKind::Function,
        captures: Vec::new(),
    };
    assert_eq!(ex(&m, &e), "function () {\n  return;\n}");
}

// ── SelfFunction (1739) ──────────────────────────────────────────

#[test]
fn self_function_emission() {
    let m = mk_module();
    assert_eq!(ex(&m, &Expr::SelfFunction("foo".to_string())), "foo");
    // A mangled internal name is sanitized.
    assert_eq!(ex(&m, &Expr::SelfFunction("#*#f".to_string())), "___f");
}

// ── TemplateObject non-string quasis (1764, 1792) ────────────────

#[test]
fn template_object_non_string_quasis() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    // A non-string raw quasi defeats the raw path; a non-string
    // cooked quasi renders via the literal renderer.
    let e = Expr::TemplateObject {
        raw: Some(vec![Lit::Null]),
        cooked: Some(vec![Lit::Number(1.0f64.to_bits())]),
    };
    em.expr(&e, 0, &mut out);
    assert_eq!(out, "\"1.0\" /*template: raw absent, cooked-only*/");
    assert_eq!(em.stats.fallback_comments["GetTemplateObject"], 1);
    assert!(em.current_fn_has_fallback);
}

// ── SetObjectWithProto (1886-1892) ───────────────────────────────

#[test]
fn set_object_with_proto_emission() {
    let m = mk_module();
    let e = Expr::SetObjectWithProto {
        obj: bx(id("o")),
        proto: bx(id("p")),
    };
    assert_eq!(
        ex(&m, &e),
        "Object.setPrototypeOf(o, p) /*NOT identical: no-setter semantics*/"
    );
}

// ── DefineGetterSetter with both accessors (1926) ────────────────

#[test]
fn define_getter_setter_both_accessors() {
    let m = mk_module();
    let e = Expr::DefineGetterSetter {
        obj: bx(id("o")),
        key: bx(Expr::Lit(Lit::String("k".to_string()))),
        getter: bx(id("g")),
        setter: bx(id("s")),
    };
    assert_eq!(
        ex(&m, &e),
        "Object.defineProperty(o, \"k\", { get: g, set: s, configurable: true }) /*DefineGetterSetterByValue: approximate*/"
    );
}

// ── WILD-ONLY arms (1741-1745, 1879-1885, 1893-1898) ─────────────

#[test]
fn wild_only_plumbing_arms() {
    let m = mk_module();
    assert_eq!(
        ex(&m, &Expr::RestArgs { start_index: 1 }),
        "[...arguments].slice(1) /*CopyRestArgs*/"
    );
    let cdp = Expr::CopyDataProps {
        dst: bx(id("d")),
        src: bx(id("s")),
    };
    assert_eq!(
        ex(&m, &cdp),
        "Object.assign(d, s) /*CopyDataProps: approximate outside a literal*/"
    );
    let asp = Expr::ArraySpread {
        dst: bx(id("a")),
        index: bx(num(0.0)),
        src: bx(id("s")),
    };
    assert_eq!(
        ex(&m, &asp),
        "a.push(...s) /*ArraySpread: result=new-index*/"
    );
}

// ── Apply without `this` (2021) + SuperSpread multi-arg (2037) ───

#[test]
fn apply_without_this_and_superspread_multi_arg() {
    let m = mk_module();
    let apply = Expr::Call {
        callee: bx(id("f")),
        this: None,
        args: vec![id("a")],
        kind: CallKind::Apply,
    };
    assert_eq!(ex(&m, &apply), "f.apply(undefined, a)");
    let sup = Expr::Call {
        callee: bx(Expr::SuperMarker),
        this: None,
        args: vec![id("a"), id("b")],
        kind: CallKind::SuperSpread,
    };
    assert_eq!(ex(&m, &sup), "super(...a, b)");
}

// ── render_lit_js MethodRef/Array/Object arms (2164-2180) ────────

#[test]
fn render_lit_js_methodref_shapes() {
    let m = mk_module();
    assert_eq!(
        ex(&m, &Expr::Lit(Lit::MethodRef(FuncId::new(3)))),
        "undefined /*method fn#3*/"
    );
    let arr = Expr::Lit(Lit::Array(vec![
        Lit::MethodRef(FuncId::new(3)),
        Lit::Number(2.0f64.to_bits()),
    ]));
    assert_eq!(ex(&m, &arr), "[undefined /*method fn#3*/, 2.0]");
    let obj = Expr::Lit(Lit::Object(vec![
        (Lit::String("k".to_string()), Lit::MethodRef(FuncId::new(3))),
        (
            Lit::String("bad key".to_string()),
            Lit::Number(1.0f64.to_bits()),
        ),
    ]));
    assert_eq!(
        ex(&m, &obj),
        "{k: undefined /*method fn#3*/, \"bad key\": 1.0}"
    );
}

// ── ERR: private ops out of class (1412-1423, 1430-1439) ─────────

#[test]
fn private_ops_out_of_class_loud_fallbacks() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    let load = Expr::PrivateLoad {
        object: bx(id("o")),
        name: "x".to_string(),
    };
    em.expr(&load, 0, &mut out);
    assert_eq!(out, "o[\"x\"] /*private #x — out-of-class*/");
    assert_eq!(em.stats.fallback_comments["LoadPrivate(out-of-class)"], 1);
    assert!(em.current_fn_has_fallback);
    out.clear();
    let test = Expr::PrivateTest {
        object: bx(id("o")),
        name: "x".to_string(),
    };
    em.expr(&test, 0, &mut out);
    assert_eq!(out, "(\"x\" in o) /*private test — out-of-class*/");
    assert_eq!(em.stats.fallback_comments["TestPrivate(out-of-class)"], 1);
    // Contrast: inside a class body the true private syntax prints.
    let mut em2 = emitter(&m, &opts);
    em2.class_depth = 1;
    out.clear();
    em2.expr(&load, 0, &mut out);
    assert_eq!(out, "o.#x");
    out.clear();
    em2.expr(&test, 0, &mut out);
    assert_eq!(out, "#x in o");
}

// ── ERR: structurer-residue statements (1065-1086) ───────────────

#[test]
fn structurer_residue_statements() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    em.emit_stmt(
        &Stmt::Branch {
            dest: BlockId::new(5),
        },
        0,
        &mut out,
    );
    em.emit_stmt(
        &Stmt::CondBranch {
            cond: id("c"),
            true_dest: BlockId::new(1),
            false_dest: BlockId::new(2),
        },
        0,
        &mut out,
    );
    em.emit_stmt(
        &Stmt::CatchBind {
            name: "e".to_string(),
        },
        0,
        &mut out,
    );
    assert_eq!(
        out,
        "/* branch B5 (structurer residue) */\n/* cond-branch B1/B2 (structurer residue) */\n/* catch-bind e (projection residue) */\n"
    );
}

// ── ERR: Stmt::Fallback loud comment (1094-1101) ─────────────────

#[test]
fn stmt_fallback_loud_comment() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    em.emit_stmt(
        &Stmt::Fallback {
            op: "XOp",
            note: "no surface form",
            loc: Some(Loc {
                line: 9,
                column: Some(3),
            }),
        },
        0,
        &mut out,
    );
    em.emit_stmt(
        &Stmt::Fallback {
            op: "YOp",
            note: "plain",
            loc: None,
        },
        0,
        &mut out,
    );
    assert_eq!(
        out,
        "/* fallback XOp: no surface form @9:3 */\n/* fallback YOp: plain */\n"
    );
    assert_eq!(em.stats.fallback_comments["XOp"], 1);
    assert_eq!(em.stats.fallback_comments["YOp"], 1);
    assert!(em.current_fn_has_fallback);
}

// ── Leaf arms: Destructure rename (811), Decl without value (831) ─

#[test]
fn leaf_destructure_rename_and_bare_decl() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    em.emit_leaf(
        &Leaf::Destructure {
            obj: id("o"),
            keys: vec![
                ("a".to_string(), "a".to_string()),
                ("b".to_string(), "c".to_string()),
            ],
            rest: "r".to_string(),
        },
        0,
        &mut out,
    );
    assert_eq!(out, "const {a, b: c, ...r} = o;\n");
    out.clear();
    em.emit_leaf(
        &Leaf::Decl {
            name: "x".to_string(),
            mutable: true,
            value: None,
        },
        0,
        &mut out,
    );
    assert_eq!(out, "let x;\n");
}

// ── Line anchors (854-856, 1125-1132) ────────────────────────────

#[test]
fn line_anchor_option() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let v = emit_val(&mut m, b, Op::LoadGlobalObject);
    let ValueDef::Inst(iid) = m.values[v.index()].def else {
        panic!("inst-defined value")
    };
    m.inst_mut(iid).unwrap().loc = Some(Loc {
        line: 42,
        column: None,
    });
    // A param-defined value has no defining inst: no anchor.
    let p = add_param(&mut m, f);
    // An inst without a source location: no anchor.
    let v2 = emit_val(&mut m, b, Op::LoadGlobalObject);
    let opts = EmitOptions {
        line_anchors: true,
        ..EmitOptions::default()
    };
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    let decl = |name: &str, value_id: ValueId| Stmt::Declare {
        name: name.to_string(),
        mutable: false,
        value: Expr::GlobalThis,
        value_id,
    };
    em.emit_stmt(&decl("t", v), 0, &mut out);
    assert_eq!(out, "// line 42\nconst t = globalThis;\n");
    out.clear();
    em.emit_stmt(&decl("u", p), 0, &mut out);
    assert_eq!(out, "const u = globalThis;\n");
    out.clear();
    em.emit_stmt(&decl("w", v2), 0, &mut out);
    assert_eq!(out, "const w = globalThis;\n");
}

// ── Object-literal statement parens (924) ────────────────────────

#[test]
fn object_literal_statement_parens() {
    let m = mk_module();
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    let obj = Expr::ObjectLit {
        entries: vec![(Lit::String("a".to_string()), Lit::Number(1.0f64.to_bits()))],
    };
    em.emit_stmt(&Stmt::Expr(obj), 0, &mut out);
    assert_eq!(out, "({a: 1.0});\n");
}

// ── Quoted class method key (1353) + member-buffer walk ──────────

#[test]
fn class_method_quoted_key() {
    let mut m = mk_module();
    let ctor = add_ret_fn(&mut m, "C");
    let m_fn = add_ret_fn(&mut m, "meth");
    let key = m.sym.intern("1bad");
    let members = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(key),
        Const::MethodRef(m_fn),
    ]));
    let opts = EmitOptions::default();
    let mut em = emitter(&m, &opts);
    let mut out = String::new();
    let decl = Stmt::Declare {
        name: "C".to_string(),
        mutable: false,
        value: Expr::Class {
            ctor,
            name: "C".to_string(),
            heritage: None,
            members,
            member_attrs: Vec::new(),
            sendable: false,
        },
        value_id: ValueId::new(0),
    };
    em.emit_stmt(&decl, 0, &mut out);
    assert_eq!(
        out,
        "class C {\n  constructor() {\n    return;\n  }\n  \"1bad\"() {\n    return;\n  }\n}\n"
    );
    assert_eq!(em.stats.classes, 1);
    assert_eq!(em.stats.class_methods, 1);
}

// ── module_facing_name sanitize arm (344) ────────────────────────

#[test]
fn module_facing_name_sanitize() {
    let mut m = mk_module();
    let x = m.sym.intern("x");
    let imp = m.sym.intern("has space");
    let req = m.sym.intern("m");
    m.imports.push(ImportDecl::Regular {
        local_name: x,
        import_name: imp,
        module_request: req,
    });
    let bad = m.sym.intern("bad name");
    m.exports.push(ExportDecl::Local {
        local_name: x,
        export_name: bad,
    });
    let out = decompile_module(&m, &EmitOptions::default());
    assert!(out.text.contains("import { has_space as x } from \"m\";\n"));
    assert!(out.text.contains("export { x as bad_name };\n"));
}

// ── collect_method_refs const shapes (383-385, 393-394, 410-413) ──

#[test]
fn consumed_functions_const_shapes() {
    let mut m = mk_module();
    let ctor_a = add_fn(&mut m, "CA");
    let m_a = add_fn(&mut m, "ma");
    let ctor_b = add_fn(&mut m, "CB");
    let m_b = add_fn(&mut m, "mb");
    let ctor_c = add_fn(&mut m, "CC");
    let m_c = add_fn(&mut m, "mc");
    let holder = add_fn(&mut m, "h");
    let hb = entry_of(&m, holder);
    let key = m.sym.intern("k");
    // Bare MethodRef members constant (383-385).
    let cid_a = m.consts.push(Const::MethodRef(m_a));
    // Flat ObjectLiteral members (393-394 via the const walker).
    let cid_b = m.consts.push(Const::ObjectLiteral {
        keys: vec![Const::String(key)],
        values: vec![Const::MethodRef(m_b)],
    });
    // ObjectLiteral NESTED in an ArrayLiteral (410-413).
    let cid_c = m
        .consts
        .push(Const::ArrayLiteral(vec![Const::ObjectLiteral {
            keys: vec![Const::String(key)],
            values: vec![Const::MethodRef(m_c)],
        }]));
    for (ctor, members) in [(ctor_a, cid_a), (ctor_b, cid_b), (ctor_c, cid_c)] {
        emit_val(
            &mut m,
            hb,
            Op::DefineClass {
                ctor,
                heritage: None,
                members,
                member_attrs: Vec::new(),
                count: 0,
            },
        );
    }
    let consumed = consumed_functions(&m);
    for f in [ctor_a, m_a, ctor_b, m_b, ctor_c, m_c] {
        assert!(consumed.contains(&f), "fn#{f:?} consumed");
    }
    assert!(!consumed.contains(&holder));
}

// ── ty_ts variants (2390-2427) ───────────────────────────────────

#[test]
fn ty_ts_variants() {
    let mut m = mk_module();
    // A descriptor class name unwraps to its simple TS name.
    m.classes[0].name = m.sym.intern("Lfoo/Bar;");
    assert_eq!(ty_ts(&m, &Ty::Any), "any");
    assert_eq!(ty_ts(&m, &Ty::Unknown), "unknown");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Undefined)), "undefined");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Null)), "null");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Bool)), "boolean");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Number)), "number");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::String)), "string");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Symbol)), "symbol");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::BigInt)), "bigint");
    assert_eq!(ty_ts(&m, &Ty::DynPrim(DynPrim::Object)), "object");
    assert_eq!(
        ty_ts(
            &m,
            &Ty::Union(vec![
                Ty::DynPrim(DynPrim::Number),
                Ty::DynPrim(DynPrim::String),
            ]),
        ),
        "number | string"
    );
    assert_eq!(ty_ts(&m, &Ty::Static(StaticTy::Void)), "void");
    assert_eq!(
        ty_ts(&m, &Ty::Static(StaticTy::Reference(ClassId::new(0)))),
        "Bar"
    );
    // The ArkTS numeric statics all surface as `number`.
    assert_eq!(ty_ts(&m, &Ty::Static(StaticTy::F64)), "number");
    assert_eq!(ty_ts(&m, &Ty::Static(StaticTy::I8)), "number");
}

// ── params_ret signature edge cases (2448, 2463-2465, 2468) ──────

#[test]
fn params_ret_signature_edges() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "g");
    let opts = EmitOptions {
        ts: true,
        ..EmitOptions::default()
    };
    let rf = |kind: FunctionKind, params: &[&str]| RecoveredFunc {
        func: f,
        name: "g".to_string(),
        kind,
        params: params.iter().map(|s| s.to_string()).collect(),
        hidden_params: 0,
        blocks: Vec::new(),
        histogram: BTreeMap::new(),
    };
    // Misaligned declaration: annotate nothing (honest skip).
    m.func_mut(f).unwrap().sig = Some(Signature {
        return_ty: None,
        param_tys: vec![Ty::Any, Ty::Any],
    });
    let em = emitter(&m, &opts);
    assert_eq!(
        em.params_ret(&rf(FunctionKind::Function, &["x"])),
        ("x".to_string(), String::new())
    );
    // TS forbids a return annotation on constructors.
    m.func_mut(f).unwrap().sig = Some(Signature {
        return_ty: Some(Ty::Any),
        param_tys: Vec::new(),
    });
    let em = emitter(&m, &opts);
    assert_eq!(
        em.params_ret(&rf(FunctionKind::Constructor, &[])),
        (String::new(), String::new())
    );
    // No declared return type: bare.
    m.func_mut(f).unwrap().sig = Some(Signature {
        return_ty: None,
        param_tys: vec![Ty::Any],
    });
    let em = emitter(&m, &opts);
    assert_eq!(
        em.params_ret(&rf(FunctionKind::Function, &["x"])),
        ("x: any".to_string(), String::new())
    );
    // Aligned + annotated.
    m.func_mut(f).unwrap().sig = Some(Signature {
        return_ty: Some(Ty::DynPrim(DynPrim::Bool)),
        param_tys: vec![Ty::DynPrim(DynPrim::Number)],
    });
    let em = emitter(&m, &opts);
    assert_eq!(
        em.params_ret(&rf(FunctionKind::Function, &["x"])),
        ("x: number".to_string(), ": boolean".to_string())
    );
}

// ── method_prefix kinds (2309-2317) ──────────────────────────────

#[test]
fn method_prefix_kinds() {
    assert_eq!(method_prefix(FunctionKind::Constructor), "");
    assert_eq!(method_prefix(FunctionKind::Getter), "get ");
    assert_eq!(method_prefix(FunctionKind::Setter), "set ");
    assert_eq!(method_prefix(FunctionKind::Async), "async ");
    assert_eq!(method_prefix(FunctionKind::Generator), "*");
    assert_eq!(method_prefix(FunctionKind::AsyncGenerator), "async *");
    assert_eq!(method_prefix(FunctionKind::Function), "");
    assert_eq!(method_prefix(FunctionKind::Arrow), "");
    assert_eq!(method_prefix(FunctionKind::AsyncArrow), "");
}

// ── fn_uses_super: super-CALL detection (2240) ───────────────────

#[test]
fn fn_uses_super_detects_super_call() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let p = add_param(&mut m, f);
    emit_val(
        &mut m,
        b,
        Op::Call {
            callee: p,
            this: None,
            args: Vec::new(),
            kind: CallKind::Super,
        },
    );
    assert!(fn_uses_super(&m, f));
    let g = add_ret_fn(&mut m, "g");
    assert!(!fn_uses_super(&m, g));
}

// ── collect_private_names arms (2268, 2276-2283) ─────────────────

#[test]
fn collect_private_names_arms() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let p = add_param(&mut m, f);
    // DefinePrivate with no resolvable name: the p{level}_{slot}
    // fallback (2268).
    push_inst(
        &mut m,
        b,
        Op::DefinePrivate {
            level: 0,
            slot: 0,
            obj: p,
            value: p,
        },
    );
    // CreatePrivateNames with a string-array constant (2276-2283).
    let nx = m.sym.intern("x");
    let ny = m.sym.intern("y");
    let names = m.consts.push(Const::ArrayLiteral(vec![
        Const::String(nx),
        Const::String(ny),
    ]));
    push_inst(&mut m, b, Op::CreatePrivateNames { count: 2, names });
    let mut set = BTreeSet::new();
    collect_private_names(&m, f, &mut set);
    assert_eq!(
        set,
        BTreeSet::from(["p0_0".to_string(), "x".to_string(), "y".to_string()])
    );
}

// ── escaped_temps leaf catch-all (2633) ──────────────────────────

#[test]
fn escaped_temps_leaf_arms() {
    let nodes = vec![
        SNode::Stmts(vec![
            // Decl without a value: the leaf catch-all arm.
            Leaf::Decl {
                name: "x".to_string(),
                mutable: false,
                value: None,
            },
            // Decl with a value / Assign: the use-collecting arms.
            Leaf::Decl {
                name: "y".to_string(),
                mutable: true,
                value: Some(id("z")),
            },
            Leaf::Assign {
                target: "w".to_string(),
                value: id("q"),
            },
        ]),
        SNode::Honest("note".to_string()),
    ];
    assert!(escaped_temps(&nodes).is_empty());
}

// ── Streaming, batching, orphan equivalence & 256 KiB stack tests (#33) ──

#[test]
fn orphan_lexenv_prefilter_matches_naive_full_module_scan() {
    use abcd_ir::function::{Catch, DebugData, LocalName, LocalScope, TryRegion};
    use abcd_ir::op::ModuleVarKind;

    let mut m = mk_module();

    // 1. Plain functions without lexvars (majority path skipped by prefilter).
    for k in 0..40 {
        let f = add_fn(&mut m, &format!("plain_{k}"));
        let b = entry_of(&m, f);
        let c = m.consts.push(Const::number(k as f64));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        push_inst(&mut m, b, Op::Return { value: Some(v) });
    }

    // 2. Function with unnamed `NewLexEnv` + `PutLexVar` / `GetLexVar` (`v0_0`, `v1_2`).
    let f_lex = add_fn(&mut m, "with_lex");
    {
        let b = entry_of(&m, f_lex);
        let _env = emit_val(&mut m, b, Op::NewLexEnv { num_vars: 2 });
        let c = m.consts.push(Const::number(1.0));
        let v = emit_val(&mut m, b, Op::LoadConst(c));
        push_inst(
            &mut m,
            b,
            Op::PutLexVar {
                level: 0,
                slot: 1,
                value: v,
            },
        );
        let rd = emit_val(&mut m, b, Op::GetLexVar { level: 3, slot: 2 });
        push_inst(&mut m, b, Op::Return { value: Some(rd) });
    }

    // 3. Function reading a global whose identifier happens to match `v<d>_<d>`.
    let f_glob = add_fn(&mut m, "with_fallback_global");
    {
        let b = entry_of(&m, f_glob);
        let gsym = m.sym.intern("v4_7");
        let g = emit_val(
            &mut m,
            b,
            Op::TryGetGlobal {
                name: gsym,
                default: None,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(g) });
    }

    // 4. Function whose debug param_names and catch local_names match `v<d>_<d>`.
    let f_dbg = add_fn(&mut m, "with_fallback_debug");
    {
        let _this = add_param(&mut m, f_dbg);
        let p = add_param(&mut m, f_dbg);
        let b0 = entry_of(&m, f_dbg);
        let bh = BlockId::new(m.blocks.len() as u32);
        m.blocks.push(Block::default());
        m.func_mut(f_dbg).unwrap().blocks.push(bh);
        m.block_mut(bh)
            .unwrap()
            .preds
            .push(abcd_ir::function::Edge {
                from: b0,
                kind: abcd_ir::function::EdgeKind::Exceptional,
            });
        let exc = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::ExceptionParam(bh),
            ty: Ty::Any,
        });
        m.func_mut(f_dbg).unwrap().try_regions.push(TryRegion {
            protected: vec![b0],
            catches: vec![Catch {
                handler: bh,
                exception: exc,
                type_idx: None,
            }],
        });
        let call_res = emit_val(
            &mut m,
            b0,
            Op::Call {
                callee: p,
                this: None,
                args: vec![],
                kind: CallKind::Direct,
            },
        );
        push_inst(
            &mut m,
            b0,
            Op::Return {
                value: Some(call_res),
            },
        );
        let handler_ret = push_inst(&mut m, bh, Op::Return { value: Some(exc) });

        let psym = m.sym.intern("v5_6");
        let lsym = m.sym.intern("v7_8");
        m.func_mut(f_dbg).unwrap().debug = Some(DebugData {
            param_names: vec![psym],
            local_names: vec![LocalName {
                name: lsym,
                ty: None,
                scope: Some(LocalScope {
                    start: handler_ret,
                    end: handler_ret,
                }),
            }],
            ..DebugData::default()
        });
    }

    // 5. Module slot resolved via TDZ guard to `v9_10`, read in a separate function.
    let f_mod_tdz = add_fn(&mut m, "mod_tdz");
    {
        let b = entry_of(&m, f_mod_tdz);
        let mv = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let msym = m.sym.intern("v9_10");
        push_inst(
            &mut m,
            b,
            Op::ThrowUndefinedIfHoleWithName {
                name: msym,
                value: mv,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(mv) });
    }
    let f_mod_reader = add_fn(&mut m, "mod_reader");
    {
        let b = entry_of(&m, f_mod_reader);
        let mv = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let mv2 = emit_val(
            &mut m,
            b,
            Op::LoadModuleVar {
                index: 0,
                kind: ModuleVarKind::Local,
            },
        );
        let sum = emit_val(
            &mut m,
            b,
            Op::BinaryOp {
                op: BinOp::Add,
                left: mv2,
                right: mv,
            },
        );
        push_inst(&mut m, b, Op::Return { value: Some(sum) });
    }

    // 5b. Named `NewLexEnvWithName` + `GetLexVar`/`PutLexVar` MUST be skipped by
    //     `func_may_have_orphan_lexenv` when no fallback `v<d>_<d>` slot exists.
    let f_named_parent = add_fn(&mut m, "named_parent");
    let f_named_child = add_fn(&mut m, "named_child");
    {
        let b_p = entry_of(&m, f_named_parent);
        let s_x = m.sym.intern("namedSlot");
        let arr = m.consts.push(Const::ArrayLiteral(vec![Const::String(s_x)]));
        let _ = emit_val(
            &mut m,
            b_p,
            Op::NewLexEnvWithName {
                num_vars: 1,
                scope_names: arr,
            },
        );
        let c = m.consts.push(Const::number(42.0));
        let v = emit_val(&mut m, b_p, Op::LoadConst(c));
        push_inst(
            &mut m,
            b_p,
            Op::PutLexVar {
                level: 0,
                slot: 0,
                value: v,
            },
        );
        let df = emit_val(
            &mut m,
            b_p,
            Op::DefineFunc {
                body: f_named_child,
                captures: vec![],
                length: 0,
            },
        );
        push_inst(&mut m, b_p, Op::Return { value: Some(df) });

        let b_c = entry_of(&m, f_named_child);
        let rd = emit_val(&mut m, b_c, Op::GetLexVar { level: 0, slot: 0 });
        push_inst(&mut m, b_c, Op::Return { value: Some(rd) });
    }

    let index = DecompileIndex::build(&m);
    assert!(!func_may_have_orphan_lexenv(
        &m,
        f_named_parent,
        &index,
        false
    ));
    assert!(!func_may_have_orphan_lexenv(
        &m,
        f_named_child,
        &index,
        false
    ));
    assert!(func_may_have_orphan_lexenv(&m, f_lex, &index, false));
    let fast = collect_module_orphan_lexenv_names(&m, &index);
    let mut naive = BTreeSet::new();
    for i in 0..m.functions.len() {
        let rf = recover_func_with_index(&m, FuncId::new(i as u32), &index);
        naive.extend(orphan_lexenv_names_in_func(&rf));
    }
    assert_eq!(fast, naive);
    for expected in ["v0_1", "v3_2", "v4_7", "v5_6", "v7_8", "v9_10"] {
        assert!(fast.contains(expected), "missing {expected} in {fast:?}");
    }
}

#[test]
fn decompile_module_to_writer_multi_batch_and_shared_inline_closures_match() {
    let mut m = mk_module();

    // Shared inline closure referenced BOTH twice inside one function (tail-dup
    // simulation) AND across multiple 256-function batches.
    let shared_inline = add_fn(&mut m, "shared_cb");
    {
        let _this = add_param(&mut m, shared_inline);
        let x = add_param(&mut m, shared_inline);
        let b = entry_of(&m, shared_inline);
        push_inst(&mut m, b, Op::Return { value: Some(x) });
    }

    // Span >2 full bounded batches AND attach 25 inline closures to several roots so
    // `next_bounded_top_batch` exercises adaptive transitive batch capping (`<= 512`).
    let total_top = MAX_BATCH_PREPARED_FUNCS + 80;
    for k in 0..total_top {
        let name = if k == total_top - 1 {
            "func_main_0".to_string()
        } else {
            format!("top_fn_{k}")
        };
        let f = add_fn(&mut m, &name);
        let _this = add_param(&mut m, f);
        let b = entry_of(&m, f);
        if k < 30 {
            let mut acc_v = None;
            for j in 0..25 {
                let child = add_fn(&mut m, &format!("inline_{k}_{j}"));
                let _cthis = add_param(&mut m, child);
                let cb = entry_of(&m, child);
                let cc = m.consts.push(Const::number((k * 100 + j) as f64));
                let cv = emit_val(&mut m, cb, Op::LoadConst(cc));
                push_inst(&mut m, cb, Op::Return { value: Some(cv) });
                let df = emit_val(
                    &mut m,
                    b,
                    Op::DefineFunc {
                        body: child,
                        captures: vec![],
                        length: 0,
                    },
                );
                let cl = emit_val(&mut m, b, Op::AllocClosure { func: df });
                acc_v = Some(match acc_v {
                    None => cl,
                    Some(prev) => emit_val(
                        &mut m,
                        b,
                        Op::BinaryOp {
                            op: BinOp::Add,
                            left: cl,
                            right: prev,
                        },
                    ),
                });
            }
            push_inst(&mut m, b, Op::Return { value: acc_v });
            continue;
        }
        if k % 100 == 0 {
            // Emit `shared_inline` twice inside the same function AND across batches.
            let df1 = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: shared_inline,
                    captures: vec![],
                    length: 1,
                },
            );
            let cl1 = emit_val(&mut m, b, Op::AllocClosure { func: df1 });
            let df2 = emit_val(
                &mut m,
                b,
                Op::DefineFunc {
                    body: shared_inline,
                    captures: vec![],
                    length: 1,
                },
            );
            let cl2 = emit_val(&mut m, b, Op::AllocClosure { func: df2 });
            let pair = emit_val(
                &mut m,
                b,
                Op::BinaryOp {
                    op: BinOp::Add,
                    left: cl2,
                    right: cl1,
                },
            );
            push_inst(&mut m, b, Op::Return { value: Some(pair) });
        } else {
            let c = m.consts.push(Const::number(k as f64));
            let v = emit_val(&mut m, b, Op::LoadConst(c));
            push_inst(&mut m, b, Op::Return { value: Some(v) });
        }
    }

    for opts in [
        EmitOptions::default(),
        EmitOptions {
            ts: true,
            call_entry: true,
            ..EmitOptions::default()
        },
    ] {
        let buffered = decompile_module(&m, &opts);
        let mut raw_out = Vec::new();
        let writer_stats =
            decompile_module_to_writer(&m, &opts, &mut raw_out).expect("stream to Vec");
        let streamed_text = String::from_utf8(raw_out).expect("UTF-8");
        assert_eq!(streamed_text, buffered.text);
        assert_eq!(writer_stats, buffered.stats);
        assert_eq!(writer_stats.functions, total_top);
    }

    // Verify I/O write error propagates cleanly without panicking.
    struct FailAfter {
        rem: usize,
    }
    impl Write for FailAfter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if self.rem == 0 {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::BrokenPipe,
                    "simulated sink failure",
                ));
            }
            let n = buf.len().min(self.rem);
            self.rem -= n;
            Ok(n)
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    let mut failing = FailAfter { rem: 128 };
    let err = decompile_module_to_writer(&m, &EmitOptions::default(), &mut failing)
        .expect_err("must surface BrokenPipe");
    assert_eq!(err.kind(), std::io::ErrorKind::BrokenPipe);
}

#[test]
fn emit_walkers_survive_deep_nesting_and_cycles_on_256k_stack() {
    // Build 5,000-deep trees (a recursive debug-build walker uses >1 MiB of call
    // stack at depth 5,000 and overflows a 256 KiB stack immediately).
    let mut deep_expr = Expr::Ident("v12_34".to_string());
    for _ in 0..5_000 {
        deep_expr = Expr::Unary {
            op: UnOp::LogicalNot,
            operand: Box::new(deep_expr),
        };
    }
    let rf = RecoveredFunc {
        func: FuncId::new(0),
        name: "deep".to_string(),
        kind: FunctionKind::Function,
        params: Vec::new(),
        hidden_params: 0,
        blocks: vec![crate::recover::BlockStmts {
            block: BlockId::new(0),
            preds: Vec::new(),
            stmts: vec![Stmt::Expr(deep_expr)],
        }],
        histogram: BTreeMap::new(),
    };

    let mut deep_const = Const::MethodRef(FuncId::new(7));
    for _ in 0..5_000 {
        deep_const = Const::ArrayLiteral(vec![deep_const]);
    }

    let mut deep_nodes = vec![SNode::Stmts(vec![
        Leaf::Raw(Stmt::ScopePush { names: vec![None] }),
        Leaf::Raw(Stmt::LexStore {
            level: 0,
            slot: 0,
            name: "inner_lex".to_string(),
            value: Expr::Temp {
                value: ValueId::new(0),
                name: "esc_tmp".to_string(),
            },
        }),
    ])];
    for step in 0..4_000 {
        deep_nodes = if step % 2 == 0 {
            vec![SNode::If {
                cond: id("c"),
                then: deep_nodes,
                otherwise: Vec::new(),
            }]
        } else {
            vec![SNode::DoWhile {
                label: None,
                body: deep_nodes,
                cond: id("c"),
            }]
        };
    }
    deep_nodes.insert(
        0,
        SNode::If {
            cond: id("c0"),
            then: vec![SNode::Stmts(vec![Leaf::Raw(Stmt::Declare {
                name: "esc_tmp".to_string(),
                mutable: false,
                value: num(1.0),
                value_id: ValueId::new(0),
            })])],
            otherwise: Vec::new(),
        },
    );

    // Flat 5,000-function DefineFunc chain + cycle (`f_4999 -> f_0`).
    let mut m = mk_module();
    let chain_len = 5_000usize;
    let chain: Vec<FuncId> = (0..chain_len)
        .map(|i| add_fn(&mut m, &format!("f_{i}")))
        .collect();
    for i in 0..chain_len {
        let b = entry_of(&m, chain[i]);
        let next = chain[(i + 1) % chain_len];
        let _ = emit_val(
            &mut m,
            b,
            Op::DefineFunc {
                body: next,
                captures: vec![],
                length: 0,
            },
        );
        push_inst(&mut m, b, Op::Return { value: None });
    }

    std::thread::scope(|s| {
        let handle = std::thread::Builder::new()
            .name("emit-256k-stack".to_string())
            .stack_size(256 * 1024)
            .spawn_scoped(s, || {
                let orphans = orphan_lexenv_names_in_func(&rf);
                assert_eq!(orphans, BTreeSet::from(["v12_34".to_string()]));

                let mut mrefs = BTreeSet::new();
                collect_method_refs_const(&deep_const, &mut mrefs);
                assert_eq!(mrefs, BTreeSet::from([FuncId::new(7)]));

                assert_eq!(lex_decls(&deep_nodes, &[]), vec!["inner_lex".to_string()]);
                assert_eq!(
                    escaped_temps(&deep_nodes),
                    BTreeSet::from(["esc_tmp".to_string()])
                );

                let batch = collect_batch_funcs(&m, &[chain[0]]);
                assert_eq!(batch.len(), chain_len);
            })
            .expect("spawn 256k scoped thread");
        handle.join().expect("256k thread must not stack-overflow");
    });

    // Iteratively dismantle deep trees so test teardown itself uses O(1) stack.
    let mut rf = rf;
    if let Some(Stmt::Expr(mut cur)) = rf.blocks[0].stmts.pop() {
        while let Expr::Unary { operand, .. } = cur {
            cur = *operand;
        }
    }
    while let Const::ArrayLiteral(mut v) = deep_const {
        deep_const = v.pop().unwrap_or(Const::Null);
    }
    while let Some(node) = deep_nodes.pop() {
        match node {
            SNode::If {
                then, otherwise, ..
            } => {
                deep_nodes.extend(then);
                deep_nodes.extend(otherwise);
            }
            SNode::DoWhile { body, .. } => deep_nodes.extend(body),
            _ => {}
        }
    }
}
