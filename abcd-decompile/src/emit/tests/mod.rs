#[allow(
    unused_imports,
    reason = "emit unit tests import sibling submodule items via wildcard"
)]
use super::{decl::*, expr::*, *};
use abcd_ir::Const;
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, InstId, ValueId};
use abcd_ir::module::ClassData;

// ── Hand-built module scaffolding (mirrors tests/common) ─────────

pub(super) fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData::new(name, name));
    m
}

/// A fresh function with one empty entry block.
pub(super) fn add_fn(m: &mut Module, name: &str) -> FuncId {
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
pub(super) fn add_ret_fn(m: &mut Module, name: &str) -> FuncId {
    let id = add_fn(m, name);
    let b = entry_of(m, id);
    push_inst(m, b, Op::Return { value: None });
    id
}

pub(super) fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

pub(super) fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
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

pub(super) fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    let inst = push_inst(m, b, op);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

pub(super) fn add_param(m: &mut Module, f: FuncId) -> ValueId {
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

pub(super) fn emitter<'m>(module: &'m Module, opts: &'m EmitOptions) -> Emitter<'m> {
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
        emitting_funcs: HashSet::new(),
        arkui_components: std::collections::HashMap::new(),
    }
}

/// Print one expression at precedence 0 with default options.
pub(super) fn ex(module: &Module, e: &Expr) -> String {
    let opts = EmitOptions::default();
    let mut em = emitter(module, &opts);
    let mut s = String::new();
    em.expr(e, 0, &mut s);
    s
}

pub(super) fn id(s: &str) -> Expr {
    Expr::Ident(s.to_string())
}

pub(super) fn num(x: f64) -> Expr {
    Expr::Lit(Lit::Number(x.to_bits()))
}

pub(super) fn bx(e: Expr) -> Box<Expr> {
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
    let ckey = m.consts.intern(Const::String(key));
    let cmfn = m.consts.intern(Const::method_ref(m_fn));
    let members = m.consts.push_array(vec![ckey, cmfn]);
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
    assert!(
        out.text
            .contains("import { \"has space\" as x } from \"m\";\n")
    );
    assert!(out.text.contains("export { x as \"bad name\" };\n"));
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
    let ckey = m.consts.intern(Const::String(key));
    let cmb = m.consts.intern(Const::method_ref(m_b));
    let cmc = m.consts.intern(Const::method_ref(m_c));
    // Bare MethodRef members constant (383-385).
    let cid_a = m.consts.push(Const::method_ref(m_a));
    // Flat ObjectLiteral members (393-394 via the const walker).
    let cid_b = m.consts.push_object(vec![ckey], vec![cmb]);
    // ObjectLiteral NESTED in an ArrayLiteral (410-413).
    let nested_obj = m.consts.push_object(vec![ckey], vec![cmc]);
    let cid_c = m.consts.push_array(vec![nested_obj]);
    for (ctor, members) in [(ctor_a, cid_a), (ctor_b, cid_b), (ctor_c, cid_c)] {
        emit_val(
            &mut m,
            hb,
            Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                ctor,
                heritage: None,
                members,
                member_attrs: Vec::new(),
                count: 0,
            })),
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
            &Ty::union(vec![
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
    let cnx = m.consts.intern(Const::String(nx));
    let cny = m.consts.intern(Const::String(ny));
    let names = m.consts.push_array(vec![cnx, cny]);
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

// ── P3-DEC-1 (#103): shared diamond ConstId DAG & ESM pre-indexing ──

#[test]
fn p3_dec1_shared_diamond_const_dag_depth_48_method_refs_memoized_o_const_pool() {
    use abcd_ir::consts::TypedArrayTag;
    use std::sync::Arc;

    let mut m = mk_module();
    let leaf_m0 = add_fn(&mut m, "leaf_m0");
    let leaf_m1 = add_fn(&mut m, "leaf_m1");

    let mut leaf_get_insts = Vec::new();
    for leaf in [leaf_m0, leaf_m1] {
        let _this = add_param(&mut m, leaf);
        let lb = entry_of(&m, leaf);
        let get_v = emit_val(
            &mut m,
            lb,
            Op::GetLexVar {
                level: 0,
                slot: 0,
                kind: abcd_ir::LexEnvKind::Plain,
            },
        );
        let ValueDef::Inst(get_iid) = m.values[get_v.index()].def else {
            panic!("inst-defined GetLexVar");
        };
        leaf_get_insts.push((leaf, get_iid));
        push_inst(&mut m, lb, Op::Return { value: Some(get_v) });
    }

    // Build a 48-level shared diamond ConstId DAG (`2^48` virtual paths) over
    // two `MethodRef` leaves, mixing `ObjectLiteral`, `ArrayLiteral`,
    // `TypedArrayLiteral`, and `LiteralBufferRef`.
    let k0_sym = m.sym.intern("m0");
    let k1_sym = m.sym.intern("m1");
    let k0 = m.consts.intern(Const::String(k0_sym));
    let k1 = m.consts.intern(Const::String(k1_sym));
    let mr0 = m.consts.intern(Const::method_ref(leaf_m0));
    let mr1 = m.consts.intern(Const::method_ref(leaf_m1));
    let mut cur = m.consts.push_object(vec![k0, k1], vec![mr0, mr1]);
    let base_dag = cur;

    for depth in 0..48 {
        cur = match depth % 4 {
            0 => m.consts.push_array(vec![cur, cur]),
            1 => m.consts.push(Const::TypedArrayLiteral {
                tag: TypedArrayTag::I32,
                items: vec![cur, cur],
            }),
            2 => m.consts.push_object(vec![k0, k1], vec![cur, cur]),
            _ => {
                let pair = m.consts.push_array(vec![cur, cur]);
                m.consts.push(Const::LiteralBufferRef(pair))
            }
        };
    }

    // Reference `cur` across 128 sites (`AllocObject`, `DefineClass`, `AllocArray`)
    // inside a parent function that pushes a named lexical frame.
    let main = add_fn(&mut m, "func_main_0");
    m.classes[0].methods.push(main);
    let _this = add_param(&mut m, main);
    let mb = entry_of(&m, main);
    let cap_sym = m.sym.intern("capturedDagBinding");
    let cap_cid = m.consts.intern(Const::String(cap_sym));
    let scope_arr = m.consts.push_array(vec![cap_cid]);
    let _ = emit_val(
        &mut m,
        mb,
        Op::NewLexEnvWithName {
            num_vars: 1,
            scope_names: scope_arr,
        },
    );

    let mut ctors = Vec::new();
    for i in 0..64 {
        let _ = emit_val(&mut m, mb, Op::AllocObject { shape: cur });
        let _ = emit_val(&mut m, mb, Op::AllocArray { shape: Some(cur) });
        if i < 16 {
            let ctor = add_ret_fn(&mut m, &format!("DagClass{i}"));
            ctors.push(ctor);
            let _ = emit_val(
                &mut m,
                mb,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor,
                    heritage: None,
                    members: cur,
                    member_attrs: Vec::new(),
                    count: 0,
                })),
            );
        }
    }
    push_inst(&mut m, mb, Op::Return { value: None });

    let start = std::time::Instant::now();
    let cache = ConstMethodRefCache::build(&m);
    assert_eq!(cache.get(cur), &[leaf_m0, leaf_m1]);
    assert!(
        Arc::ptr_eq(cache.arc_of(base_dag).unwrap(), cache.arc_of(cur).unwrap()),
        "diamond DAG levels must share the same Arc<[FuncId]>"
    );

    let index = DecompileIndex::build(&m);
    for (leaf, get_iid) in leaf_get_insts {
        let scopes = crate::names::NameScopes::build_with_index(&m, leaf, Some(&index));
        assert_eq!(scopes.name_of(get_iid), Some("capturedDagBinding"));
    }

    let consumed = consumed_functions(&m);
    assert!(consumed.contains(&leaf_m0));
    assert!(consumed.contains(&leaf_m1));
    for &ctor in &ctors {
        assert!(consumed.contains(&ctor));
    }
    assert!(!consumed.contains(&main));

    let out_a = decompile_module(&m, &EmitOptions::default());
    let out_b = decompile_module(&m, &EmitOptions::default());
    let split_out = crate::decompile_module_split(&m, &EmitOptions::default());
    let elapsed = start.elapsed();

    assert_eq!(out_a.text, out_b.text);
    assert_eq!(out_a.stats, out_b.stats);
    assert_eq!(split_out.files.len(), 1);
    assert!(
        elapsed.as_secs_f64() < 2.0,
        "O(|ConstPool|) memoized decompile on depth-48 diamond DAG took too long: {elapsed:?}"
    );
}

#[test]
fn p3_dec1_esm_preindexed_multi_import_multi_export_deterministic_parity() {
    use abcd_ir::module::{EsModule, Modifiers, ModuleRequest};
    use abcd_ir::op::ModuleVarKind;

    let mut m = Module::new();
    let cls_sym = m.sym.intern("L_GLOBAL;");
    let mut cls = ClassData::new(cls_sym, cls_sym);
    cls.source_file = Some(m.sym.intern("entry.js"));
    m.classes.push(cls);

    let req_a = m.sym.intern("./alpha");
    let req_side = m.sym.intern("./side-effect");
    let req_reexp = m.sym.intern("./reexport-only");
    let req_star = m.sym.intern("./star-mod");
    let req_orphan = m.sym.intern("./orphan-tail");

    // Include duplicate `req_a` in `module_requests` to verify dedup + exact order.
    m.module_requests = vec![
        ModuleRequest {
            specifier: req_side,
            lazy: false,
        },
        ModuleRequest {
            specifier: req_a,
            lazy: false,
        },
        ModuleRequest {
            specifier: req_a,
            lazy: false,
        },
        ModuleRequest {
            specifier: req_reexp,
            lazy: false,
        },
        ModuleRequest {
            specifier: req_star,
            lazy: false,
        },
    ];

    let s_default = m.sym.intern("default");
    let s_def_a = m.sym.intern("defA");
    let s_ns_a = m.sym.intern("nsA");
    let s_collide = m.sym.intern("hoistedFn");
    let s_kebab = m.sym.intern("kebab-imp");
    let s_kebab_loc = m.sym.intern("kebabImp");
    let s_orphan_imp = m.sym.intern("tailVal");

    m.imports = vec![
        ImportDecl::Regular {
            local_name: s_orphan_imp,
            import_name: s_orphan_imp,
            module_request: req_orphan,
        },
        ImportDecl::Regular {
            local_name: s_def_a,
            import_name: s_default,
            module_request: req_a,
        },
        ImportDecl::Namespace {
            local_name: s_ns_a,
            module_request: req_a,
        },
        ImportDecl::Regular {
            local_name: s_collide,
            import_name: s_collide,
            module_request: req_a,
        },
        ImportDecl::Regular {
            local_name: s_kebab_loc,
            import_name: s_kebab,
            module_request: req_a,
        },
    ];

    let def_impl = add_ret_fn(&mut m, "#*#MyDefaultFn");
    let hoisted_top = add_ret_fn(&mut m, "hoistedFn");
    m.func_mut(hoisted_top).unwrap().modifiers |= Modifiers::STATIC;
    m.classes[0].methods.push(def_impl);
    m.classes[0].methods.push(hoisted_top);

    let main = add_fn(&mut m, "func_main_0");
    m.func_mut(main).unwrap().modifiers |= Modifiers::STATIC;
    m.classes[0].methods.push(main);
    let mb = entry_of(&m, main);
    let _this = add_param(&mut m, main);

    // Bind slot 0 via named `DefineFunc` (`MyDefaultFn`) so `*default*` export resolves to it.
    let df = emit_val(
        &mut m,
        mb,
        Op::DefineFunc {
            body: def_impl,
            captures: Vec::new(),
            length: 0,
        },
    );
    let cl = emit_val(&mut m, mb, Op::AllocClosure { func: df });
    push_inst(
        &mut m,
        mb,
        Op::StoreModuleVar {
            index: 0,
            value: cl,
        },
    );

    // Read external slots and namespace slot, and store 64 local export slots.
    let _ext0 = emit_val(
        &mut m,
        mb,
        Op::LoadModuleVar {
            index: 1,
            kind: ModuleVarKind::External,
        },
    );
    let _ns = emit_val(&mut m, mb, Op::GetModuleNamespace { index: 1 });

    let star_default_tag = m.sym.intern("*default*");
    m.exports.push(ExportDecl::Local {
        local_name: star_default_tag,
        export_name: s_default,
    });

    for idx in 1..=64u32 {
        let name_str = format!("expVal{idx}");
        let sym = m.sym.intern(&name_str);
        let cid = m.consts.push(Const::Int32(idx));
        let v = emit_val(&mut m, mb, Op::LoadConst(cid));
        push_inst(
            &mut m,
            mb,
            Op::StoreModuleVar {
                index: idx,
                value: v,
            },
        );
        let lv = emit_val(
            &mut m,
            mb,
            Op::LoadModuleVar {
                index: idx,
                kind: ModuleVarKind::Local,
            },
        );
        push_inst(
            &mut m,
            mb,
            Op::ThrowUndefinedIfHoleWithName {
                name: sym,
                value: lv,
            },
        );
        m.exports.push(ExportDecl::Local {
            local_name: sym,
            export_name: sym,
        });
        if idx == 1 {
            let alias = m.sym.intern("expVal1Alias");
            m.exports.push(ExportDecl::Local {
                local_name: sym,
                export_name: alias,
            });
            let quoted = m.sym.intern("exp-val-1");
            m.exports.push(ExportDecl::Local {
                local_name: sym,
                export_name: quoted,
            });
        }
    }

    // Untouched local export (no bytecode instructions touch its slot).
    let untouched = m.sym.intern("untouchedLocal");
    m.exports.push(ExportDecl::Local {
        local_name: untouched,
        export_name: untouched,
    });

    let re_in = m.sym.intern("orig");
    let re_out = m.sym.intern("reexported");
    m.exports.push(ExportDecl::Indirect {
        export_name: re_out,
        import_name: re_in,
        module_request: req_reexp,
    });
    m.exports.push(ExportDecl::Star {
        module_request: req_star,
    });
    push_inst(&mut m, mb, Op::Return { value: None });

    m.classes[0].es_module = Some(EsModule {
        imports: m.imports.clone(),
        exports: m.exports.clone(),
        module_requests: m.module_requests.clone(),
    });

    let mod_a = decompile_module(&m, &EmitOptions::default());
    let mod_b = decompile_module(&m, &EmitOptions::default());
    assert_eq!(mod_a.text, mod_b.text);

    // Verify exact `module_requests` import ordering + orphan trailing import,
    // and verify `req_reexp` / `req_star` do NOT emit spurious side-effect imports.
    let expected_imports = concat!(
        "import \"./side-effect\";\n",
        "import defA from \"./alpha\";\n",
        "import * as nsA from \"./alpha\";\n",
        "import { hoistedFn as hoistedFn$1 } from \"./alpha\";\n",
        "import { \"kebab-imp\" as kebabImp } from \"./alpha\";\n",
        "import { tailVal } from \"./orphan-tail\";\n",
    );
    assert!(
        mod_a.text.contains(expected_imports),
        "imports order mismatch:\n{}",
        mod_a.text
    );
    assert!(!mod_a.text.contains("import \"./reexport-only\";"));
    assert!(!mod_a.text.contains("import \"./star-mod\";"));
    assert!(!mod_a.text.contains("let _default_;"));

    // Verify `*default*` resolved to `MyDefaultFn`, plus duplicate/aliased/quoted/indirect/star exports.
    assert!(
        mod_a.text.contains(concat!(
            "export { MyDefaultFn as default };\n",
            "export { expVal1 };\n",
            "export { expVal1 as expVal1Alias };\n",
            "export { expVal1 as \"exp-val-1\" };\n",
        )),
        "exports mismatch:\n{}",
        mod_a.text
    );
    assert!(mod_a.text.contains("export { expVal64 };\n"));
    assert!(mod_a.text.contains("export { untouchedLocal };\n"));
    assert!(mod_a.text.contains(
        "export { orig as reexported } from \"./reexport-only\";\nexport * from \"./star-mod\";\n"
    ));

    // Verify `--split-modules` parity and untouched local export predeclaration.
    let split_a = crate::decompile_module_split(&m, &EmitOptions::default());
    let split_b = crate::decompile_module_split(&m, &EmitOptions::default());
    assert_eq!(split_a.files, split_b.files);
    assert_eq!(split_a.files.len(), 1);
    let sf = &split_a.files[0];
    assert!(
        sf.text.contains(expected_imports),
        "split imports:\n{}",
        sf.text
    );
    assert!(
        sf.text.contains("let untouchedLocal;\n"),
        "split untouched local:\n{}",
        sf.text
    );
    assert!(sf.text.contains("export { MyDefaultFn as default };\n"));
    assert!(sf.text.contains("export { expVal64 };\n"));
}

// ── Streaming, batching, orphan equivalence & 256 KiB stack tests (#33) ──

mod batch_and_stack;
