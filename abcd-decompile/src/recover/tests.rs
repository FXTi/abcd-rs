//! Stage-A expression recovery unit tests.

use super::*;
use abcd_ir::function::{Block, DebugData, FunctionData, Inst};
use abcd_ir::module::ClassData;
use abcd_ir::ty::Ty;
use abcd_ir::{ClassId, Const};

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
    assert!(!op.has_result(), "{op:?} has a result");
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
    assert!(op.has_result(), "{op:?} has no result");
    let inst = {
        let id = InstId::new(m.insts.len() as u32);
        m.insts.push(Inst {
            op,
            result: None,
            block: b,
            loc: None,
        });
        m.block_mut(b).unwrap().insts.push(id);
        id
    };
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

fn load_const(m: &mut Module, b: BlockId, c: Const) -> ValueId {
    let cid = m.consts.push(c);
    emit_val(m, b, Op::LoadConst(cid))
}

fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    load_const(m, b, Const::number(x))
}

fn load_string(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    load_const(m, b, Const::String(sym))
}

/// A constant-defined SSA value (no instruction).
fn const_value(m: &mut Module, c: Const) -> ValueId {
    let cid = m.consts.push(c);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(cid),
        ty: Ty::Any,
    });
    val
}

fn ident(s: &str) -> Expr {
    Expr::Ident(s.to_string())
}

/// The `new ReferenceError(msg)` expression the TDZ guards emit.
fn reference_error(msg: &str) -> Stmt {
    Stmt::Throw(Expr::Call {
        callee: Box::new(Expr::Ident("ReferenceError".to_string())),
        this: None,
        args: vec![Expr::Lit(Lit::String(msg.to_string()))],
        kind: CallKind::New,
    })
}

// ── OpStat::get (88-90) ──────────────────────────────────────────

#[test]
fn opstat_get() {
    let mut s = OpStat::default();
    assert_eq!(s.get(Outcome::Expressed), 0);
    s.add(Fitness::Trivial, Outcome::Expressed);
    s.add(Fitness::Hard, Outcome::Fallback);
    s.add(Fitness::Hard, Outcome::Fallback);
    assert_eq!(s.get(Outcome::Expressed), 1);
    assert_eq!(s.get(Outcome::Fallback), 2);
    assert_eq!(s.get(Outcome::DeadPure), 0);
    assert_eq!(s.fitness, Some(Fitness::Hard));
}

// ── Debug param names, equal-length path (779) ───────────────────

#[test]
fn debug_params_equal_length() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    add_param(&mut m, f);
    add_param(&mut m, f);
    let a = m.sym.intern("a");
    let bb = m.sym.intern("b");
    m.func_mut(f).unwrap().debug = Some(DebugData {
        source_file: None,
        source_code: None,
        line_table: Vec::new(),
        column_table: Vec::new(),
        local_names: Vec::new(),
        // Same length as the IR param list: direct indexing (779).
        param_names: vec![a, bb],
        scope_names: None,
    });
    let rf = recover_func(&m, f);
    assert_eq!(rf.params, vec!["this".to_string(), "b".to_string()]);
}

// ── Provably-hole TDZ guards (1016-1025 + WithName + label arm) ──

#[test]
fn tdz_guard_provably_hole() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let hole_cid = m.consts.push(Const::Hole);
    // Hole through a Mov (chase_mov 2194-2196).
    let hole_load = emit_val(&mut m, b, Op::LoadConst(hole_cid));
    let hole_mov = emit_val(&mut m, b, Op::Mov { src: hole_load });
    let x_sym = m.sym.intern("x");
    let name_val = const_value(&mut m, Const::String(x_sym));
    push_inst(
        &mut m,
        b,
        Op::ThrowUndefinedIfHole {
            name: name_val,
            value: hole_mov,
        },
    );
    // A non-string name expression falls back to "binding" (1019).
    let num_val = const_value(&mut m, Const::number(1.0));
    let hole2 = emit_val(&mut m, b, Op::LoadConst(hole_cid));
    push_inst(
        &mut m,
        b,
        Op::ThrowUndefinedIfHole {
            name: num_val,
            value: hole2,
        },
    );
    // The with-name form materializes the same ReferenceError.
    let hole3 = emit_val(&mut m, b, Op::LoadConst(hole_cid));
    let y = m.sym.intern("y");
    push_inst(
        &mut m,
        b,
        Op::ThrowUndefinedIfHoleWithName {
            name: y,
            value: hole3,
        },
    );
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![
            reference_error("Cannot access 'x' before initialization"),
            reference_error("Cannot access 'binding' before initialization"),
            reference_error("Cannot access 'y' before initialization"),
        ]
    );
}

// ── undef_through: non-Undefined const (1303) ────────────────────

#[test]
fn define_getter_setter_undef_through_non_undef() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let obj = add_param(&mut m, f);
    let key = add_param(&mut m, f);
    // Getter is a NON-Undefined const load: the undef-through probe
    // declines (1303) and the ordinary expression path resolves it.
    let getter = load_number(&mut m, b, 1.0);
    let undef_cid = m.consts.push(Const::Undefined);
    let setter = emit_val(&mut m, b, Op::LoadConst(undef_cid));
    let set_name = load_const(&mut m, b, Const::Bool(false));
    emit_val(
        &mut m,
        b,
        Op::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
            set_name,
        },
    );
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Expr(Expr::DefineGetterSetter {
            obj: Box::new(ident("this")),
            key: Box::new(ident("p1")),
            getter: Box::new(Expr::Lit(Lit::Number(1.0f64.to_bits()))),
            setter: Box::new(Expr::Lit(Lit::Undefined)),
        })]
    );
}

// ── SetObjectWithProto statement (1322-1328) ─────────────────────

#[test]
fn set_object_with_proto_stmt() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let obj = add_param(&mut m, f);
    let proto = add_param(&mut m, f);
    push_inst(&mut m, b, Op::SetObjectWithProto { proto, obj });
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Expr(Expr::SetObjectWithProto {
            obj: Box::new(ident("this")),
            proto: Box::new(ident("p1")),
        })]
    );
    assert_eq!(rf.histogram["SetObjectWithProto"].get(Outcome::Plumbing), 1);
}

// ── Lazy catch-name mint (1512-1514) ─────────────────────────────

#[test]
fn lazy_catch_name_mint() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    // An ExceptionParam value with NO try region: `mint_catch_names`
    // never saw it, so `expr_of` mints lazily (1512-1514).
    let exc = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(b),
        ty: Ty::Any,
    });
    push_inst(&mut m, b, Op::Throw { value: exc });
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Throw(Expr::Ident("e".to_string()))]
    );
}

// ── Shape buffers: numeric-key plain pairs (1588-1597) ───────────

#[test]
fn shape_buffer_numeric_keys() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let sa = m.sym.intern("a");
    let sb = m.sym.intern("b");
    let c0 = m.consts.intern(Const::number(0.0));
    let csa = m.consts.intern(Const::String(sa));
    let c1 = m.consts.intern(Const::number(1.0));
    let csb = m.consts.intern(Const::String(sb));
    let shape = m.consts.push_array(vec![c0, csa, c1, csb]);
    let v = emit_val(&mut m, b, Op::AllocObject { shape });
    push_inst(&mut m, b, Op::Return { value: Some(v) });
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Return(Some(Expr::ObjectLit {
            entries: vec![
                (Lit::Number(0.0f64.to_bits()), Lit::String("a".to_string())),
                (Lit::Number(1.0f64.to_bits()), Lit::String("b".to_string())),
            ],
        }))]
    );
}

// ── Shape-buffer parse failures (1597/1599/1632 → 1687-1691) ─────

#[test]
fn shape_buffer_parse_failures() {
    let mut m = mk_module();
    let meth = add_fn(&mut m, "mm");
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let c0 = m.consts.intern(Const::number(0.0));
    let cmeth = m.consts.intern(Const::method_ref(meth));
    let ctrue = m.consts.intern(Const::Bool(true));
    // (a) numeric key followed by a MethodRef (1597).
    let shape_a = m.consts.push_array(vec![c0, cmeth]);
    // (b) a key that is neither String nor Number (1599).
    let shape_b = m.consts.push_array(vec![ctrue, c0]);
    // (c) a trailing key without a value (1632).
    let key_c = m.sym.intern("a");
    let ckey_c = m.consts.intern(Const::String(key_c));
    let shape_c = m.consts.push_array(vec![ckey_c]);
    for shape in [shape_a, shape_b, shape_c] {
        let v = emit_val(&mut m, b, Op::AllocObject { shape });
        push_inst(&mut m, b, Op::Return { value: Some(v) });
    }
    let rf = recover_func(&m, f);
    let fallback = Expr::Fallback {
        op: "AllocObject",
        note: "shape buffer is not a flat key/value array",
        operands: Vec::new(),
    };
    assert_eq!(
        rf.blocks[0].stmts,
        vec![
            Stmt::Return(Some(fallback.clone())),
            Stmt::Return(Some(fallback.clone())),
            Stmt::Return(Some(fallback)),
        ]
    );
    // The loud marker is the Expr::Fallback node; the histogram
    // records the op's base outcome (Expressed for AllocObject).
    assert_eq!(rf.histogram["AllocObject"].get(Outcome::Expressed), 3);
}

// ── Shape-buffer method entries: attrs skip / absent (1621-1624) ──

#[test]
fn shape_buffer_method_entries() {
    let mut m = mk_module();
    let meth = add_ret_fn(&mut m, "meth");
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let mname = m.sym.intern("m");
    let cmname = m.consts.intern(Const::String(mname));
    let cmeth = m.consts.intern(Const::method_ref(meth));
    let c7 = m.consts.intern(Const::number(7.0));
    // No trailing attrs payload: `i += 2` (1624).
    let shape_plain = m.consts.push_array(vec![cmname, cmeth]);
    // Trailing numeric attrs payload: `i += 3` (1621-1622).
    let shape_attrs = m.consts.push_array(vec![cmname, cmeth, c7]);
    for shape in [shape_plain, shape_attrs] {
        let v = emit_val(&mut m, b, Op::AllocObject { shape });
        push_inst(&mut m, b, Op::Return { value: Some(v) });
    }
    let rf = recover_func(&m, f);
    let expected = Stmt::Return(Some(Expr::ObjectBuild {
        entries: vec![ObjEntry::Method(
            "m".to_string(),
            Expr::Closure {
                body: meth,
                name: "meth".to_string(),
                kind: FunctionKind::Function,
                captures: Vec::new(),
            },
        )],
    }));
    assert_eq!(rf.blocks[0].stmts, vec![expected.clone(), expected.clone()]);
}

// ── TestProp Index/Dynamic keys (1740) ───────────────────────────

#[test]
fn testprop_index_dynamic_keys() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let obj = add_param(&mut m, f);
    let k1 = load_number(&mut m, b, 7.0);
    let t1 = emit_val(
        &mut m,
        b,
        Op::TestProp {
            object: obj,
            key: PropKey::Index(k1),
        },
    );
    let k2 = load_number(&mut m, b, 8.0);
    // Result unused but observable (Proxy `has` trap): an expression
    // statement, never dead code.
    emit_val(
        &mut m,
        b,
        Op::TestProp {
            object: obj,
            key: PropKey::Dynamic(k2),
        },
    );
    push_inst(&mut m, b, Op::Return { value: Some(t1) });
    let rf = recover_func(&m, f);
    let cmp = |bits: u64| Expr::Compare {
        op: CmpOp::In,
        left: Box::new(Expr::Lit(Lit::Number(bits))),
        right: Box::new(ident("this")),
    };
    let stmts = &rf.blocks[0].stmts;
    assert!(
        matches!(&stmts[0], Stmt::Declare { value, .. } if *value == cmp(7.0f64.to_bits())),
        "index-keyed TestProp declare: {stmts:?}"
    );
    assert_eq!(stmts[1], Stmt::Expr(cmp(8.0f64.to_bits())));
}

// ── AllocClosure: Mov-chased DefineFunc (1939-1941) + fallback ───

#[test]
fn alloc_closure_mov_chain() {
    let mut m = mk_module();
    let inner = add_ret_fn(&mut m, "inner");
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let df = emit_val(
        &mut m,
        b,
        Op::DefineFunc {
            body: inner,
            captures: Vec::new(),
            length: 0,
        },
    );
    let mv = emit_val(&mut m, b, Op::Mov { src: df });
    let clo = emit_val(&mut m, b, Op::AllocClosure { func: mv });
    push_inst(&mut m, b, Op::Return { value: Some(clo) });
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Return(Some(Expr::Closure {
            body: inner,
            name: "inner".to_string(),
            kind: FunctionKind::Function,
            captures: Vec::new(),
        }))]
    );
}

#[test]
fn alloc_closure_not_a_definefunc_chain() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    // The func operand is a number load, not a DefineFunc chain:
    // loud fallback (1951-1955).
    let c = load_number(&mut m, b, 5.0);
    let clo = emit_val(&mut m, b, Op::AllocClosure { func: c });
    push_inst(&mut m, b, Op::Return { value: Some(clo) });
    let rf = recover_func(&m, f);
    assert_eq!(
        rf.blocks[0].stmts,
        vec![Stmt::Return(Some(Expr::Fallback {
            op: "AllocClosure",
            note: "func operand is not a DefineFunc def-chain",
            operands: vec![Expr::Lit(Lit::Number(5.0f64.to_bits()))],
        }))]
    );
    // The loud marker is the Expr::Fallback node; the histogram
    // records the op's base outcome (AllocClosure is expressible —
    // the fallback is data-driven, not fitness-driven).
    assert_eq!(rf.histogram["AllocClosure"].get(Outcome::Expressed), 1);
}

// ── GetTemplateObject: non-array const literal (2046, 2211) ──────

#[test]
fn template_const_literal_non_array() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    // A const-defined literal that is NOT an array (2046); the
    // direct `ValueDef::Const` arm of `const_id_of` resolves it
    // (2211).
    let lit_sym = m.sym.intern("not-an-array");
    let lit = const_value(&mut m, Const::String(lit_sym));
    let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: lit });
    push_inst(&mut m, b, Op::Return { value: Some(g) });
    let rf = recover_func(&m, f);
    assert!(
        matches!(
            &rf.blocks[0].stmts[0],
            Stmt::Declare {
                value: Expr::TemplateObject {
                    raw: None,
                    cooked: None
                },
                ..
            }
        ),
        "{:?}",
        rf.blocks[0].stmts
    );
}

// ── GetTemplateObject: the imperative pair-array build ────────────
// (2060-2079 pair-slot evidence, 2101-2103 const-array fast path,
//  2123-2146 element stores, 2148 Mov user, 2171/2174 bad keys)

#[test]
fn template_imperative_build() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let c0 = load_number(&mut m, b, 0.0);
    let c1 = load_number(&mut m, b, 1.0);
    let c2 = load_number(&mut m, b, 2.0);
    let sa = load_string(&mut m, b, "a");
    let sb = load_string(&mut m, b, "b");
    let sc = load_string(&mut m, b, "c");
    // The cooked list as a direct const-array value (2101-2103).
    let ck_sym = m.sym.intern("ck");
    let ck_cid = m.consts.intern(Const::String(ck_sym));
    let cooked = const_value(&mut m, Const::ArrayLiteral(vec![ck_cid]));
    let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
    let raw = emit_val(&mut m, b, Op::AllocArray { shape: None });
    // Element stores into `raw`: all three store forms.
    push_inst(
        &mut m,
        b,
        Op::StoreOwnPropIdx {
            object: raw,
            index: c0,
            value: sa,
            kind: abcd_ir::OwnStoreKind::OwnProp,
        },
    );
    push_inst(
        &mut m,
        b,
        Op::StorePropDyn {
            object: raw,
            key: c1,
            value: sb,
        },
    );
    push_inst(
        &mut m,
        b,
        Op::StorePropIdx {
            object: raw,
            index: c2,
            value: sc,
        },
    );
    // A `Mov` user of the element array is accounted for (2148).
    emit_val(&mut m, b, Op::Mov { src: raw });
    // Bad-key pair stores are skipped: non-number const key (2174),
    // fractional number key (2171).
    let bad_str = load_string(&mut m, b, "nope");
    push_inst(
        &mut m,
        b,
        Op::StorePropDyn {
            object: pair,
            key: bad_str,
            value: raw,
        },
    );
    let bad_frac = load_number(&mut m, b, 1.5);
    push_inst(
        &mut m,
        b,
        Op::StorePropIdx {
            object: pair,
            index: bad_frac,
            value: raw,
        },
    );
    // The vendor pair stores: slot 0 = raw strings, slot 1 = cooked.
    push_inst(
        &mut m,
        b,
        Op::StorePropDyn {
            object: pair,
            key: c0,
            value: raw,
        },
    );
    push_inst(
        &mut m,
        b,
        Op::StorePropIdx {
            object: pair,
            index: c1,
            value: cooked,
        },
    );
    let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
    push_inst(&mut m, b, Op::Return { value: Some(g) });
    let rf = recover_func(&m, f);
    let tpl = rf.blocks[0]
        .stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Declare {
                value: Expr::TemplateObject { raw, cooked },
                ..
            } => Some((raw.clone(), cooked.clone())),
            _ => None,
        })
        .expect("a TemplateObject declare");
    assert_eq!(
        tpl,
        (
            Some(vec![
                Lit::String("a".to_string()),
                Lit::String("b".to_string()),
                Lit::String("c".to_string()),
            ]),
            Some(vec![Lit::String("ck".to_string())]),
        )
    );
}

// ── Template slot value that is not an allocation (2116) ─────────

#[test]
fn template_slot_value_not_alloc() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let p = add_param(&mut m, f);
    let c0 = load_number(&mut m, b, 0.0);
    let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
    // Slot 0 holds a PARAMETER: neither a const array nor an
    // AllocArray the walk can account for (2116).
    push_inst(
        &mut m,
        b,
        Op::StorePropDyn {
            object: pair,
            key: c0,
            value: p,
        },
    );
    let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
    push_inst(&mut m, b, Op::Return { value: Some(g) });
    let rf = recover_func(&m, f);
    let tpl = rf.blocks[0]
        .stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Declare {
                value: Expr::TemplateObject { raw, cooked },
                ..
            } => Some((raw.clone(), cooked.clone())),
            _ => None,
        })
        .expect("a TemplateObject declare");
    assert_eq!(tpl, (None, None));
}

// ── Template slot value that is a non-array const (2103) ─────────

#[test]
fn template_slot_value_non_array_const() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let c0 = load_number(&mut m, b, 0.0);
    let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
    // Slot 0 holds a const STRING: the const fast path of
    // `string_elems_of` declines non-array literals (2103).
    let s_sym = m.sym.intern("s");
    let slot_val = const_value(&mut m, Const::String(s_sym));
    push_inst(
        &mut m,
        b,
        Op::StorePropDyn {
            object: pair,
            key: c0,
            value: slot_val,
        },
    );
    let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
    push_inst(&mut m, b, Op::Return { value: Some(g) });
    let rf = recover_func(&m, f);
    let tpl = rf.blocks[0]
        .stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Declare {
                value: Expr::TemplateObject { raw, cooked },
                ..
            } => Some((raw.clone(), cooked.clone())),
            _ => None,
        })
        .expect("a TemplateObject declare");
    assert_eq!(tpl, (None, None));
}

// ── Template element array with a foreign user (2149) ────────────

#[test]
fn template_elem_array_foreign_user() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "f");
    let b = entry_of(&m, f);
    let c0 = load_number(&mut m, b, 0.0);
    let pair = emit_val(&mut m, b, Op::AllocArray { shape: None });
    let elems = emit_val(&mut m, b, Op::AllocArray { shape: None });
    push_inst(
        &mut m,
        b,
        Op::StoreOwnPropIdx {
            object: pair,
            index: c0,
            value: elems,
            kind: abcd_ir::OwnStoreKind::OwnProp,
        },
    );
    let g = emit_val(&mut m, b, Op::GetTemplateObject { literal: pair });
    push_inst(&mut m, b, Op::Return { value: Some(g) });
    // A use of the element array that is not a store/Mov: the walk
    // bails (2149) and the template stays unresolved.
    push_inst(&mut m, b, Op::Throw { value: elems });
    let rf = recover_func(&m, f);
    let tpl = rf.blocks[0]
        .stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Declare {
                value: Expr::TemplateObject { raw, cooked },
                ..
            } => Some((raw.clone(), cooked.clone())),
            _ => None,
        })
        .expect("a TemplateObject declare");
    assert_eq!(tpl, (None, None));
}

#[test]
fn parallel_phi_swap_cycle_and_bridge() {
    let mut m = mk_module();
    let f = add_fn(&mut m, "swapLoop");
    let b_entry = entry_of(&m, f);
    let _this = add_param(&mut m, f);
    let p_x = add_param(&mut m, f);
    let p_y = add_param(&mut m, f);
    let p_z = add_param(&mut m, f);

    let b_hdr = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_hdr);

    let b_latch = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(b_latch);

    push_inst(&mut m, b_entry, Op::Branch { dest: b_hdr });
    m.block_mut(b_hdr).unwrap().preds.push(Edge {
        from: b_entry,
        kind: EdgeKind::Normal,
    });
    m.block_mut(b_hdr).unwrap().preds.push(Edge {
        from: b_latch,
        kind: EdgeKind::Normal,
    });

    // Bridge `m = z` read by cycle `[a, b] = [m + b, a]` on the latch edge:
    // only ONE cycle-breaking temp (`phi`) should be minted (not on `m`).
    let v_m = emit_val(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let v_a = emit_val(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    let v_b = emit_val(
        &mut m,
        b_hdr,
        Op::Phi {
            entries: Vec::new(),
        },
    );
    push_inst(&mut m, b_hdr, Op::Branch { dest: b_latch });
    m.block_mut(b_latch).unwrap().preds.push(Edge {
        from: b_hdr,
        kind: EdgeKind::Normal,
    });

    let mb = emit_val(
        &mut m,
        b_latch,
        Op::BinaryOp {
            op: abcd_ir::op::BinOp::Add,
            left: v_b,
            right: v_m,
        },
    );
    push_inst(&mut m, b_latch, Op::Branch { dest: b_hdr });

    let e0 = Edge {
        from: b_entry,
        kind: EdgeKind::Normal,
    };
    let e1 = Edge {
        from: b_latch,
        kind: EdgeKind::Normal,
    };
    for (pv, entries) in [
        (v_m, vec![(e0, p_x), (e1, p_z)]),
        (v_a, vec![(e0, p_x), (e1, mb)]),
        (v_b, vec![(e0, p_y), (e1, v_a)]),
    ] {
        let ValueDef::Inst(iid) = m.value(pv).unwrap().def else {
            panic!("phi inst");
        };
        m.inst_mut(iid).unwrap().op = Op::Phi { entries };
    }

    let rf = recover_func(&m, f);
    let synth_decls: Vec<&str> = rf.blocks[0]
        .stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::PhiDecl { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert_eq!(synth_decls, vec!["phi"]);
}
