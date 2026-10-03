//! Inline skip-reason coverage (c-COV W10): the eligibility arms no
//! corpus function produces — `CalleeForeignValue` (all four emit
//! sites), `CallBlockIsHandler`, `slot_roles`-driven `CallTypeUnknown`,
//! the annotation-element arms, the `resolve_callee` Mov/guard/bound
//! arms, the nested-definition walk arms, the phi remap and
//! multi-return continuation of a multi-block callee, the step-H
//! exception participation, and the empty-block clone skip. Plus the
//! full skip-label pin. Production `inline.rs` is not modified (N82).

mod common;

use abcd_ir::verify_module;
use abcd_ir::{
    AnnValue, BlockId, CallKind, ClassId, Const, Edge, EdgeKind, FuncId, FunctionKind, Module, Op,
    ValueId,
};
use abcd_opt::inline::{InlineReport, SkipReason, inline_module};

use common::V2Builder;

/// Create a STATIC function (params are all formals — no `this`).
fn create_static(module: &mut Module, name: &str) -> FuncId {
    let f = V2Builder::create_function(module, name, FunctionKind::Function);
    module.functions[f.index()].modifiers = abcd_ir::Modifiers::STATIC;
    f
}

/// Attach an `L_ESCallTypeAnnotation;` with `callType = bits` to `f`.
fn set_call_type(module: &mut Module, f: FuncId, bits: u32) {
    let descriptor = module.sym.intern("L_ESCallTypeAnnotation;");
    let class_id = match module
        .classes
        .iter()
        .position(|c| c.descriptor == descriptor)
    {
        Some(i) => ClassId::new(i as u32),
        None => {
            module.classes.push(abcd_ir::ClassData {
                descriptor,
                name: descriptor,
                modifiers: abcd_ir::Modifiers::NONE,
                source_lang: abcd_ir::SourceLang::EcmaScript,
                super_class: None,
                interfaces: Vec::new(),
                fields: Vec::new(),
                methods: Vec::new(),
                annotations: Vec::new(),
                source_file: None,
            });
            ClassId::new((module.classes.len() - 1) as u32)
        }
    };
    let name = module.sym.intern("callType");
    let value = module.consts.push(Const::number(bits as f64));
    module.functions[f.index()]
        .annotations
        .push(abc_ir_annotation(class_id, name, value));
}

/// Shorthand for the annotation record.
fn abc_ir_annotation(
    class_id: ClassId,
    name: abcd_ir::Sym,
    value: abcd_ir::ConstId,
) -> abcd_ir::Annotation {
    abcd_ir::Annotation {
        class: class_id,
        elements: vec![(name, AnnValue::Const(value))],
    }
}

/// `g(p) { return p; }` — a minimal inlinable static callee (callType
/// 0: formals from slot 0).
fn build_identity_callee(module: &mut Module, name: &str) -> FuncId {
    let g = create_static(module, name);
    set_call_type(module, g, 0);
    let mut b = V2Builder::new(module, g);
    let p = b.create_param();
    b.emit_void(Op::Return { value: Some(p) });
    g
}

/// In `f`'s entry block: define a closure of `g` and call it.
fn emit_identity_call(b: &mut V2Builder, g: FuncId) -> ValueId {
    let df = b.emit_val(Op::DefineFunc {
        body: g,
        captures: vec![],
        length: 1,
    });
    let cl = b.emit_val(Op::AllocClosure { func: df });
    let arg = b.emit_number(1.0);
    b.emit_val(Op::Call {
        callee: cl,
        this: None,
        args: vec![arg],
        kind: CallKind::Dynamic,
    })
}

/// The caller: `f() { let r = g(1); return r; }`.
fn build_caller(module: &mut Module, g: FuncId) -> (FuncId, BlockId) {
    let f = create_static(module, "f");
    let mut b = V2Builder::new(module, f);
    let r = emit_identity_call(&mut b, g);
    b.emit_void(Op::Return { value: Some(r) });
    let entry = b.entry();
    (f, entry)
}

/// The complete skip-reason vocabulary is stable (the corpus histogram
/// keys — one line per variant).
#[test]
fn skip_reason_labels_all_stable() {
    let labels: Vec<(&'static str, SkipReason)> = vec![
        ("unsupported-call-kind", SkipReason::UnsupportedCallKind),
        ("unresolved-callee", SkipReason::UnresolvedCallee),
        ("self-recursive", SkipReason::SelfRecursive),
        ("callee-no-body", SkipReason::CalleeNoBody),
        ("callee-kind", SkipReason::CalleeKind),
        ("callee-too-large", SkipReason::CalleeTooLarge),
        ("caller-budget-exhausted", SkipReason::CallerBudgetExhausted),
        ("callee-has-try-regions", SkipReason::CalleeHasTryRegions),
        ("callee-entry-has-preds", SkipReason::CalleeEntryHasPreds),
        ("callee-foreign-value", SkipReason::CalleeForeignValue),
        ("callee-uses-lexenv", SkipReason::CalleeUsesLexEnv),
        (
            "callee-uses-private-names",
            SkipReason::CalleeUsesPrivateNames,
        ),
        ("callee-uses-arguments", SkipReason::CalleeUsesArguments),
        ("callee-uses-super", SkipReason::CalleeUsesSuper),
        ("callee-suspends", SkipReason::CalleeSuspends),
        ("callee-defines-closure", SkipReason::CalleeDefinesClosure),
        ("direct-without-this", SkipReason::DirectWithoutThis),
        ("call-type-unknown", SkipReason::CallTypeUnknown),
        ("call-block-is-handler", SkipReason::CallBlockIsHandler),
        ("block-terminal-call", SkipReason::BlockTerminalCall),
    ];
    assert_eq!(labels.len(), 20, "the whole vocabulary is pinned");
    let mut seen = std::collections::BTreeSet::new();
    for (want, reason) in labels {
        assert_eq!(reason.label(), want, "{reason:?}");
        assert!(seen.insert(want), "labels are unique: {want}");
    }
}

/// `InlineReport::merge` folds skips and counters (the corpus
/// aggregation path).
#[test]
fn inline_report_merge_folds() {
    let mut a = InlineReport::default();
    a.sites_inlined += 1;
    a.insts_inlined += 3;
    *a.skips.entry(SkipReason::CalleeTooLarge).or_insert(0) += 2;
    let mut b = InlineReport::default();
    b.sites_inlined += 2;
    b.insts_inlined += 5;
    *b.skips.entry(SkipReason::CalleeTooLarge).or_insert(0) += 1;
    *b.skips.entry(SkipReason::UnresolvedCallee).or_insert(0) += 7;
    a.merge(&b);
    assert_eq!(a.sites_inlined, 3);
    assert_eq!(a.insts_inlined, 8);
    assert_eq!(a.skips[&SkipReason::CalleeTooLarge], 3);
    assert_eq!(a.skips[&SkipReason::UnresolvedCallee], 7);
}

/// `CalleeForeignValue`, all four emit sites: a dangling operand, a
/// `Branch`/`CondBranch` target outside the callee, a phi entry from a
/// foreign block.
#[test]
fn callee_foreign_value_all_emit_sites() {
    let mut module = Module::new();
    // (1) A dangling operand value.
    let g1 = create_static(&mut module, "g1");
    set_call_type(&mut module, g1, 0);
    {
        let mut b = V2Builder::new(&mut module, g1);
        let p = b.create_param();
        let bad = b.emit_val(Op::Mov {
            src: ValueId::new(99999),
        });
        let _ = p;
        b.emit_void(Op::Return { value: Some(bad) });
    }
    // (2) A Branch to a block the callee does not own.
    let g2 = create_static(&mut module, "g2");
    set_call_type(&mut module, g2, 0);
    // (3) A CondBranch with a foreign dest.
    let g3 = create_static(&mut module, "g3");
    set_call_type(&mut module, g3, 0);
    // (4) A phi entry from a foreign block.
    let g4 = create_static(&mut module, "g4");
    set_call_type(&mut module, g4, 0);
    // The caller comes first in id order only for readability; the
    // foreign references below name ITS entry block (created next).
    let f = create_static(&mut module, "f");
    let foreign = module.functions[f.index()].blocks[0];
    {
        let mut b = V2Builder::new(&mut module, g2);
        let _p = b.create_param();
        b.emit_void(Op::Branch { dest: foreign });
    }
    {
        let mut b = V2Builder::new(&mut module, g3);
        let p = b.create_param();
        b.emit_void(Op::CondBranch {
            cond: p,
            true_dest: foreign,
            false_dest: foreign,
        });
    }
    {
        let mut b = V2Builder::new(&mut module, g4);
        let p = b.create_param();
        b.emit_void(Op::Phi {
            entries: vec![(
                Edge {
                    from: foreign,
                    kind: EdgeKind::Normal,
                },
                p,
            )],
        });
        b.emit_void(Op::Return { value: Some(p) });
    }
    {
        let mut b = V2Builder::new(&mut module, f);
        for g in [g1, g2, g3, g4] {
            emit_identity_call(&mut b, g);
        }
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 0);
    assert_eq!(
        report.skips.get(&SkipReason::CalleeForeignValue),
        Some(&4),
        "all four emit sites: {:?}",
        report.skips
    );
}

/// `CallBlockIsHandler`: a region protecting the call block that also
/// uses it as a catch handler.
#[test]
fn call_block_is_handler_skips() {
    let mut module = Module::new();
    let g = build_identity_callee(&mut module, "g");
    let (f, entry) = build_caller(&mut module, g);
    // The call sits in `entry`; `entry` is both protected and a handler.
    let mut b = V2Builder::new(&mut module, f);
    let exc = b.create_exception_param(entry);
    b.add_try(vec![entry], entry);
    let _ = exc;

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 0);
    assert_eq!(
        report.skips.get(&SkipReason::CallBlockIsHandler),
        Some(&1),
        "{:?}",
        report.skips
    );
}

/// `CallTypeUnknown` via `slot_roles`: a STATIC callee (the vendored
/// default 0xF applies) with FEWER params than the three implicit slots.
#[test]
fn call_type_unknown_via_slot_roles() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g"); // no annotation: the 0xF default
    {
        let mut b = V2Builder::new(&mut module, g);
        let p0 = b.create_param();
        let _p1 = b.create_param(); // 2 params < 3 implicit slots
        b.emit_void(Op::Return { value: Some(p0) });
    }
    build_caller(&mut module, g);

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 0);
    assert_eq!(
        report.skips.get(&SkipReason::CallTypeUnknown),
        Some(&1),
        "{:?}",
        report.skips
    );
}

/// The annotation-element arms: an `L_ESCallTypeAnnotation;` whose
/// elements name something else, and a `callType` element whose value
/// is not a pooled const — both read as "no usable annotation", so the
/// STATIC callees (4 params = the 0xF default's 3 implicit slots + 1
/// formal) take the vendored default and inline.
#[test]
fn annotation_element_arms_fall_through_to_default() {
    let mut module = Module::new();
    // (a) callType annotation whose only element is named "other".
    let descriptor = module.sym.intern("L_ESCallTypeAnnotation;");
    module.classes.push(abcd_ir::ClassData {
        descriptor,
        name: descriptor,
        modifiers: abcd_ir::Modifiers::NONE,
        source_lang: abcd_ir::SourceLang::EcmaScript,
        super_class: None,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        annotations: Vec::new(),
        source_file: None,
    });
    let ann_class = ClassId::new((module.classes.len() - 1) as u32);
    let other = module.sym.intern("other");
    let call_type = module.sym.intern("callType");
    let zero_cid = module.consts.push(Const::number(0.0));
    let build_callee = |module: &mut Module, name: &str, elems: Vec<(abcd_ir::Sym, AnnValue)>| {
        let g = create_static(module, name);
        {
            let mut b = V2Builder::new(module, g);
            for _ in 0..4 {
                b.create_param();
            }
            let p3 = b.module.functions[g.index()].params[3];
            b.emit_void(Op::Return { value: Some(p3) });
        }
        module.functions[g.index()]
            .annotations
            .push(abcd_ir::Annotation {
                class: ann_class,
                elements: elems,
            });
        g
    };
    // (a) the element name is not `callType`: skipped, no annotation.
    let g1 = build_callee(&mut module, "g1", vec![(other, AnnValue::Const(zero_cid))]);
    // (b) a `callType` element with a non-Const value: skipped too.
    let g2 = build_callee(&mut module, "g2", vec![(call_type, AnnValue::Name(other))]);
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let arg = b.emit_number(1.0);
        for g in [g1, g2] {
            let df = b.emit_val(Op::DefineFunc {
                body: g,
                captures: vec![],
                length: 1,
            });
            let cl = b.emit_val(Op::AllocClosure { func: df });
            b.emit_val(Op::Call {
                callee: cl,
                this: None,
                args: vec![arg],
                kind: CallKind::Dynamic,
            });
        }
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(
        report.sites_inlined, 2,
        "unusable annotations fall through to the vendored default: {:?}",
        report.skips
    );
}

/// `resolve_callee`'s Mov pass-through (the callee chain inlines), the
/// two `AllocClosure` shape guards, the non-closure leaf, and the
/// 16-iteration chain bound.
#[test]
fn resolve_callee_mov_chain_and_guards() {
    let mut module = Module::new();
    let g = build_identity_callee(&mut module, "g");
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let p = b.create_param();
        // (a) A Mov-chained closure: resolves, inlines.
        let df = b.emit_val(Op::DefineFunc {
            body: g,
            captures: vec![],
            length: 1,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let mv = b.emit_val(Op::Mov { src: cl });
        let arg = b.emit_number(1.0);
        b.emit_val(Op::Call {
            callee: mv,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        });
        // (b) AllocClosure over a parameter (not Inst-defined).
        let clo_param = b.emit_val(Op::AllocClosure { func: p });
        let arg = b.emit_number(2.0);
        b.emit_val(Op::Call {
            callee: clo_param,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        });
        // (c) AllocClosure over a non-DefineFunc inst result.
        let num = b.emit_number(3.0);
        let clo_num = b.emit_val(Op::AllocClosure { func: num });
        b.emit_val(Op::Call {
            callee: clo_num,
            this: None,
            args: vec![num],
            kind: CallKind::Dynamic,
        });
        // (d) A 17-long Mov chain: the 16-iteration bound cuts it.
        let df = b.emit_val(Op::DefineFunc {
            body: g,
            captures: vec![],
            length: 1,
        });
        let mut cur = b.emit_val(Op::AllocClosure { func: df });
        for _ in 0..17 {
            cur = b.emit_val(Op::Mov { src: cur });
        }
        let arg = b.emit_number(4.0);
        b.emit_val(Op::Call {
            callee: cur,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "only the Mov-chained site");
    assert_eq!(
        report.skips.get(&SkipReason::UnresolvedCallee),
        Some(&3),
        "{:?}",
        report.skips
    );
}

/// The nested-definition walk: `DefineClass`/`DefineSendableClass`
/// roots whose transitive bodies stay env-clean inline fine (including
/// a DefineFunc cycle cut and a dangling nested body); a constructor
/// reading the lexical env refuses.
#[test]
fn nested_class_roots_walk() {
    let mut module = Module::new();
    // The clean ctor: contains a nested DefineFunc cycle (a <-> deep)
    // and a dangling DefineFunc body.
    let ctor_ok = create_static(&mut module, "ctor_ok");
    let deep = create_static(&mut module, "deep");
    set_call_type(&mut module, ctor_ok, 0);
    set_call_type(&mut module, deep, 0);
    // A dangling block in the ctor's block list and a dangling inst in
    // the deep body's entry: the nested walk skips both.
    module.functions[ctor_ok.index()]
        .blocks
        .push(BlockId::new(9998));
    let deep_entry = module.functions[deep.index()].blocks[0];
    module.blocks[deep_entry.index()]
        .insts
        .push(abcd_ir::InstId::new(9999));
    {
        let mut b = V2Builder::new(&mut module, ctor_ok);
        let _p = b.create_param();
        b.emit_val(Op::DefineFunc {
            body: deep,
            captures: vec![],
            length: 0,
        });
        b.emit_val(Op::DefineFunc {
            body: FuncId::new(999), // dangling: skipped by the walk
            captures: vec![],
            length: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    {
        let mut b = V2Builder::new(&mut module, deep);
        b.emit_val(Op::DefineFunc {
            body: ctor_ok, // the cycle back edge: the visited cut
            captures: vec![],
            length: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    let ctor_send = create_static(&mut module, "ctor_send");
    set_call_type(&mut module, ctor_send, 0);
    {
        let mut b = V2Builder::new(&mut module, ctor_send);
        b.emit_void(Op::Return { value: None });
    }
    // The env-reading ctor.
    let ctor_bad = create_static(&mut module, "ctor_bad");
    set_call_type(&mut module, ctor_bad, 0);
    {
        let mut b = V2Builder::new(&mut module, ctor_bad);
        b.emit_val(Op::GetLexVar { level: 0, slot: 0 });
        b.emit_void(Op::Return { value: None });
    }
    // g_ok's body defines both class forms; g_bad's ctor reads the env.
    let g_ok = create_static(&mut module, "g_ok");
    set_call_type(&mut module, g_ok, 0);
    {
        let mut b = V2Builder::new(&mut module, g_ok);
        let _p = b.create_param();
        let members = b.konst(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        b.emit_val(Op::DefineClass {
            ctor: ctor_ok,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 0,
        });
        b.emit_val(Op::DefineSendableClass {
            ctor: ctor_send,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 0,
        });
        b.emit_void(Op::Return { value: Some(_p) });
    }
    let g_bad = create_static(&mut module, "g_bad");
    set_call_type(&mut module, g_bad, 0);
    {
        let mut b = V2Builder::new(&mut module, g_bad);
        let _p = b.create_param();
        let members = b.konst(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        b.emit_val(Op::DefineClass {
            ctor: ctor_bad,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 0,
        });
        b.emit_void(Op::Return { value: Some(_p) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        emit_identity_call(&mut b, g_ok);
        emit_identity_call(&mut b, g_bad);
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "the env-clean class def inlines");
    assert_eq!(
        report.skips.get(&SkipReason::CalleeDefinesClosure),
        Some(&1),
        "{:?}",
        report.skips
    );
}

/// A multi-block callee: the clone remaps phi edges (entry → a | b →
/// join with a phi), and a two-`Return` callee grows a continuation
/// phi. Both inline; the module still verifies.
#[test]
fn multi_block_callee_phi_and_multi_return() {
    let mut module = Module::new();
    // g_phi(x): entry ->{a|b}; a: y = x; b: z = x; join: phi(y, z);
    // return phi.
    let g_phi = create_static(&mut module, "g_phi");
    set_call_type(&mut module, g_phi, 0);
    {
        let mut b = V2Builder::new(&mut module, g_phi);
        let x = b.create_param();
        let entry = b.entry();
        let a = b.create_block();
        let bb = b.create_block();
        let join = b.create_block();
        b.set_insert_block(entry);
        b.emit_void(Op::CondBranch {
            cond: x,
            true_dest: a,
            false_dest: bb,
        });
        b.set_insert_block(a);
        b.emit_void(Op::Branch { dest: join });
        b.set_insert_block(bb);
        b.emit_void(Op::Branch { dest: join });
        b.add_predecessor(a, entry);
        b.add_predecessor(bb, entry);
        b.add_predecessor(join, a);
        b.add_predecessor(join, bb);
        b.set_insert_block(join);
        let phi = b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: a,
                        kind: EdgeKind::Normal,
                    },
                    x,
                ),
                (
                    Edge {
                        from: bb,
                        kind: EdgeKind::Normal,
                    },
                    x,
                ),
            ],
        });
        b.emit_void(Op::Return { value: Some(phi) });
    }
    // g_two(x): entry ->{a|b}; a: return x; b: return x (two Returns).
    let g_two = create_static(&mut module, "g_two");
    set_call_type(&mut module, g_two, 0);
    {
        let mut b = V2Builder::new(&mut module, g_two);
        let x = b.create_param();
        let entry = b.entry();
        let a = b.create_block();
        let bb = b.create_block();
        b.set_insert_block(entry);
        b.emit_void(Op::CondBranch {
            cond: x,
            true_dest: a,
            false_dest: bb,
        });
        b.set_insert_block(a);
        b.emit_void(Op::Return { value: Some(x) });
        b.set_insert_block(bb);
        b.emit_void(Op::Return { value: Some(x) });
        b.add_predecessor(a, entry);
        b.add_predecessor(bb, entry);
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let r1 = emit_identity_call(&mut b, g_phi);
        let r2 = emit_identity_call(&mut b, g_two);
        let s = b.emit_val(Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: r1,
            right: r2,
        });
        b.emit_void(Op::Return { value: Some(s) });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 2, "{:?}", report.skips);
    let errors = verify_module(&module);
    assert!(errors.is_ok(), "{:?}", errors.errors);
    // The two-return callee produced a fresh phi in the caller, and
    // the cloned callee brought its own join phi.
    let phi_count = module.functions[f.index()]
        .blocks
        .iter()
        .flat_map(|&bb| module.blocks[bb.index()].insts.iter())
        .filter(|&&i| matches!(module.insts[i.index()].op, Op::Phi { .. }))
        .count();
    assert_eq!(
        phi_count, 2,
        "the cloned join phi + the continuation phi of the two-return inline"
    );
}

/// Step H: an inline site inside a protected region joins every cloned
/// block and the continuation to the region; handler phis keyed by the
/// call block's exceptional edge gain one entry per new protected
/// block. (No verify_module here: the second, deliberately
/// under-keyed handler phi is verifier-inconsistent by construction.)
#[test]
fn inline_inside_try_region_extends_region_and_handler_phis() {
    let mut module = Module::new();
    let g = build_identity_callee(&mut module, "g");
    let f = create_static(&mut module, "f");
    let handler;
    let callee_blocks = module.functions[g.index()].blocks.len();
    {
        let mut b = V2Builder::new(&mut module, f);
        let call_block = b.entry();
        let _r = emit_identity_call(&mut b, g);
        b.emit_void(Op::Return { value: None });
        handler = b.create_block();
        let exc = b.add_try(vec![call_block], handler);
        b.set_insert_block(handler);
        b.emit_void(Op::Return { value: Some(exc) });
        // A handler phi keyed by the call block's exceptional edge…
        b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: call_block,
                    kind: EdgeKind::Exceptional,
                },
                exc,
            )],
        });
        // …and one NOT keyed by it (the find-None skip).
        let some_other = b.create_block();
        b.set_insert_block(some_other);
        b.emit_void(Op::Return { value: None });
        b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: some_other,
                    kind: EdgeKind::Exceptional,
                },
                exc,
            )],
        });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "{:?}", report.skips);
    let region = &module.functions[f.index()].try_regions[0];
    assert_eq!(
        region.protected.len(),
        1 + callee_blocks + 1,
        "every cloned block + the continuation joined the region"
    );
    // The keyed phi gained one entry per new protected block; the
    // unkeyed one is untouched.
    let phi_entry_counts: Vec<usize> = module.functions[f.index()]
        .blocks
        .iter()
        .flat_map(|&bb| module.blocks[bb.index()].insts.iter())
        .filter_map(|&i| match &module.insts[i.index()].op {
            Op::Phi { entries } => Some(entries.len()),
            _ => None,
        })
        .collect();
    assert!(
        phi_entry_counts.iter().any(|&n| n == 1 + callee_blocks + 1),
        "the keyed phi grew: {phi_entry_counts:?}"
    );
    assert!(
        phi_entry_counts.contains(&1),
        "the unkeyed phi was skipped: {phi_entry_counts:?}"
    );
}

/// `LoadNewTarget` in the callee binds undefined (Direct/Dynamic);
/// `LoadFunction` binds the call-site closure value (a Mov of it).
#[test]
fn newtarget_and_loadfunction_are_bound() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    set_call_type(&mut module, g, 0);
    {
        let mut b = V2Builder::new(&mut module, g);
        let _p = b.create_param();
        let nt = b.emit_val(Op::LoadNewTarget);
        let lf = b.emit_val(Op::LoadFunction);
        let s = b.emit_val(Op::BinaryOp {
            op: abcd_ir::BinOp::Add,
            left: nt,
            right: lf,
        });
        b.emit_void(Op::Return { value: Some(s) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let r = emit_identity_call(&mut b, g);
        b.emit_void(Op::Return { value: Some(r) });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "{:?}", report.skips);
    // The clone contains no LoadNewTarget/LoadFunction: they were bound.
    let mut saw_loadconst_undef = false;
    let mut saw_mov = false;
    for &bb in &module.functions[f.index()].blocks {
        for &i in &module.blocks[bb.index()].insts {
            match &module.insts[i.index()].op {
                Op::LoadNewTarget | Op::LoadFunction => {
                    panic!("frame ops must be bound at the splice: {i:?}")
                }
                Op::LoadConst(c) => {
                    if matches!(module.consts.get(*c), Some(Const::Undefined)) {
                        saw_loadconst_undef = true;
                    }
                }
                Op::Mov { .. } => saw_mov = true,
                _ => {}
            }
        }
    }
    assert!(
        saw_loadconst_undef,
        "new.target became the pooled undefined"
    );
    assert!(saw_mov, "LoadFunction became a Mov of the closure value");
    let errors = verify_module(&module);
    assert!(errors.is_ok(), "{:?}", errors.errors);
}

/// A callee with an EMPTY middle block: the clone's last-inst lookup
/// skips it (no return point), the splice still completes.
#[test]
fn empty_block_in_callee_is_skipped_by_return_scan() {
    let mut module = Module::new();
    let g = create_static(&mut module, "g");
    set_call_type(&mut module, g, 0);
    {
        let mut b = V2Builder::new(&mut module, g);
        let _p = b.create_param();
        let entry = b.entry();
        let mid = b.create_block(); // zero instructions
        let out = b.create_block();
        b.set_insert_block(entry);
        b.emit_void(Op::Branch { dest: mid });
        b.set_insert_block(out);
        b.emit_void(Op::Return { value: Some(_p) });
        b.add_predecessor(mid, entry);
        b.add_predecessor(out, mid);
    }
    let f = create_static(&mut module, "f");
    let f_blocks_before = module.functions[f.index()].blocks.len();
    {
        let mut b = V2Builder::new(&mut module, f);
        let _r = emit_identity_call(&mut b, g);
        b.emit_void(Op::Return { value: Some(_r) });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "{:?}", report.skips);
    assert_eq!(
        module.functions[f.index()].blocks.len(),
        f_blocks_before + 3 + 1,
        "three cloned blocks + the continuation"
    );
}

/// The call block's old successors re-key onto the continuation,
/// including phi entries (the N82 predecessor rebuild).
#[test]
fn successor_phi_entries_rekey_to_continuation() {
    let mut module = Module::new();
    let g = build_identity_callee(&mut module, "g");
    let f = create_static(&mut module, "f");
    let entry;
    let phi_iid;
    let moved_terminator;
    {
        let mut b = V2Builder::new(&mut module, f);
        entry = b.entry();
        let r = emit_identity_call(&mut b, g);
        let s2 = b.create_block();
        let j = b.create_block();
        // The call block branches DIRECTLY to the join and to s2 (so
        // the join's phi can legitimately key an entry by the call
        // block pre-inline).
        let c = b.emit_number(0.0);
        let (tid, _) = b.emit(Op::CondBranch {
            cond: c,
            true_dest: j,
            false_dest: s2,
        });
        moved_terminator = tid;
        b.set_insert_block(s2);
        b.emit_void(Op::Branch { dest: j });
        b.add_predecessor(s2, entry);
        b.add_predecessor(j, entry);
        b.add_predecessor(j, s2);
        b.set_insert_block(j);
        let (iid, phi) = b.emit(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Normal,
                    },
                    r,
                ),
                (
                    Edge {
                        from: s2,
                        kind: EdgeKind::Normal,
                    },
                    r,
                ),
            ],
        });
        phi_iid = iid;
        let _ = phi;
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "{:?}", report.skips);
    // The continuation owns the moved terminator now.
    let cont = module.insts[moved_terminator.index()].block;
    assert_ne!(cont, entry, "the terminator moved to the continuation");
    // The phi entry that named the call block was re-keyed to it.
    let Op::Phi { entries } = &module.insts[phi_iid.index()].op else {
        panic!("the phi survived")
    };
    assert!(
        entries.iter().all(|(e, _)| e.from != entry),
        "no entry names the truncated call block: {entries:?}"
    );
    assert!(
        entries.iter().any(|(e, _)| e.from == cont),
        "an entry names the continuation: {entries:?}"
    );
    let errors = verify_module(&module);
    assert!(errors.is_ok(), "{:?}", errors.errors);
}

/// Dangling ids in the caller's block/inst lists are skipped by the
/// site scan; the genuine call still inlines.
#[test]
fn dangling_ids_in_caller_are_skipped() {
    let mut module = Module::new();
    let g = build_identity_callee(&mut module, "g");
    let (f, entry) = build_caller(&mut module, g);
    module.functions[f.index()].blocks.push(BlockId::new(9999));
    module.blocks[entry.index()]
        .insts
        .push(abcd_ir::InstId::new(9999));

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(report.sites_inlined, 1, "{:?}", report.skips);
}

/// `resolve_callee`'s leaf arm: a callee value defined by a
/// non-Mov/non-closure op (a number load) is deliberately unresolved.
#[test]
fn resolve_callee_non_closure_leaf_is_unresolved() {
    let mut module = Module::new();
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        let num = b.emit_number(1.0);
        b.emit_val(Op::Call {
            callee: num,
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    let report = inline_module(&mut module, &Default::default());
    assert_eq!(
        report.skips.get(&SkipReason::UnresolvedCallee),
        Some(&1),
        "{:?}",
        report.skips
    );
}

/// A callee carrying an UNRELATED annotation (not
/// `L_ESCallTypeAnnotation;`) reads as "no annotation" — the static
/// default applies and the site inlines.
#[test]
fn unrelated_annotation_class_falls_through() {
    let mut module = Module::new();
    // A 0xF-default static callee (3 implicit slots + 1 formal).
    let g = create_static(&mut module, "g");
    {
        let mut b = V2Builder::new(&mut module, g);
        for _ in 0..4 {
            b.create_param();
        }
        let p3 = b.module.functions[g.index()].params[3];
        b.emit_void(Op::Return { value: Some(p3) });
    }
    let descriptor = module.sym.intern("LOther;");
    module.classes.push(abcd_ir::ClassData {
        descriptor,
        name: descriptor,
        modifiers: abcd_ir::Modifiers::NONE,
        source_lang: abcd_ir::SourceLang::EcmaScript,
        super_class: None,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        annotations: Vec::new(),
        source_file: None,
    });
    let ann_class = ClassId::new((module.classes.len() - 1) as u32);
    let elem = module.sym.intern("callType");
    let cid = module.consts.push(Const::number(0.0));
    module.functions[g.index()]
        .annotations
        .push(abc_ir_annotation(ann_class, elem, cid));
    build_caller(&mut module, g);

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(
        report.sites_inlined, 1,
        "an unrelated annotation is no annotation: {:?}",
        report.skips
    );
}

/// The callee body scan's integrity guards: a dangling block in the
/// callee's block list and a dangling inst in a block each read as
/// `CalleeNoBody` (two callees — the inst guard returns before the
/// block guard otherwise).
#[test]
fn callee_dangling_ids_read_as_no_body() {
    let mut module = Module::new();
    // (a) A dangling INST in the callee's entry block.
    let g1 = build_identity_callee(&mut module, "g1");
    let g1_entry = module.functions[g1.index()].blocks[0];
    module.blocks[g1_entry.index()]
        .insts
        .push(abcd_ir::InstId::new(9999));
    // (b) A dangling BLOCK in the callee's block list.
    let g2 = build_identity_callee(&mut module, "g2");
    module.functions[g2.index()].blocks.push(BlockId::new(9999));
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        emit_identity_call(&mut b, g1);
        emit_identity_call(&mut b, g2);
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(
        report.skips.get(&SkipReason::CalleeNoBody),
        Some(&2),
        "{:?}",
        report.skips
    );
    assert_eq!(report.sites_inlined, 0);
}

/// The nested walk's DefineClass arm: a nested ctor whose body defines
/// ANOTHER class (env-clean) — the transitive walk descends, finds
/// nothing, and the callee inlines.
#[test]
fn nested_walk_descends_into_class_ctors() {
    let mut module = Module::new();
    let deep_ctor = create_static(&mut module, "deep_ctor");
    set_call_type(&mut module, deep_ctor, 0);
    {
        let mut b = V2Builder::new(&mut module, deep_ctor);
        b.emit_void(Op::Return { value: None });
    }
    let ctor = create_static(&mut module, "ctor");
    set_call_type(&mut module, ctor, 0);
    {
        let mut b = V2Builder::new(&mut module, ctor);
        let members = b.konst(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        // The ctor's body defines a class: the walk descends into
        // deep_ctor (env-clean) through the class edge.
        b.emit_val(Op::DefineClass {
            ctor: deep_ctor,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 0,
        });
        b.emit_void(Op::Return { value: None });
    }
    let g = create_static(&mut module, "g");
    set_call_type(&mut module, g, 0);
    {
        let mut b = V2Builder::new(&mut module, g);
        let _p = b.create_param();
        let members = b.konst(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        b.emit_val(Op::DefineClass {
            ctor,
            heritage: None,
            members,
            member_attrs: vec![],
            count: 0,
        });
        b.emit_void(Op::Return { value: Some(_p) });
    }
    let f = create_static(&mut module, "f");
    {
        let mut b = V2Builder::new(&mut module, f);
        emit_identity_call(&mut b, g);
        b.emit_void(Op::Return { value: None });
    }

    let report = inline_module(&mut module, &Default::default());
    assert_eq!(
        report.sites_inlined, 1,
        "the env-clean transitive class tree inlines: {:?}",
        report.skips
    );
}
