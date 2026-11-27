//! Unit tests for [`crate::op`] single-point visitors, arity contracts, and
//! opcode predicates.

use super::*;

// ── Single-point operand & entity visitors ───────────────────────────────

/// The two single-point operand accessors must agree (drift guard
/// behind the verifier's arity check).
#[test]
fn operands_and_operands_mut_agree() {
    let v = || ValueId::new(1);
    let s = Sym::new(0);
    let mut ops = vec![
        Op::BinaryOp {
            op: BinOp::Add,
            left: v(),
            right: v(),
        },
        Op::UnaryOp {
            op: UnOp::Minus,
            operand: v(),
        },
        Op::Mov { src: v() },
        Op::LoadConst(ConstId::new(0)),
        Op::AllocObject {
            shape: ConstId::new(0),
        },
        Op::LoadProp {
            object: v(),
            name: s,
        },
        Op::StorePropIdx {
            object: v(),
            index: v(),
            value: v(),
        },
        Op::DeleteProp {
            object: v(),
            key: v(),
        },
        Op::LoadPropIdx {
            object: v(),
            index: v(),
        },
        Op::LoadPropDyn {
            object: v(),
            key: v(),
        },
        Op::TestProp {
            object: v(),
            key: PropKey::Dynamic(v()),
        },
        Op::Call {
            callee: v(),
            this: Some(v()),
            args: vec![v(), v()],
            kind: CallKind::Direct,
        },
        Op::DefineFunc {
            body: FuncId::new(0),
            captures: vec![(s, v())],
            length: 2,
        },
        Op::Phi { entries: vec![] },
        Op::Branch {
            dest: BlockId::new(0),
        },
        Op::Return { value: Some(v()) },
        Op::Unreachable,
        // ── Full ISA coverage ops ──
        Op::NewLexEnv {
            num_vars: 3,
            kind: LexEnvKind::Plain,
        },
        Op::NewLexEnvWithName {
            num_vars: 3,
            scope_names: ConstId::new(0),
        },
        Op::PopLexEnv,
        Op::SetObjectWithProto {
            proto: v(),
            obj: v(),
        },
        Op::ArraySpread {
            dst: v(),
            index: v(),
            src: v(),
        },
        Op::CreateObjectWithExcludedKeys {
            obj: v(),
            keys: vec![v(), v()],
        },
        Op::DefineGetterSetterByValue {
            obj: v(),
            key: v(),
            getter: v(),
            setter: v(),
            set_name: v(),
        },
        Op::GetTemplateObject { literal: v() },
        Op::CreateIterResultObj {
            value: v(),
            done: v(),
        },
        Op::GetAsyncIterator { obj: v() },
        Op::CopyRestArgs { start_index: 1 },
        Op::GetUnmappedArgs,
        Op::LoadNewTarget,
        Op::LoadGlobalObject,
        Op::LoadFunction,
        Op::AsyncFunctionEnter,
        Op::AwaitUncaught {
            funcobj: v(),
            value: v(),
        },
        Op::ThrowUndefinedIfHoleWithName {
            name: s,
            value: v(),
        },
        Op::ThrowNotExists,
        Op::ThrowPatternNonCoercible,
        Op::ThrowDeleteSuperProperty,
        Op::Debugger,
        Op::DefineMethod {
            object: v(),
            name: s,
            func: v(),
            length: 1,
        },
        Op::DefineClass(Box::new(DefineClassData {
            ctor: FuncId::new(0),
            heritage: Some(v()),
            members: ConstId::new(0),
            member_attrs: Vec::new(),
            count: 2,
        })),
        Op::DefineSendableClass(Box::new(DefineClassData {
            ctor: FuncId::new(0),
            heritage: Some(v()),
            members: ConstId::new(0),
            member_attrs: Vec::new(),
            count: 2,
        })),
        Op::CreatePrivateNames {
            count: 2,
            names: ConstId::new(0),
        },
    ];
    for op in &mut ops {
        assert_eq!(op.operands().len(), op.operands_mut().len(), "{op:?}");
        if let Arity::Exact(n) = op.arity() {
            assert_eq!(op.operands().len(), n, "{op:?}");
        }
    }
}

/// All 94 variants' operand accessors (`operands`, `for_each_operand`,
/// `has_operand`, `operands_mut`), entity visitors, and fixed `arity()` agree
/// in exact order on distinct `ValueId`s.
#[test]
fn all_88_variants_operand_visitors_agree_in_order() {
    use crate::function::EdgeKind;

    let mut next_id = 1u32;
    let mut v = || {
        let id = ValueId::new(next_id);
        next_id += 1;
        id
    };
    let s = Sym::new(0);
    let c = ConstId::new(0);
    let f = FuncId::new(0);
    let b = BlockId::new(0);
    let edge = |idx| Edge {
        from: BlockId::new(idx),
        kind: EdgeKind::Normal,
    };

    let mut ops = vec![
        // Compute (5)
        Op::BinaryOp {
            op: BinOp::Add,
            left: v(),
            right: v(),
        },
        Op::UnaryOp {
            op: UnOp::Minus,
            operand: v(),
        },
        Op::Compare {
            op: CmpOp::Eq,
            left: v(),
            right: v(),
        },
        Op::Mov { src: v() },
        Op::LoadConst(c),
        // Objects / arrays (23)
        Op::AllocObject { shape: c },
        Op::AllocArray { shape: Some(c) },
        Op::AllocRegExp {
            pattern: s,
            flags: 0,
        },
        Op::AllocClosure { func: v() },
        Op::LoadProp {
            object: v(),
            name: s,
        },
        Op::StoreProp {
            object: v(),
            name: s,
            value: v(),
        },
        Op::LoadPropIdx {
            object: v(),
            index: v(),
        },
        Op::StorePropIdx {
            object: v(),
            index: v(),
            value: v(),
        },
        Op::LoadPropDyn {
            object: v(),
            key: v(),
        },
        Op::StorePropDyn {
            object: v(),
            key: v(),
            value: v(),
        },
        Op::StoreOwnPropName {
            object: v(),
            name: s,
            value: v(),
            kind: OwnStoreKind::OwnProp,
        },
        Op::StoreOwnPropDyn {
            object: v(),
            key: v(),
            value: v(),
            kind: OwnStoreKind::OwnProp,
        },
        Op::StoreOwnPropIdx {
            object: v(),
            index: v(),
            value: v(),
            kind: OwnStoreKind::OwnProp,
        },
        Op::DefineMethod {
            object: v(),
            name: s,
            func: v(),
            length: 1,
        },
        Op::DeleteProp {
            object: v(),
            key: v(),
        },
        Op::TestProp {
            object: v(),
            key: PropKey::Name(s),
        },
        Op::TestProp {
            object: v(),
            key: PropKey::Index(v()),
        },
        Op::TestProp {
            object: v(),
            key: PropKey::Dynamic(v()),
        },
        Op::CopyDataProps { dst: v(), src: v() },
        Op::SetObjectWithProto {
            proto: v(),
            obj: v(),
        },
        Op::ArraySpread {
            dst: v(),
            index: v(),
            src: v(),
        },
        Op::CreateObjectWithExcludedKeys {
            obj: v(),
            keys: vec![v(), v()],
        },
        Op::DefineGetterSetterByValue {
            obj: v(),
            key: v(),
            getter: v(),
            setter: v(),
            set_name: v(),
        },
        Op::GetTemplateObject { literal: v() },
        Op::CreateIterResultObj {
            value: v(),
            done: v(),
        },
        // Iteration (7)
        Op::GetIterator { obj: v() },
        Op::GetAsyncIterator { obj: v() },
        Op::IteratorNext { iterator: v() },
        Op::IteratorReturn { iterator: v() },
        Op::IteratorThrow { iterator: v() },
        Op::GetPropIterator { obj: v() },
        Op::NextPropName { iterator: v() },
        // Lexical / global / module (13)
        Op::NewLexEnv {
            num_vars: 2,
            kind: LexEnvKind::Plain,
        },
        Op::NewLexEnvWithName {
            num_vars: 2,
            scope_names: c,
        },
        Op::PopLexEnv,
        Op::GetLexVar {
            level: 0,
            slot: 1,
            kind: LexEnvKind::Plain,
        },
        Op::PutLexVar {
            level: 0,
            slot: 1,
            value: v(),
            kind: LexEnvKind::Plain,
        },
        Op::TryGetGlobal {
            name: s,
            default: None,
        },
        Op::TryGetGlobal {
            name: s,
            default: Some(v()),
        },
        Op::StoreGlobal {
            name: s,
            value: v(),
        },
        Op::StoreGlobalRecord {
            name: s,
            value: v(),
            is_const: true,
        },
        Op::TryStoreGlobal {
            name: s,
            value: v(),
        },
        Op::LoadModuleVar {
            index: 0,
            kind: ModuleVarKind::Local,
        },
        Op::StoreModuleVar {
            index: 0,
            value: v(),
        },
        Op::GetModuleNamespace { index: 0 },
        Op::DynamicImport { specifier: v() },
        // Calls / definitions (4)
        Op::Call {
            callee: v(),
            this: None,
            args: vec![],
            kind: CallKind::Dynamic,
        },
        Op::Call {
            callee: v(),
            this: Some(v()),
            args: vec![v(), v()],
            kind: CallKind::Direct,
        },
        Op::DefineFunc {
            body: f,
            captures: vec![(s, v()), (s, v())],
            length: 2,
        },
        Op::DefineClass(Box::new(DefineClassData {
            ctor: f,
            heritage: None,
            members: c,
            member_attrs: Vec::new(),
            count: 0,
        })),
        Op::DefineClass(Box::new(DefineClassData {
            ctor: f,
            heritage: Some(v()),
            members: c,
            member_attrs: Vec::new(),
            count: 1,
        })),
        Op::DefineSendableClass(Box::new(DefineClassData {
            ctor: f,
            heritage: Some(v()),
            members: c,
            member_attrs: Vec::new(),
            count: 1,
        })),
        // Private properties (5)
        Op::LoadPrivate {
            level: 0,
            slot: 0,
            obj: v(),
        },
        Op::StorePrivate {
            level: 0,
            slot: 0,
            obj: v(),
            value: v(),
        },
        Op::DefinePrivate {
            level: 0,
            slot: 0,
            obj: v(),
            value: v(),
        },
        Op::TestPrivate {
            level: 0,
            slot: 0,
            obj: v(),
        },
        Op::CreatePrivateNames { count: 1, names: c },
        // Exceptions (9)
        Op::Throw { value: v() },
        Op::ThrowIfSuperNotCalled {
            value: v(),
            kind: SuperCheck::NotCalled,
        },
        Op::ThrowUndefinedIfHole {
            name: v(),
            value: v(),
        },
        Op::ThrowUndefinedIfHoleWithName {
            name: s,
            value: v(),
        },
        Op::ThrowNotExists,
        Op::ThrowPatternNonCoercible,
        Op::ThrowDeleteSuperProperty,
        Op::ThrowConstAssignment { name: v() },
        Op::ThrowIfNotObject { value: v() },
        // Generator / async / concurrent (14)
        Op::CreateGenerator { func: v() },
        Op::CreateAsyncGenerator { func: v() },
        Op::SetGeneratorState {
            genobj: v(),
            state: 1,
        },
        Op::SuspendGenerator {
            genobj: v(),
            value: v(),
        },
        Op::ResumeGenerator { genobj: v() },
        Op::GetResumeMode { genobj: v() },
        Op::Await { value: v() },
        Op::AwaitUncaught {
            funcobj: v(),
            value: v(),
        },
        Op::AsyncFunctionEnter,
        Op::AsyncResolve {
            funcobj: v(),
            value: v(),
        },
        Op::AsyncReject {
            funcobj: v(),
            value: v(),
        },
        Op::AsyncGeneratorResolve {
            genobj: v(),
            value: v(),
            done: v(),
        },
        Op::AsyncGeneratorReject {
            genobj: v(),
            value: v(),
        },
        Op::NotifyConcurrentResult { value: v() },
        // Frame / special value loaders (6)
        Op::LoadSymbol,
        Op::LoadNewTarget,
        Op::LoadGlobalObject,
        Op::LoadFunction,
        Op::GetUnmappedArgs,
        Op::CopyRestArgs { start_index: 1 },
        // Super (2)
        Op::LoadSuper {
            key: SuperKey::Name(s),
            this_value: v(),
        },
        Op::LoadSuper {
            key: SuperKey::Dynamic(v()),
            this_value: v(),
        },
        Op::StoreSuper {
            key: SuperKey::Name(s),
            this_value: v(),
            value: v(),
        },
        Op::StoreSuper {
            key: SuperKey::Dynamic(v()),
            this_value: v(),
            value: v(),
        },
        // Control (5)
        Op::Branch { dest: b },
        Op::CondBranch {
            cond: v(),
            true_dest: b,
            false_dest: b,
        },
        Op::Return { value: None },
        Op::Return { value: Some(v()) },
        Op::Phi {
            entries: vec![(edge(0), v()), (edge(1), v())],
        },
        Op::Unreachable,
        // Debug (1)
        Op::Debugger,
    ];

    let absent = ValueId::new(u32::MAX);
    let mut distinct_discriminants = std::collections::HashSet::new();
    for op in &mut ops {
        distinct_discriminants.insert(std::mem::discriminant(op));
        let vec_ops = op.operands();
        let mut visited = Vec::new();
        op.for_each_operand(|val| visited.push(val));
        assert_eq!(visited, vec_ops, "for_each_operand order mismatch: {op:?}");

        let mut_ops: Vec<ValueId> = op.operands_mut().into_iter().map(|r| *r).collect();
        assert_eq!(mut_ops, vec_ops, "operands_mut order mismatch: {op:?}");

        for &operand in &vec_ops {
            assert!(
                op.has_operand(operand),
                "missing operand {operand} in {op:?}"
            );
        }
        assert!(!op.has_operand(absent), "unexpected absent match in {op:?}");

        if let Arity::Exact(n) = op.arity() {
            assert_eq!(vec_ops.len(), n, "arity mismatch: {op:?}");
        }

        // Entity visitor & mut-visitor parity across all 94 variants.
        let mut b_imm = Vec::new();
        let mut b_mut = Vec::new();
        op.for_each_block_id(|id| b_imm.push(id));
        op.for_each_block_id_mut(|id| {
            b_mut.push(*id);
            *id = BlockId::new(id.0 + 10);
        });
        assert_eq!(b_imm, b_mut, "block_id visitor mismatch: {op:?}");
        let mut b_after = Vec::new();
        op.for_each_block_id(|id| b_after.push(id));
        assert_eq!(
            b_after,
            b_imm
                .iter()
                .map(|id| BlockId::new(id.0 + 10))
                .collect::<Vec<_>>()
        );

        let mut c_imm = Vec::new();
        let mut c_mut = Vec::new();
        op.for_each_const_id(|id| c_imm.push(id));
        op.for_each_const_id_mut(|id| {
            c_mut.push(*id);
            *id = ConstId::new(id.0 + 10);
        });
        assert_eq!(c_imm, c_mut, "const_id visitor mismatch: {op:?}");

        let mut f_imm = Vec::new();
        let mut f_mut = Vec::new();
        op.for_each_func_id(|id| f_imm.push(id));
        op.for_each_func_id_mut(|id| {
            f_mut.push(*id);
            *id = FuncId::new(id.0 + 10);
        });
        assert_eq!(f_imm, f_mut, "func_id visitor mismatch: {op:?}");

        let mut s_imm = Vec::new();
        let mut s_mut = Vec::new();
        op.for_each_sym(|id| s_imm.push(id));
        op.for_each_sym_mut(|id| {
            s_mut.push(*id);
            *id = Sym::new(id.0 + 10);
        });
        assert_eq!(s_imm, s_mut, "sym visitor mismatch: {op:?}");

        let mut cls_imm = Vec::new();
        let mut cls_mut = Vec::new();
        op.for_each_class_id(|id| cls_imm.push(id));
        op.for_each_class_id_mut(|id| {
            cls_mut.push(*id);
            *id = ClassId::new(id.0 + 10);
        });
        assert_eq!(cls_imm, cls_mut, "class_id visitor mismatch: {op:?}");
    }
    assert_eq!(
        distinct_discriminants.len(),
        94,
        "test must cover all 94 Op variants"
    );
}

// ── Boolean result & module-var predicates ───────────────────────────────

#[test]
fn produces_bool_and_produces_bool_in_cover_constants_movs_and_phis() {
    use crate::function::{EdgeKind, Inst, Value};
    use crate::id::InstId;

    let mut m = Module::new();
    let c_true = m.consts.push(Const::Bool(true));
    let c_num = m.consts.push(Const::number(1.0));
    let b0 = BlockId::new(0);

    let v_bool_const = ValueId::new(0);
    m.values.push(Value {
        def: ValueDef::Inst(InstId::new(0)),
        ty: Ty::Any,
    });
    m.insts.push(Inst {
        op: Op::LoadConst(c_true),
        result: Some(v_bool_const),
        block: b0,
        loc: None,
    });

    let v_mov = ValueId::new(1);
    m.values.push(Value {
        def: ValueDef::Inst(InstId::new(1)),
        ty: Ty::Any,
    });
    m.insts.push(Inst {
        op: Op::Mov { src: v_bool_const },
        result: Some(v_mov),
        block: b0,
        loc: None,
    });

    let v_num = ValueId::new(2);
    m.values.push(Value {
        def: ValueDef::Const(c_num),
        ty: Ty::DynPrim(DynPrim::Number),
    });

    assert!(
        Op::Compare {
            op: CmpOp::Eq,
            left: v_num,
            right: v_num,
        }
        .produces_bool()
    );
    assert!(
        Op::TestProp {
            object: v_num,
            key: PropKey::Name(Sym::new(0)),
        }
        .produces_bool()
    );
    assert!(
        Op::TestPrivate {
            level: 0,
            slot: 0,
            obj: v_num,
        }
        .produces_bool()
    );
    assert!(
        Op::DeleteProp {
            object: v_num,
            key: v_num,
        }
        .produces_bool()
    );
    assert!(!Op::LoadConst(c_true).produces_bool());
    assert!(Op::LoadConst(c_true).produces_bool_in(&m));
    assert!(!Op::LoadConst(c_num).produces_bool_in(&m));
    assert!(Op::Mov { src: v_mov }.produces_bool_in(&m));
    assert!(!Op::Mov { src: v_num }.produces_bool_in(&m));

    let edge = Edge {
        from: b0,
        kind: EdgeKind::Normal,
    };
    assert!(
        Op::Phi {
            entries: vec![(edge, v_bool_const), (edge, v_mov)],
        }
        .produces_bool_in(&m)
    );
    assert!(
        !Op::Phi {
            entries: vec![(edge, v_bool_const), (edge, v_num)],
        }
        .produces_bool_in(&m)
    );
}

#[test]
fn module_var_kind_local_and_lazy_predicates() {
    assert!(ModuleVarKind::Local.is_local());
    assert!(ModuleVarKind::SendableLocal.is_local());
    assert!(ModuleVarKind::SendableClass.is_local());
    assert!(!ModuleVarKind::External.is_local());
    assert!(!ModuleVarKind::SendableExternal.is_local());
    assert!(!ModuleVarKind::Lazy.is_local());
    assert!(!ModuleVarKind::LazySendable.is_local());

    assert!(ModuleVarKind::Lazy.is_lazy());
    assert!(ModuleVarKind::LazySendable.is_lazy());
    assert!(!ModuleVarKind::SendableClass.is_lazy());
}
