//! N27/N23 regression (v0.2 port of v0.1 `opt_merge_empty_phi.rs`): the
//! optimizer must never leave an EMPTY phi (`Phi { entries: [] }`) on a
//! reachable block whose result feeds a use.
//!
//! Bug (probe-pinned on the corpus fixture
//! upstream/bytecode/ts/cases/test-namespace/optimized, opt variant ×6):
//!
//! ```text
//! bb_1 (entry): v_8 = undefined; v_9 = <callee>
//!               v_10 = IsTrue v_8; v_11 = IsTrue v_10
//!               CondBranch v_11, bb_3, bb_2
//! bb_2:         v_12 = CreateEmptyObject; Branch bb_3
//! bb_3:         v_13 = Phi [bb_1: v_9], [bb_2: v_9]
//!               v_14 = Phi [bb_1: v_8], [bb_2: v_12]
//!               v_15 = Call v_9, v_14; Return
//! ```
//!
//! Two defects chain into the empty phi:
//!
//! 1. SCCP folds the constant-false CondBranch to `Branch bb_2` and must
//!    remove bb_1 from bb_3.preds AND from bb_3's phi entries (N23) — a
//!    stale entry survives on the impossible path otherwise.
//! 2. `merge_single_succ_pred` must SUBSTITUTE the single incoming value
//!    for the absorbed successor's phi results (a single-pred phi is
//!    definitionally equal to its incoming value), never re-key the
//!    entries — re-keying onto the pred-less entry block manufactures
//!    `Phi { entries: [] }` whose result stays live (N27). Copyprop's
//!    trivial-phi arm sees zero entries → leaves it, ADCE keeps it
//!    (result live), lowering never writes its home register, and uses
//!    read frame garbage.

mod common;

use abcd_file::{AccessFlags, Builder, File, Type};
use abcd_ir::verify_module;
use abcd_ir::{
    BlockId, CallKind, Const, Edge, EdgeKind, FuncId, FunctionKind, Module, Op, ValueId,
};
use abcd_isa::{Bytecode, Label, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::lower_function;
use abcd_opt::sccp::Sccp;
use abcd_opt::{FuncPass, optimize_module};

use common::{EMPTY_OBJECT, Halt, Machine, V2Builder, empty_phis};

/// Build the corpus shape directly (v0.2: `AllocObject` for the empty
/// object, kinded edges). Returns (module, func, bb_1, bb_2, bb_3,
/// phi result v_14, object value v_12).
fn build_namespace_shape() -> (Module, FuncId, BlockId, BlockId, BlockId, ValueId, ValueId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "func_main_0", FunctionKind::Function);
    let bb_2;
    let bb_3;
    let v_12;
    let v_14;
    let bb_1;
    {
        let mut b = V2Builder::new(&mut module, func);
        bb_1 = b.entry();
        bb_2 = b.create_block();
        bb_3 = b.create_block();
        b.add_predecessor(bb_2, bb_1);
        b.add_predecessor(bb_3, bb_1);
        b.add_predecessor(bb_3, bb_2);

        // Entry: constant-false condition guarding the direct edge to bb_3.
        let undefined = b.konst(Const::Undefined);
        let v_8 = b.emit_val(Op::LoadConst(undefined));
        let v_9 = b.emit_number(1.0);
        let v_10 = b.emit_val(Op::UnaryOp {
            op: abcd_ir::UnOp::IsTrue,
            operand: v_8,
        });
        let v_11 = b.emit_val(Op::UnaryOp {
            op: abcd_ir::UnOp::IsTrue,
            operand: v_10,
        });
        b.emit_void(Op::CondBranch {
            cond: v_11,
            true_dest: bb_3,
            false_dest: bb_2,
        });

        // bb_2: the only live path, produces the object.
        b.set_insert_block(bb_2);
        let shape = b.konst(Const::ObjectLiteral {
            keys: vec![],
            values: vec![],
        });
        v_12 = b.emit_val(Op::AllocObject { shape });
        b.emit_void(Op::Branch { dest: bb_3 });

        // bb_3: join with a trivial phi (v_13) and the two-value phi (v_14).
        b.set_insert_block(bb_3);
        let n = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Normal,
        };
        b.emit_val(Op::Phi {
            entries: vec![(n(bb_1), v_9), (n(bb_2), v_9)],
        });
        v_14 = b.emit_val(Op::Phi {
            entries: vec![(n(bb_1), v_8), (n(bb_2), v_12)],
        });
        b.emit_val(Op::Call {
            callee: v_9,
            this: None,
            args: vec![v_14],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: None });
    }
    (module, func, bb_1, bb_2, bb_3, v_14, v_12)
}

/// Red pin (1), N23: when SCCP folds the constant CondBranch, the dead
/// edge's phi entries must be dropped together with the predecessor.
#[test]
fn sccp_branch_fold_removes_dead_edge_phi_entries() {
    let (mut module, func, bb_1, bb_2, bb_3, v_14, v_12) = build_namespace_shape();
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    let changed = Sccp.run(&mut module, func);
    assert!(changed, "SCCP must fold the constant-false CondBranch");

    // bb_1's terminator is now an unconditional branch to bb_2.
    let bb_1_term = *module.blocks[bb_1.index()].insts.last().unwrap();
    assert!(
        matches!(&module.insts[bb_1_term.index()].op, Op::Branch { dest } if *dest == bb_2),
        "CondBranch must fold to Branch bb_2: {:?}",
        module.insts[bb_1_term.index()].op
    );

    // The dead edge bb_1→bb_3 is gone from preds AND from phi entries.
    assert_eq!(
        module.blocks[bb_3.index()].preds,
        vec![Edge {
            from: bb_2,
            kind: EdgeKind::Normal
        }],
        "dead pred bb_1 must be removed from bb_3.preds"
    );
    let phi_id = module.blocks[bb_3.index()]
        .insts
        .iter()
        .copied()
        .find(|&id| {
            module.insts[id.index()].result == Some(v_14)
                && matches!(&module.insts[id.index()].op, Op::Phi { .. })
        });
    let Some(phi_id) = phi_id else {
        panic!("v_14 phi must survive SCCP (its value is Bottom)");
    };
    let Op::Phi { entries } = &module.insts[phi_id.index()].op else {
        unreachable!()
    };
    assert_eq!(
        entries,
        &[(
            Edge {
                from: bb_2,
                kind: EdgeKind::Normal
            },
            v_12
        )],
        "stale bb_1 entry must be dropped with the dead edge (N23)"
    );
}

/// Red test (2): the full pipeline must not leave an empty phi, and the
/// Call must receive the AllocObject value from the only live path (not
/// the stale undefined from the folded-away direct edge).
#[test]
fn optimized_namespace_shape_leaves_no_empty_phi_and_keeps_live_value() {
    let (mut module, _func, _bb_1, _bb_2, _bb_3, _v_14, v_12) = build_namespace_shape();
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    optimize_module(&mut module);

    assert!(
        empty_phis(&module).is_empty(),
        "optimizer must never leave an empty phi on a reachable block: {:?}",
        empty_phis(&module)
    );
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-opt verify: {:?}", report.errors);

    // The Call's argument is the AllocObject value from the live path.
    let call_args = (0..module.insts.len())
        .filter_map(|i| match &module.insts[i].op {
            Op::Call { args, .. } => Some(args.clone()),
            _ => None,
        })
        .next()
        .expect("the Call must survive the optimizer");
    assert_eq!(
        call_args,
        vec![v_12],
        "the call arg must be the AllocObject value from the only live \
         path, not the stale undefined from the folded-away edge"
    );
}

/// Build a 12.x file whose static method `f()` computes the corpus shape:
///
/// ```text
/// 0: ldundefined
/// 1: istrue              ; acc = false (constant-foldable)
/// 2: jnez L_JOIN         ; direct edge entry → JOIN (never taken)
/// 3: createemptyobject
/// 4: sta v0
/// 5: jmp L_JOIN
/// --- L_JOIN: (preds: entry, the object block) ---
/// 6: lda v0
/// 7: return
/// ```
///
/// JOIN's phi for v0 carries the frame-initial undefined (entry edge) and
/// the object (object-block edge); the entry edge is provably dead.
fn build_namespace_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let code_seq = [
        Bytecode::Ldundefined,
        Bytecode::Istrue,
        Bytecode::Jnez(Label(6)),
        Bytecode::Createemptyobject,
        Bytecode::Sta(Reg(0)),
        Bytecode::Jmp(Label(6)),
        Bytecode::Lda(Reg(0)),
        Bytecode::Return,
    ];
    let (bytes, offsets) = encode_bytecodes(&code_seq).unwrap();
    assert_eq!(offsets.len(), 8, "every instruction needs an offset");
    builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &bytes, 1, 0);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// Red test (3), e2e: lift → optimize → lower → simulate the namespace
/// shape. The optimized pipeline must deliver the created object to the
/// return; the empty phi's home register is never written and the read
/// yields frame garbage (0 in the simulator).
#[test]
fn optimized_namespace_shape_returns_created_object() {
    let file = build_namespace_file();
    let mut module = lift_file(&file).expect("namespace shape must lift");
    let func = (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.func(f).unwrap().name) == Some("f"))
        .expect("function f");

    optimize_module(&mut module);
    assert!(
        empty_phis(&module).is_empty(),
        "optimizer must never leave an empty phi on a reachable block"
    );
    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "optimized module must verify: {:?}",
        report.errors
    );

    let result = lower_function(&module, func).expect("optimized function must lower");
    let halt = Machine::new().run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(EMPTY_OBJECT),
        "the only live path returns the created object (N27; bytecodes: {:?})",
        result.bytecodes
    );
}
