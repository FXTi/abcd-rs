//! N27: the optimizer must never leave an EMPTY phi (`Phi { entries: [] }`)
//! on a reachable block whose result feeds a use.
//!
//! Bug (P3-T17 registration, probe-pinned on the corpus fixture
//! upstream/bytecode/ts/cases/test-namespace/optimized, opt variant ×6):
//! func_main_0 lifts to
//!
//! ```text
//! bb_1 (entry): v_8 = LiteralUndefined; v_9 = <callee>
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
//! 1. SCCP folds the constant-false CondBranch to `Branch bb_2` and removes
//!    bb_1 from bb_3.preds but leaves the STALE `[bb_1: v_8]` phi entry
//!    (N23). When CfgSimplify later merges bb_2 into bb_1, the bb_2→bb_1
//!    re-key creates duplicate bb_1 entries and `rebuild_predecessors`
//!    dedups keeping the FIRST — the stale undefined — dropping the
//!    correct CreateEmptyObject value from the only live path.
//! 2. `merge_single_succ_pred` (dce.rs) absorbs a single-pred successor by
//!    RE-KEYING its phi entries to the surviving block's preds. When the
//!    survivor is the ENTRY block (no preds) this produces
//!    `Phi { entries: [] }` whose result stays live (it feeds the Call).
//!    Copyprop's trivial-phi arm sees zero entries → `unique = None` →
//!    leaves it ("ADCE will clean it up"), but ADCE keeps it because the
//!    result is live. Lowering writes no phi copy for a pred-less phi, so
//!    the home register is never written and the call reads frame garbage
//!    ('TypeError: Obj is not a Valid object', exit 255 post-B4).
//!
//! Fixes: (1) SCCP drops the dead edge's phi entries together with the
//! pred when folding a branch; (2) the merge SUBSTITUTES the single
//! incoming value for the absorbed successor's phi results (a single-pred
//! phi is definitionally equal to its incoming value) instead of
//! re-keying entries.

mod common;

use abcd_file::{AccessFlags, Builder, File, FileType, FunctionKind, Type, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId, Value};
use abcd_ir::inst::{CallKind, InstData};
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::opt::{FuncPass, sccp};
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Label, Reg, encode as encode_bytecodes};

use common::{EMPTY_OBJECT, Halt, Machine};

/// Build the corpus shape directly. Returns (module, func, bb_1, bb_2,
/// bb_3, phi result v_14, object value v_12).
fn build_namespace_shape() -> (Module, FuncId, Block, Block, Block, Value, Value) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "func_main_0", FunctionKind::Function, 0);
    let bb_1 = module.func(func).entry_block;

    let bb_2;
    let bb_3;
    let v_12;
    let v_14;
    {
        let mut b = IRBuilder::new(&mut module, func);
        bb_2 = b.create_block();
        bb_3 = b.create_block();
        b.add_predecessor(bb_2, bb_1);
        b.add_predecessor(bb_3, bb_1);
        b.add_predecessor(bb_3, bb_2);

        // Entry: constant-false condition guarding the direct edge to bb_3.
        let v_8 = b.emit_val(InstData::LiteralUndefined, IrType::default());
        let v_9 = b.emit_val(InstData::LiteralNumber(1.0), IrType::default());
        let v_10 = b.emit_val(InstData::IsTrue { operand: v_8 }, IrType::default());
        let v_11 = b.emit_val(InstData::IsTrue { operand: v_10 }, IrType::default());
        b.emit_void(InstData::CondBranch {
            cond: v_11,
            true_dest: bb_3,
            false_dest: bb_2,
        });

        // bb_2: the only live path, produces the object.
        b.set_insert_block(bb_2);
        v_12 = b.emit_val(InstData::CreateEmptyObject, IrType::default());
        b.emit_void(InstData::Branch { dest: bb_3 });

        // bb_3: join with a trivial phi (v_13) and the two-value phi (v_14).
        b.set_insert_block(bb_3);
        b.emit_val(
            InstData::Phi {
                entries: vec![(bb_1, v_9), (bb_2, v_9)],
            },
            IrType::default(),
        );
        v_14 = b.emit_val(
            InstData::Phi {
                entries: vec![(bb_1, v_8), (bb_2, v_12)],
            },
            IrType::default(),
        );
        b.emit_val(
            InstData::Call {
                kind: CallKind::Call,
                callee: v_9,
                args: vec![v_14],
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: None });
    }
    (module, func, bb_1, bb_2, bb_3, v_14, v_12)
}

/// Find every phi with zero entries in the module.
fn empty_phis(module: &Module) -> Vec<String> {
    let mut out = Vec::new();
    for i in 0..module.functions.len() {
        let func = FuncId::from_index(i);
        for &bb in &module.func(func).blocks {
            for &phi_id in &module.block(bb).phis {
                if let InstData::Phi { entries } = &module.inst(phi_id).data {
                    if entries.is_empty() {
                        out.push(format!("{func} {bb} {phi_id}"));
                    }
                }
            }
        }
    }
    out
}

/// Red pin (1), N23: when SCCP folds the constant CondBranch, the dead
/// edge's phi entries must be dropped together with the predecessor.
/// Today the stale `[bb_1: v_8]` entry survives and later wins a merge
/// dedup, resurrecting a value from an impossible path.
#[test]
fn sccp_branch_fold_removes_dead_edge_phi_entries() {
    let (mut module, func, bb_1, bb_2, bb_3, v_14, v_12) = build_namespace_shape();
    assert!(verify_module(&module).is_empty());

    let changed = sccp::Sccp.run(&mut module, func);
    assert!(changed, "SCCP must fold the constant-false CondBranch");

    // bb_1's terminator is now an unconditional branch to bb_2.
    let bb_1_term = *module.block(bb_1).insts.last().unwrap();
    assert!(
        matches!(&module.inst(bb_1_term).data, InstData::Branch { dest } if *dest == bb_2),
        "CondBranch must fold to Branch bb_2: {:?}",
        module.inst(bb_1_term).data
    );

    // The dead edge bb_1→bb_3 is gone from preds AND from phi entries.
    assert_eq!(
        module.block(bb_3).preds,
        vec![bb_2],
        "dead pred bb_1 must be removed from bb_3.preds"
    );
    let phi_id = module.block(bb_3).phis.iter().copied().find(|&id| {
        module.inst(id).result == Some(v_14)
            && matches!(&module.inst(id).data, InstData::Phi { .. })
    });
    let Some(phi_id) = phi_id else {
        panic!(
            "v_14 phi must survive SCCP (its value is Bottom): {}",
            module.display_func(func)
        );
    };
    let InstData::Phi { entries } = &module.inst(phi_id).data else {
        unreachable!()
    };
    assert_eq!(
        entries,
        &[(bb_2, v_12)],
        "stale bb_1 entry must be dropped with the dead edge (N23)"
    );
}

/// Red test (2): the full pipeline must not leave an empty phi, and the
/// Call must receive the CreateEmptyObject value from the only live path
/// (not the stale undefined from the folded-away direct edge).
#[test]
fn optimized_namespace_shape_leaves_no_empty_phi_and_keeps_live_value() {
    let (mut module, func, _bb_1, _bb_2, _bb_3, _v_14, v_12) = build_namespace_shape();
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);

    assert!(
        empty_phis(&module).is_empty(),
        "optimizer must never leave an empty phi on a reachable block: {:?}\n{}",
        empty_phis(&module),
        module.display_func(func)
    );
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-opt verify: {errors:?}");

    // The Call's argument is the CreateEmptyObject value from the live path.
    let call_args = (0..module.insts.len())
        .filter_map(|i| match &module.insts[i].data {
            InstData::Call { args, .. } => Some(args.clone()),
            _ => None,
        })
        .next()
        .expect("the Call must survive the optimizer");
    assert_eq!(
        call_args,
        vec![v_12],
        "the call arg must be the CreateEmptyObject value from the only \
         live path, not the stale undefined from the folded-away edge\n{}",
        module.display_func(func)
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
/// return; today the empty phi's home register is never written and the
/// read yields frame garbage (0 in the simulator).
#[test]
fn optimized_namespace_shape_returns_created_object() {
    let file = build_namespace_file();
    let mut module = lift_file(&file).expect("namespace shape must lift");
    let func = (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == "f")
        .expect("function f");

    optimize_module(&mut module);
    assert!(
        empty_phis(&module).is_empty(),
        "optimizer must never leave an empty phi on a reachable block"
    );
    let errors = verify_module(&module);
    assert!(
        errors.is_empty(),
        "optimized module must verify: {errors:?}"
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
