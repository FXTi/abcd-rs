//! Empty-jump elimination must not merge converging edges that carry
//! DIFFERENT phi values (V4 / MEMORY.md "Empty-jump elimination must
//! preserve distinct values when a predecessor already has a direct edge
//! to the target").
//!
//! Bug (P3-T8, proven on the optional-chain corpus fixtures):
//! `opt::dce::eliminate_empty_jumps` threads a predecessor's edge around
//! a removed jump-only block. The per-PRED phi model cannot represent two
//! converging edges from the same pred carrying different values: when
//! pred P already has a direct edge to target T (phi value v_old) AND an
//! edge through the eliminated block B (phi value v_new != v_old), the
//! phi rewrite's `any(|(p,_)| *p == pred)` guard skips P's entry, so
//! v_new is silently dropped. Live corpus instance (optional-chain
//! optimized profile): `%bb_8` phi `[bb_5: v_17], [bb_6: v_15(=7)],
//! [bb_7: v_15]` — threading bb_5's false edge through removed bb_6
//! produced `CondBranch v_22, bb_8, bb_8` with the bb_6-mediated value 7
//! lost, printing `undefined` instead of `7`.
//!
//! The converging shape already exists at LIFT time: an Ark `mov`
//! lift-renames the destination vreg, so a block containing only
//! `mov v0, v1; jmp T` lifts to a jump-only block whose phi entry
//! carries the RENAMED value — while the jump-around edge from the same
//! pred carries the original value.
//!
//! Fix: `eliminate_empty_jumps` refuses to eliminate a jump-only block B
//! when any of its predecessors P also has a direct edge to B's target T
//! and T's phi entry for the B-mediated path differs from the entry for
//! the direct P path.

mod common;

use abcd_file::{AccessFlags, Builder, File, FileType, FunctionKind, Type, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{Block, FuncId};
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Imm, Label, Reg, encode as encode_bytecodes};

use common::{Halt, Machine, UNDEFINED};

/// Value arriving at T via the direct P → T edge.
const DIRECT_SENTINEL: i64 = 17;
/// Value arriving at T via the jump-only block B.
const THREADED_SENTINEL: i64 = 7;

/// Build the converging-edge shape directly:
///
/// ```text
/// p (entry): v_old = 17; v_new = 7; CondBranch(param, T, B)
/// B:         Branch T                      ; jump-only
/// T:         phi = Phi [(p, v_old), (B, v_new)]; Return phi
/// ```
///
/// P has BOTH a direct edge to T and an edge via B, and T's phi carries
/// DIFFERENT values for the two edge sources — eliminating B would
/// thread P's B-edge onto T and drop one value. Returns (module, func,
/// p, B, T, phi result value).
fn build_converging_module(
    distinct: bool,
) -> (Module, FuncId, Block, Block, Block, abcd_ir::entity::Value) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let p = module.func(func).entry_block;

    let b;
    let t;
    let phi;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        let cond = builder.create_func_param(0, IrType::default());
        b = builder.create_block();
        t = builder.create_block();

        builder.add_predecessor(b, p);
        builder.add_predecessor(t, p);
        builder.add_predecessor(t, b);

        let v_old = builder.emit_val(
            InstData::LiteralNumber(DIRECT_SENTINEL as f64),
            IrType::default(),
        );
        let v_new = if distinct {
            builder.emit_val(
                InstData::LiteralNumber(THREADED_SENTINEL as f64),
                IrType::default(),
            )
        } else {
            v_old
        };
        builder.emit_void(InstData::CondBranch {
            cond,
            true_dest: t,
            false_dest: b,
        });

        builder.set_insert_block(b);
        builder.emit_void(InstData::Branch { dest: t });

        builder.set_insert_block(t);
        phi = builder.emit_val(
            InstData::Phi {
                entries: vec![(p, v_old), (b, v_new)],
            },
            IrType::default(),
        );
        builder.emit_void(InstData::Return { value: Some(phi) });
    }
    (module, func, p, b, t, phi)
}

/// Red test (a): eliminating the jump-only block B would thread P's
/// B-edge onto T, whose phi already has a P entry carrying a DIFFERENT
/// value. The per-pred phi model cannot hold both, so elimination must
/// be REFUSED: B survives, both phi entries keep their values, and the
/// module still verifies. Today the elimination fires and the
/// B-mediated value is silently dropped.
#[test]
fn elimination_refused_when_converging_edges_carry_distinct_values() {
    let (mut module, func, p, b, t, phi) = build_converging_module(true);
    assert!(
        verify_module(&module).is_empty(),
        "fixture must verify pre-opt: {:?}",
        verify_module(&module)
    );

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        func_data.blocks.contains(&b),
        "jump-only block B must survive: its phi edge carries a value the \
         direct P edge does not (V4): blocks={:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&p) && func_data.blocks.contains(&t));

    // Both edge values are still present in T's phi.
    let phi_ids = &module.block(t).phis;
    let entries = phi_ids
        .iter()
        .find_map(|&id| match &module.inst(id).data {
            InstData::Phi { entries } if module.inst(id).result == Some(phi) => Some(entries),
            _ => None,
        })
        .expect("the phi must survive the optimizer");
    let value_of = |pred: Block| entries.iter().find(|(q, _)| *q == pred).map(|(_, v)| *v);
    let v_b = value_of(b).expect("B-mediated phi entry must survive");
    let v_p = value_of(p).expect("direct-edge phi entry must survive");
    assert_ne!(
        v_b, v_p,
        "the two converging edges carry distinct values that must both survive"
    );

    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-opt verify: {errors:?}");
}

/// Negative pin (b): when both converging edges carry the SAME value,
/// elimination is value-preserving and must STILL fire — the jump-only
/// block is removed, T's phi collapses to the single surviving edge,
/// and the module verifies.
#[test]
fn elimination_still_fires_when_converging_edges_agree() {
    let (mut module, func, _p, b, t, _phi) = build_converging_module(false);
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);

    let func_data = module.func(func);
    assert!(
        !func_data.blocks.contains(&b),
        "same-value converging edges must not block empty-jump elimination: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&t));
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-opt verify: {errors:?}");
}

/// Build a 12.x file whose static method `f(any a0)` computes
/// `a0 == undefined ? 7 : a0` in the optional-chain shape:
///
/// ```text
/// 0:  ldai 7
/// 1:  sta v1              ; v1 = 7 (the default)
/// 2:  ldundefined
/// 3:  sta v2              ; v2 = undefined
/// 4:  lda v3              ; acc = a0 (arg0 sits above the 3 vregs)
/// 5:  sta v0              ; v0 = a0 (the maybe-value)
/// 6:  lda v2              ; acc = undefined
/// 7:  jeq v0, L_UNDEF     ; a0 == undefined → jump-only block B
/// --- T (fall-through, the DIRECT P → T edge): ---
/// 8:  lda v0              ; acc = v0 (= a0 on this edge)
/// 9:  return
/// --- L_UNDEF (B): ---
/// 10: mov v0, v1          ; v0 = 7 (lifts to a rename → B is jump-only)
/// 11: jmp T
/// ```
///
/// Lift produces pred P (0..7) with a direct edge to T (8..9) AND an
/// edge via jump-only B (10..11); T's phi for v0 carries a0 for the
/// direct edge and 7 for the B-mediated edge.
fn build_optional_chain_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let code_seq = [
        Bytecode::Ldai(Imm(THREADED_SENTINEL)),
        Bytecode::Sta(Reg(1)),
        Bytecode::Ldundefined,
        Bytecode::Sta(Reg(2)),
        Bytecode::Lda(Reg(3)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Lda(Reg(2)),
        Bytecode::Jeq(Reg(0), Label(10)),
        Bytecode::Lda(Reg(0)),
        Bytecode::Return,
        Bytecode::Mov(Reg(0), Reg(1)),
        Bytecode::Jmp(Label(8)),
    ];
    let (bytes, offsets) = encode_bytecodes(&code_seq).unwrap();
    assert_eq!(offsets.len(), 12, "every instruction needs an offset");
    builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &bytes, 3, 1);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// Red test (c), e2e: lift → optimize → lower → simulate the
/// optional-chain shape. Today `eliminate_empty_jumps` threads P's
/// B-edge onto T and drops the B-mediated value 7, so the
/// `a0 == undefined` path wrongly returns the (undefined) parameter
/// instead of the default 7.
#[test]
fn optimized_optional_chain_shape_preserves_default_value() {
    let file = build_optional_chain_file();
    let mut module = lift_file(&file).expect("optional-chain shape must lift");
    let func = (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == "f")
        .expect("function f");

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(
        errors.is_empty(),
        "optimized module must verify: {errors:?}"
    );

    let result = lower_function(&module, func).expect("optimized function must lower");

    // a0 = 5 (defined): the direct edge carries the parameter through.
    let halt = Machine::new()
        .with_reg(result.num_regs, 5)
        .run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(5),
        "defined parameter must be returned unchanged (bytecodes: {:?})",
        result.bytecodes
    );

    // a0 = undefined: the B-mediated edge must deliver the default 7.
    // Today the elimination drops it and the undefined parameter leaks
    // through (V4).
    let halt = Machine::new()
        .with_reg(result.num_regs, UNDEFINED)
        .run(&result.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(THREADED_SENTINEL),
        "undefined parameter must select the default value 7 (V4; bytecodes: {:?})",
        result.bytecodes
    );
}
