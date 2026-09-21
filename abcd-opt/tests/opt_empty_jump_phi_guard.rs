//! V4 regression (v0.2 port of v0.1 `opt_empty_jump_phi_guard.rs`):
//! empty-jump elimination must not merge converging edges that carry
//! DIFFERENT phi values.
//!
//! Bug (proven on the optional-chain corpus fixtures):
//! `dce::eliminate_empty_jumps` threads a predecessor's edge around a
//! removed jump-only block. The per-PRED-EDGE phi model cannot represent
//! two converging same-kind edges from the same pred carrying different
//! values: when pred P already has a direct edge to target T (phi value
//! v_old) AND an edge through the eliminated block B (phi value
//! v_new != v_old), the phi rewrite's `any(|(e,_)| e.from == pred)`
//! guard skips P's entry, so v_new is silently dropped.
//!
//! Fix: `eliminate_empty_jumps` refuses to eliminate a jump-only block B
//! when any of its predecessors P also has a direct edge to B's target T
//! and T's phi entry for the B-mediated path differs from the entry for
//! the direct P path.

mod common;

use abcd_file::{AccessFlags, Builder, File, Type};
use abcd_ir2::verify_module;
use abcd_ir2::{BlockId, Edge, EdgeKind, FuncId, FunctionKind, Module, Op, ValueId};
use abcd_isa::{Bytecode, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::lower_function;
use abcd_opt::optimize_module;

use common::{Halt, Machine, UNDEFINED, V2Builder};

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
fn build_converging_module(distinct: bool) -> (Module, FuncId, BlockId, BlockId, BlockId, ValueId) {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let p;
    let b;
    let t;
    let phi;
    {
        let mut bd = V2Builder::new(&mut module, func);
        p = bd.entry();
        let cond = bd.create_param();
        b = bd.create_block();
        t = bd.create_block();

        bd.add_predecessor(b, p);
        bd.add_predecessor(t, p);
        bd.add_predecessor(t, b);

        let v_old = bd.emit_number(DIRECT_SENTINEL as f64);
        let v_new = if distinct {
            bd.emit_number(THREADED_SENTINEL as f64)
        } else {
            v_old
        };
        bd.emit_void(Op::CondBranch {
            cond,
            true_dest: t,
            false_dest: b,
        });

        bd.set_insert_block(b);
        bd.emit_void(Op::Branch { dest: t });

        bd.set_insert_block(t);
        let n = |from: BlockId| Edge {
            from,
            kind: EdgeKind::Normal,
        };
        phi = bd.emit_val(Op::Phi {
            entries: vec![(n(p), v_old), (n(b), v_new)],
        });
        bd.emit_void(Op::Return { value: Some(phi) });
    }
    (module, func, p, b, t, phi)
}

/// Red test (a): eliminating the jump-only block B would thread P's
/// B-edge onto T, whose phi already has a P entry carrying a DIFFERENT
/// value. The per-pred-edge phi model cannot hold both, so elimination
/// must be REFUSED: B survives, both phi entries keep their values, and
/// the module still verifies.
#[test]
fn elimination_refused_when_converging_edges_carry_distinct_values() {
    let (mut module, func, p, b, t, phi) = build_converging_module(true);
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
    assert!(
        func_data.blocks.contains(&b),
        "jump-only block B must survive: its phi edge carries a value the \
         direct P edge does not (V4): blocks={:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&p) && func_data.blocks.contains(&t));

    // Both edge values are still present in T's phi.
    let entries = module.blocks[t.index()]
        .insts
        .iter()
        .find_map(|&id| match &module.insts[id.index()].op {
            Op::Phi { entries } if module.insts[id.index()].result == Some(phi) => Some(entries),
            _ => None,
        })
        .expect("the phi must survive the optimizer");
    let value_of = |pred: BlockId| {
        entries
            .iter()
            .find(|(e, _)| e.from == pred)
            .map(|(_, v)| *v)
    };
    let v_b = value_of(b).expect("B-mediated phi entry must survive");
    let v_p = value_of(p).expect("direct-edge phi entry must survive");
    assert_ne!(
        v_b, v_p,
        "the two converging edges carry distinct values that must both survive"
    );

    let report = verify_module(&module);
    assert!(report.is_ok(), "post-opt verify: {:?}", report.errors);
}

/// Negative pin (b): when both converging edges carry the SAME value,
/// elimination is value-preserving and must STILL fire — the jump-only
/// block is removed, T's phi collapses to the single surviving edge,
/// and the module verifies.
#[test]
fn elimination_still_fires_when_converging_edges_agree() {
    let (mut module, func, _p, b, t, _phi) = build_converging_module(false);
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "fixture must verify pre-opt: {:?}", pre.errors);

    optimize_module(&mut module);

    let func_data = module.func(func).unwrap();
    assert!(
        !func_data.blocks.contains(&b),
        "same-value converging edges must not block empty-jump elimination: {:?}",
        func_data.blocks
    );
    assert!(func_data.blocks.contains(&t));
    let report = verify_module(&module);
    assert!(report.is_ok(), "post-opt verify: {:?}", report.errors);
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
/// optional-chain shape. Threading P's B-edge onto T would drop the
/// B-mediated value 7, so the `a0 == undefined` path would wrongly
/// return the (undefined) parameter instead of the default 7.
#[test]
fn optimized_optional_chain_shape_preserves_default_value() {
    let file = build_optional_chain_file();
    let mut module = lift_file(&file).expect("optional-chain shape must lift");
    let func = (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.func(f).unwrap().name) == Some("f"))
        .expect("function f");

    optimize_module(&mut module);
    let report = verify_module(&module);
    assert!(
        report.is_ok(),
        "optimized module must verify: {:?}",
        report.errors
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
