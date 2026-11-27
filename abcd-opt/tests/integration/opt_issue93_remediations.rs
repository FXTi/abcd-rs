//! Issue `#93` (Part 4: `abcd-opt`) regression suite:
//!
//! 1. Unified ECMA-262 constant-evaluation parity between `Peephole` and `Sccp`
//!    (`**` `ecma_pow`, `-0.0`, canonical `0x7ff8_0000_0000_0000` `NaN`,
//!    `ToBoolean` over `""` vs `"nonempty"` strings, `"0"` vs `"42"` BigInts,
//!    `Int8`/`Int32`/`Int64`/`UInt64`/`Float32`, allocation shapes, `Null` /
//!    `Undefined` arithmetic & `===`/`!==`, and loose `==`/`!=` non-coercion).
//! 2. `CondBranch(c, T, T) -> Branch(T)` (preserving throwing/effectful `c` and
//!    deduplicating duplicate `Normal` pred/phi entries) + `CondBranch(Bool)`
//!    folding across rounds + `Sccp` entry `CondBranch` seeding.
//! 3. `CopyProp` `Op::Mov` chain propagation (with cyclic-`Mov` guard) +
//!    `Adce`/`CfgSimplify`/`CopyProp` `DebugData` (`line_table`, `column_table`,
//!    `local_names` `LocalScope`) pruning verified by `abcd_ir::verify_module`.
//! 4. `inline.rs` rejecting nested lexical captures referenced via
//!    `Const::MethodRef` (`ObjectLiteral`, `ArrayLiteral`, `DefineClass`) or
//!    `DefineMethod`, materializing fresh caller-owned `Op::LoadConst` for
//!    callee `frame_init_consts` (`DuplicateValueDef`-free), and enforcing the
//!    `ic8` (`254`) inline-cache slot budget.

use crate::common::V2Builder;
use abcd_ir::{
    BinOp, CallKind, CmpOp, ColumnEntry, Const, DebugData, DefineClassData, Edge, EdgeKind,
    FunctionKind, InstId, LexEnvKind, LineEntry, LocalName, LocalScope, Modifiers, Module, Op,
    UnOp, ValueDef, ValueId, verify_module,
};
use abcd_opt::const_eval::CANONICAL_NAN_BITS;
use abcd_opt::copyprop::CopyProp;
use abcd_opt::dce::Adce;
use abcd_opt::inline::{InlinePolicy, SkipReason, inline_module};
use abcd_opt::peephole::Peephole;
use abcd_opt::sccp::Sccp;
use abcd_opt::{FuncPass, optimize_func, optimize_module};

const NEG_ZERO_BITS: u64 = 0x8000_0000_0000_0000;

fn verify_ok(module: &Module) {
    let report = verify_module(module);
    assert!(
        report.is_ok(),
        "module failed verification: {:?}",
        report.errors
    );
}

fn loaded_const(module: &Module, iid: InstId) -> Option<Const> {
    match &module.inst(iid)?.op {
        Op::LoadConst(cid) => module.consts.get(*cid).cloned(),
        _ => None,
    }
}

/// 1. `Peephole` and `Sccp` share one ECMA-262 constant-evaluation kernel and
///    produce bit-identical folds across `**`, `-0.0`, canonical `NaN`,
///    `ToBoolean` (`String`, `BigInt`, integer/float tags, allocations),
///    `Null`/`Undefined` arithmetic, and `===`/`!==`/`==`.
#[test]
fn peephole_and_sccp_ecma262_kernel_parity() {
    let run_suite = |pass: &dyn FuncPass| -> Vec<Option<Const>> {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
        let mut tracked: Vec<InstId> = Vec::new();
        {
            let mut b = V2Builder::new(&mut module, func);
            let s_empty = b.sym("");
            let s_abc = b.sym("abc");
            let s_zero_big = b.sym("0");
            let s_hex_zero_big = b.sym("-0x00");
            let s_nz_big = b.sym("42");
            let re_pat = b.sym("a+");

            let c_empty = b.konst(Const::String(s_empty));
            let c_abc = b.konst(Const::String(s_abc));
            let c_b0 = b.konst(Const::BigInt(s_zero_big));
            let c_bh0 = b.konst(Const::BigInt(s_hex_zero_big));
            let c_bnz = b.konst(Const::BigInt(s_nz_big));
            let c_i8_0 = b.konst(Const::Int8(0));
            let c_i8_7 = b.konst(Const::Int8(7));
            let c_i32_0 = b.konst(Const::Int32(0));
            let c_i32_9 = b.konst(Const::Int32(9));
            let c_i64_0 = b.konst(Const::Int64(0));
            let c_i64_5 = b.konst(Const::Int64(-5));
            let c_u64_0 = b.konst(Const::UInt64(0));
            let c_u64_5 = b.konst(Const::UInt64(5));
            let c_f32_n0 = b.konst(Const::Float32((-0.0_f32).to_bits()));
            let c_f32_nan = b.konst(Const::Float32(f32::NAN.to_bits()));
            let c_f32_2 = b.konst(Const::Float32(2.5_f32.to_bits()));
            let c_null = b.konst(Const::Null);
            let c_undef = b.konst(Const::Undefined);
            let empty_obj_shape = b.konst(Const::ObjectLiteral {
                keys: Vec::new(),
                values: Vec::new(),
            });

            let v_empty = b.emit_val(Op::LoadConst(c_empty));
            let v_abc = b.emit_val(Op::LoadConst(c_abc));
            let v_b0 = b.emit_val(Op::LoadConst(c_b0));
            let v_bh0 = b.emit_val(Op::LoadConst(c_bh0));
            let v_bnz = b.emit_val(Op::LoadConst(c_bnz));
            let v_i8_0 = b.emit_val(Op::LoadConst(c_i8_0));
            let v_i8_7 = b.emit_val(Op::LoadConst(c_i8_7));
            let v_i32_0 = b.emit_val(Op::LoadConst(c_i32_0));
            let v_i32_9 = b.emit_val(Op::LoadConst(c_i32_9));
            let v_i64_0 = b.emit_val(Op::LoadConst(c_i64_0));
            let v_i64_5 = b.emit_val(Op::LoadConst(c_i64_5));
            let v_u64_0 = b.emit_val(Op::LoadConst(c_u64_0));
            let v_u64_5 = b.emit_val(Op::LoadConst(c_u64_5));
            let v_f32_n0 = b.emit_val(Op::LoadConst(c_f32_n0));
            let v_f32_nan = b.emit_val(Op::LoadConst(c_f32_nan));
            let v_f32_2 = b.emit_val(Op::LoadConst(c_f32_2));
            let v_null = b.emit_val(Op::LoadConst(c_null));
            let v_undef = b.emit_val(Op::LoadConst(c_undef));
            let v_nzero = b.emit_number(-0.0);
            let v_three = b.emit_number(3.0);

            let v_obj = b.emit_val(Op::AllocObject {
                shape: empty_obj_shape,
            });
            let v_arr = b.emit_val(Op::AllocArray { shape: None });
            let v_re = b.emit_val(Op::AllocRegExp {
                pattern: re_pat,
                flags: 0,
            });

            // ToBoolean via IsTrue / LogicalNot across all scalar & alloc kinds.
            for v in [
                v_empty, v_abc, v_b0, v_bh0, v_bnz, v_i8_0, v_i8_7, v_i32_0, v_i32_9, v_i64_0,
                v_i64_5, v_u64_0, v_u64_5, v_f32_n0, v_f32_nan, v_f32_2, v_null, v_undef, v_nzero,
                v_obj, v_arr, v_re,
            ] {
                tracked.push(
                    b.emit(Op::UnaryOp {
                        op: UnOp::IsTrue,
                        operand: v,
                    })
                    .0,
                );
                tracked.push(
                    b.emit(Op::UnaryOp {
                        op: UnOp::LogicalNot,
                        operand: v,
                    })
                    .0,
                );
            }

            // Exp (`**`) with `-0.0 ** 3 == -0.0` (N36: right ** left).
            tracked.push(
                b.emit(Op::BinaryOp {
                    op: BinOp::Exp,
                    left: v_three,
                    right: v_nzero,
                })
                .0,
            );
            // Undefined + 3.0 -> canonical NaN; Null + 3.0 -> 3.0; String + 3.0 -> None.
            tracked.push(
                b.emit(Op::BinaryOp {
                    op: BinOp::Add,
                    left: v_three,
                    right: v_undef,
                })
                .0,
            );
            tracked.push(
                b.emit(Op::BinaryOp {
                    op: BinOp::Add,
                    left: v_three,
                    right: v_null,
                })
                .0,
            );
            tracked.push(
                b.emit(Op::BinaryOp {
                    op: BinOp::Add,
                    left: v_three,
                    right: v_abc,
                })
                .0,
            );

            // StrictEq / StrictNotEq across Strings, Null, Undefined, Numbers, cross-type.
            for (op, l, r) in [
                (CmpOp::StrictEq, v_abc, v_abc),
                (CmpOp::StrictEq, v_empty, v_abc),
                (CmpOp::StrictEq, v_null, v_null),
                (CmpOp::StrictEq, v_undef, v_undef),
                (CmpOp::StrictEq, v_null, v_undef),
                (CmpOp::StrictNotEq, v_null, v_three),
                (CmpOp::StrictEq, v_nzero, v_f32_n0),
                (CmpOp::Eq, v_null, v_undef),
            ] {
                tracked.push(
                    b.emit(Op::Compare {
                        op,
                        left: l,
                        right: r,
                    })
                    .0,
                );
            }

            b.emit_void(Op::Return { value: None });
        }
        verify_ok(&module);
        assert!(pass.run(&mut module, func));
        verify_ok(&module);
        tracked
            .into_iter()
            .map(|iid| loaded_const(&module, iid))
            .collect()
    };

    let p = run_suite(&Peephole);
    let s = run_suite(&Sccp);
    assert_eq!(p, s, "Peephole and Sccp constant-eval outputs must match");

    let want_truthy = [
        false, // ""
        true,  // "abc"
        false, // 0n
        false, // -0x00n
        true,  // 42n
        false, // Int8(0)
        true,  // Int8(7)
        false, // Int32(0)
        true,  // Int32(9)
        false, // Int64(0)
        true,  // Int64(-5)
        false, // UInt64(0)
        true,  // UInt64(5)
        false, // Float32(-0.0)
        false, // Float32(NaN)
        true,  // Float32(2.5)
        false, // Null
        false, // Undefined
        false, // -0.0
        true,  // AllocObject
        true,  // AllocArray
        true,  // AllocRegExp
    ];
    for (idx, &truthy) in want_truthy.iter().enumerate() {
        assert_eq!(p[idx * 2], Some(Const::Bool(truthy)), "IsTrue case {idx}");
        assert_eq!(
            p[idx * 2 + 1],
            Some(Const::Bool(!truthy)),
            "LogicalNot case {idx}"
        );
    }
    let tail = &p[want_truthy.len() * 2..];
    assert_eq!(tail[0], Some(Const::Number(NEG_ZERO_BITS)));
    assert_eq!(tail[1], Some(Const::Number(CANONICAL_NAN_BITS)));
    assert_eq!(tail[2], Some(Const::number(3.0)));
    assert_eq!(tail[3], None, "String + Number must not fold as f64 add");
    assert_eq!(tail[4], Some(Const::Bool(true)));
    assert_eq!(tail[5], Some(Const::Bool(false)));
    assert_eq!(tail[6], Some(Const::Bool(true)));
    assert_eq!(tail[7], Some(Const::Bool(true)));
    assert_eq!(tail[8], Some(Const::Bool(false)));
    assert_eq!(tail[9], Some(Const::Bool(true)));
    assert_eq!(tail[10], Some(Const::Bool(true)));
    assert_eq!(tail[11], None, "null == undefined loose eq stays unfolded");
}

/// 2a. `CondBranch(c, T, T) -> Branch(T)` preserves throwing/effectful `c`
///     producers through `Adce` on verified IR and deduplicates duplicate
///     `EdgeKind::Normal` pred/phi entries when present!
#[test]
fn same_target_condbranch_dedups_preds_and_preserves_throwing_cond_side_effects() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (entry, target, get_iid);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        target = b.create_block();

        let x_sym = b.sym("throwingGetterGlobal");
        let (gid, cond_val) = b.emit(Op::TryGetGlobal {
            name: x_sym,
            default: None,
        });
        get_iid = gid;
        let v1 = b.emit_number(10.0);

        b.add_predecessor(target, entry);
        b.emit_void(Op::CondBranch {
            cond: cond_val.unwrap(),
            true_dest: target,
            false_dest: target,
        });

        b.set_insert_block(target);
        let phi_v = b.emit_val(Op::Phi {
            entries: vec![(
                Edge {
                    from: entry,
                    kind: EdgeKind::Normal,
                },
                v1,
            )],
        });
        b.emit_void(Op::Return { value: Some(phi_v) });
    }
    verify_ok(&module);

    assert!(optimize_func(&mut module, func));
    verify_ok(&module);

    let blocks = &module.functions[func.index()].blocks;
    let has_try_get_global = blocks.iter().any(|&bb| {
        module.blocks[bb.index()].insts.iter().any(|&iid| {
            iid == get_iid && matches!(module.insts[iid.index()].op, Op::TryGetGlobal { .. })
        })
    });
    assert!(
        has_try_get_global,
        "throwing TryGetGlobal condition producer must survive CondBranch(c, T, T) + Adce"
    );

    // Also test duplicate-Normal pred/phi deduplication into a verified module.
    let mut dup = Module::new();
    let dfunc = V2Builder::create_function(&mut dup, "f_dup", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut dup, dfunc);
        let d_entry = b.entry();
        let d_target = b.create_block();
        let c = b.create_param();
        let v1 = b.emit_number(7.0);
        b.add_predecessor(d_target, d_entry);
        b.add_predecessor(d_target, d_entry);
        b.emit_void(Op::CondBranch {
            cond: c,
            true_dest: d_target,
            false_dest: d_target,
        });
        b.set_insert_block(d_target);
        let pv = b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: d_entry,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
                (
                    Edge {
                        from: d_entry,
                        kind: EdgeKind::Normal,
                    },
                    v1,
                ),
            ],
        });
        b.emit_void(Op::Return { value: Some(pv) });
    }
    assert!(Peephole.run(&mut dup, dfunc));
    verify_ok(&dup);
}

/// 2b. `Sccp` accurately seeds entry `CondBranch` (never marking dead arm
///     reachable, while still keeping `Exceptional` handler edges alive) and
///     multi-round `CondBranch(Const::Bool)` folds downstream diamond phis.
#[test]
fn sccp_entry_condbranch_seeding_folds_downstream_phi_and_keeps_handler() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (handler, ret_iid);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let live_arm = b.create_block();
        let dead_arm = b.create_block();
        let join = b.create_block();
        handler = b.create_block();

        b.add_predecessor(live_arm, entry);
        b.add_predecessor(dead_arm, entry);
        b.add_predecessor(join, live_arm);
        b.add_predecessor(join, dead_arm);

        let s_nonempty = b.sym("truthy");
        let c_str = b.konst(Const::String(s_nonempty));
        let cond = b.emit_val(Op::LoadConst(c_str));
        let g_sym = b.sym("maybeThrows");
        let _ = b.emit_val(Op::TryGetGlobal {
            name: g_sym,
            default: None,
        });
        b.emit_void(Op::CondBranch {
            cond,
            true_dest: live_arm,
            false_dest: dead_arm,
        });

        b.set_insert_block(live_arm);
        let v_live = b.emit_number(100.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(dead_arm);
        let v_dead = b.emit_number(999.0);
        b.emit_void(Op::Branch { dest: join });

        b.set_insert_block(join);
        let phi = b.emit_val(Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: live_arm,
                        kind: EdgeKind::Normal,
                    },
                    v_live,
                ),
                (
                    Edge {
                        from: dead_arm,
                        kind: EdgeKind::Normal,
                    },
                    v_dead,
                ),
            ],
        });
        let two = b.emit_number(2.0);
        let (_, prod) = b.emit(Op::BinaryOp {
            op: BinOp::Mul,
            left: two,
            right: phi,
        });
        ret_iid = b.emit(Op::Return { value: prod }).0;

        let exc = b.add_try(vec![entry], handler);
        b.set_insert_block(handler);
        b.emit_void(Op::Return { value: Some(exc) });
    }
    verify_ok(&module);

    assert!(optimize_module(&mut module));
    verify_ok(&module);

    assert!(
        module.functions[func.index()].blocks.contains(&handler),
        "protected entry's catch handler must remain reachable"
    );
    let Op::Return { value: Some(ret_v) } = module.insts[ret_iid.index()].op else {
        panic!("expected Return(Some)");
    };
    let ValueDef::Inst(def_iid) = module.values[ret_v.index()].def else {
        panic!("expected LoadConst def");
    };
    assert_eq!(loaded_const(&module, def_iid), Some(Const::number(200.0)));
}

/// 3. `CopyProp` propagates `Op::Mov` chains (and terminates on degenerate
///    unverified self/mutual `Mov` cycles), and `Adce` prunes dead `InstId`s
///    from `DebugData` so `verify_module` passes cleanly.
#[test]
fn copyprop_mov_chains_cycle_guard_and_adce_debug_table_pruning() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "f", FunctionKind::Function);
    let (i_keep, i_m1, i_m2, i_dead_pure, i_ret, p0);
    {
        let mut b = V2Builder::new(&mut module, func);
        p0 = b.create_param();
        let (m1_id, m1_v) = b.emit(Op::Mov { src: p0 });
        i_m1 = m1_id;
        let (m2_id, m2_v) = b.emit(Op::Mov { src: m1_v.unwrap() });
        i_m2 = m2_id;
        let c5 = b.konst(Const::number(5.0));
        let (keep_id, five_v) = b.emit(Op::LoadConst(c5));
        i_keep = keep_id;
        let (dead_id, _) = b.emit(Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand: five_v.unwrap(),
        });
        i_dead_pure = dead_id;
        i_ret = b
            .emit(Op::Return {
                value: Some(m2_v.unwrap()),
            })
            .0;

        let local_a = b.sym("a");
        let local_dead = b.sym("dead");
        b.module.functions[func.index()].debug = Some(DebugData {
            source_file: None,
            source_code: None,
            line_table: vec![
                LineEntry {
                    inst: i_m1,
                    line: 10,
                },
                LineEntry {
                    inst: i_keep,
                    line: 11,
                },
                LineEntry {
                    inst: i_dead_pure,
                    line: 12,
                },
                LineEntry {
                    inst: i_ret,
                    line: 13,
                },
            ],
            column_table: vec![
                ColumnEntry {
                    inst: i_m2,
                    column: 2,
                },
                ColumnEntry {
                    inst: i_dead_pure,
                    column: 6,
                },
                ColumnEntry {
                    inst: i_ret,
                    column: 9,
                },
            ],
            param_names: Vec::new(),
            local_names: vec![
                LocalName {
                    name: local_a,
                    ty: None,
                    scope: Some(LocalScope {
                        start: i_m1,
                        end: i_ret,
                    }),
                },
                LocalName {
                    name: local_dead,
                    ty: None,
                    scope: Some(LocalScope {
                        start: i_dead_pure,
                        end: i_dead_pure,
                    }),
                },
            ],
            scope_names: None,
        });
    }
    verify_ok(&module);

    assert!(CopyProp.run(&mut module, func));
    verify_ok(&module);
    assert!(
        matches!(module.insts[i_ret.index()].op, Op::Return { value: Some(v) } if v == p0),
        "CopyProp must forward Mov chain p0 -> m1 -> m2 to p0"
    );

    assert!(Adce.run(&mut module, func));
    verify_ok(&module);
    let dbg = module.functions[func.index()].debug.as_ref().unwrap();
    assert_eq!(
        dbg.line_table,
        vec![LineEntry {
            inst: i_ret,
            line: 13
        }]
    );
    assert_eq!(
        dbg.column_table,
        vec![ColumnEntry {
            inst: i_ret,
            column: 9
        }]
    );
    assert_eq!(
        dbg.local_names[0].scope,
        Some(LocalScope {
            start: i_ret,
            end: i_ret
        })
    );
    assert_eq!(dbg.local_names[1].scope, None);

    // Unverified mutual Mov cycle guard: `v_a = Mov(v_b); v_b = Mov(v_a)` must
    // terminate cleanly without hanging or panicking.
    let mut cyc = Module::new();
    let cf = V2Builder::create_function(&mut cyc, "cyc", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut cyc, cf);
        let dummy = ValueId::new(0);
        let (ia, va) = b.emit(Op::Mov { src: dummy });
        let (_ib, vb) = b.emit(Op::Mov { src: va.unwrap() });
        b.module.insts[ia.index()].op = Op::Mov { src: vb.unwrap() };
        b.emit_void(Op::Return { value: va });
    }
    let _ = CopyProp.run(&mut cyc, cf);
}

/// 4a. `inline.rs` rejects callees whose nested functions read lexical
///     environments when referenced via `ObjectLiteral`, `ArrayLiteral`,
///     `DefineClass` `members`, or `DefineMethod`!
#[test]
fn inline_rejects_nested_lexenv_capture_across_methodref_and_definemethod() {
    let mut module = Module::new();

    let make_static_fn = |module: &mut Module, name: &str| {
        let f = V2Builder::create_function(module, name, FunctionKind::Function);
        module.functions[f.index()].modifiers = Modifiers::STATIC;
        {
            let mut b = V2Builder::new(module, f);
            for _ in 0..3 {
                b.create_param();
            }
        }
        f
    };

    // Nested method reading outer lexical env (`GetLexVar`).
    let nested_reader = make_static_fn(&mut module, "nested_reader");
    {
        let mut b = V2Builder::new(&mut module, nested_reader);
        let v = b.emit_val(Op::GetLexVar {
            level: 0,
            slot: 0,
            kind: LexEnvKind::Plain,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }

    // 1) Callee referencing `nested_reader` via `AllocObject` -> `ObjectLiteral` -> `MethodRef`.
    let g_obj = make_static_fn(&mut module, "g_obj");
    {
        let mut b = V2Builder::new(&mut module, g_obj);
        let k_sym = b.sym("m");
        let k_cid = b.konst(Const::String(k_sym));
        let mr_cid = b.konst(Const::method_ref(nested_reader));
        let shape = b.konst(Const::ObjectLiteral {
            keys: vec![k_cid],
            values: vec![mr_cid],
        });
        let obj = b.emit_val(Op::AllocObject { shape });
        b.emit_void(Op::Return { value: Some(obj) });
    }

    // 2) Callee referencing `nested_reader` via `AllocArray` -> nested `ArrayLiteral` -> `MethodRef`.
    let g_arr = make_static_fn(&mut module, "g_arr");
    {
        let mut b = V2Builder::new(&mut module, g_arr);
        let mr_cid = b.konst(Const::method_ref(nested_reader));
        let inner = b.konst(Const::ArrayLiteral(vec![mr_cid]));
        let outer = b.konst(Const::ArrayLiteral(vec![inner]));
        let arr = b.emit_val(Op::AllocArray { shape: Some(outer) });
        b.emit_void(Op::Return { value: Some(arr) });
    }

    // 3) Callee referencing `nested_reader` via `DefineClass` `members` literal.
    let g_cls_ctor = make_static_fn(&mut module, "g_cls_ctor");
    {
        let mut b = V2Builder::new(&mut module, g_cls_ctor);
        let u = b.create_const_value(Const::Undefined);
        b.emit_void(Op::Return { value: Some(u) });
    }
    let g_cls = make_static_fn(&mut module, "g_cls");
    {
        let mut b = V2Builder::new(&mut module, g_cls);
        let mr_cid = b.konst(Const::method_ref(nested_reader));
        let members = b.konst(Const::ArrayLiteral(vec![mr_cid]));
        let cls = b.emit_val(Op::DefineClass(Box::new(DefineClassData {
            ctor: g_cls_ctor,
            heritage: None,
            members,
            member_attrs: Vec::new(),
            count: 0,
        })));
        b.emit_void(Op::Return { value: Some(cls) });
    }

    // 4) Callee referencing `nested_reader` via `DefineFunc` -> `DefineMethod`.
    let g_dm = make_static_fn(&mut module, "g_dm");
    {
        let mut b = V2Builder::new(&mut module, g_dm);
        let m_sym = b.sym("m");
        let empty_shape = b.konst(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        });
        let home = b.emit_val(Op::AllocObject { shape: empty_shape });
        let df = b.emit_val(Op::DefineFunc {
            body: nested_reader,
            captures: Vec::new(),
            length: 0,
        });
        let dm = b.emit_val(Op::DefineMethod {
            object: home,
            name: m_sym,
            func: df,
            length: 0,
        });
        b.emit_void(Op::Return { value: Some(dm) });
    }

    let caller = make_static_fn(&mut module, "caller");
    {
        let mut b = V2Builder::new(&mut module, caller);
        let mut last = None;
        for g in [g_obj, g_arr, g_cls, g_dm] {
            let df = b.emit_val(Op::DefineFunc {
                body: g,
                captures: Vec::new(),
                length: 0,
            });
            let cl = b.emit_val(Op::AllocClosure { func: df });
            last = Some(b.emit_val(Op::Call {
                callee: cl,
                this: None,
                args: Vec::new(),
                kind: CallKind::Dynamic,
            }));
        }
        b.emit_void(Op::Return { value: last });
    }
    verify_ok(&module);

    let report = inline_module(&mut module, &InlinePolicy::default());
    verify_ok(&module);
    assert_eq!(report.sites_inlined, 0, "{report:?}");
    assert_eq!(
        report.skips.get(&SkipReason::CalleeDefinesClosure),
        Some(&4),
        "all 4 MethodRef/DefineMethod nested lexenv readers must be rejected"
    );
}

/// 4b. `inline.rs` never shares `frame_init_consts` `ValueId`s across functions
///     (`VerifyErrorKind::DuplicateValueDef`-free) and enforces the `ic8`
///     (`254`) inline-cache slot budget (`CallerBudgetExhausted`).
#[test]
fn inline_materializes_fresh_consts_and_enforces_ic8_slot_budget() {
    let mut module = Module::new();

    let callee = V2Builder::create_function(&mut module, "add_const", FunctionKind::Function);
    module.functions[callee.index()].modifiers = Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut module, callee);
        for _ in 0..3 {
            b.create_param();
        }
        let x = b.create_param();
        let c10 = b.create_const_value(Const::number(10.0));
        let (_, sum) = b.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: c10,
            right: x,
        });
        b.emit_void(Op::Return { value: sum });
    }

    let caller = V2Builder::create_function(&mut module, "caller", FunctionKind::Function);
    module.functions[caller.index()].modifiers = Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut module, caller);
        let df = b.emit_val(Op::DefineFunc {
            body: callee,
            captures: Vec::new(),
            length: 1,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let a1 = b.emit_number(5.0);
        let r1 = b.emit_val(Op::Call {
            callee: cl,
            this: None,
            args: vec![a1],
            kind: CallKind::Dynamic,
        });
        let r2 = b.emit_val(Op::Call {
            callee: cl,
            this: None,
            args: vec![r1],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: Some(r2) });
    }
    verify_ok(&module);

    let rep = inline_module(&mut module, &InlinePolicy::default());
    assert_eq!(rep.sites_inlined, 2, "{rep:?}");
    verify_ok(&module);
    optimize_module(&mut module);
    verify_ok(&module);

    // `ic8` slot budget test: caller already uses 254 8-bit IC slots (`251`
    // `BinaryOp`s + `1` `DefineFunc` + `2` for `Call` = `254`), and `ic_callee`
    // adds 3 `BinaryOp`s (`254 - 2 + 3 = 255 > 254`), so inlining must skip
    // with `CallerBudgetExhausted`.
    let mut ic_mod = Module::new();
    let ic_callee = V2Builder::create_function(&mut ic_mod, "ic_callee", FunctionKind::Function);
    ic_mod.functions[ic_callee.index()].modifiers = Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut ic_mod, ic_callee);
        for _ in 0..3 {
            b.create_param();
        }
        let x = b.create_param();
        let mut acc = x;
        for _ in 0..3 {
            acc = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: acc,
                right: x,
            });
        }
        b.emit_void(Op::Return { value: Some(acc) });
    }

    let ic_caller = V2Builder::create_function(&mut ic_mod, "ic_caller", FunctionKind::Function);
    ic_mod.functions[ic_caller.index()].modifiers = Modifiers::STATIC;
    {
        let mut b = V2Builder::new(&mut ic_mod, ic_caller);
        let x = b.create_param();
        let mut cur = x;
        for _ in 0..251 {
            cur = b.emit_val(Op::BinaryOp {
                op: BinOp::Add,
                left: cur,
                right: x,
            });
        }
        let df = b.emit_val(Op::DefineFunc {
            body: ic_callee,
            captures: Vec::new(),
            length: 1,
        });
        let cl = b.emit_val(Op::AllocClosure { func: df });
        let res = b.emit_val(Op::Call {
            callee: cl,
            this: None,
            args: vec![cur],
            kind: CallKind::Dynamic,
        });
        b.emit_void(Op::Return { value: Some(res) });
    }
    verify_ok(&ic_mod);

    let policy = InlinePolicy {
        max_callee_insts: 64,
        max_inlined_insts_per_caller: 10_000,
    };
    let ic_rep = inline_module(&mut ic_mod, &policy);
    verify_ok(&ic_mod);
    assert_eq!(ic_rep.sites_inlined, 0, "{ic_rep:?}");
    assert_eq!(
        ic_rep.skips.get(&SkipReason::CallerBudgetExhausted),
        Some(&1)
    );
}
