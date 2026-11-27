//! Round 3 regression suite (`#50`, `#55`, `#57`, `#58`, `#60`, `#61`):
//! - `R3-X1` / `R3-A7`: `JumpEqz`/`JumpNez` fusion & standalone lowering,
//!   non-boolean `CondBranch` `Istrue` coercion, boolean fallthrough `Jnez` ->
//!   `Jeqz` inversion, and unconditional `Branch` fallthrough `Jmp` elision.
//! - `R3-X2`: 2-slot IC allocation on `Instanceof` / `Typeof` /
//!   `Createregexpwithliteral`, `0xFF` (`IC_SLOT_INVALID`) skip, and upstream
//!   `0xFFFF` (`ic_size == 0x1_0001`) + `0xFF` degradation past `u16::MAX`.
//! - `R3-X3` / `R3-X4` / `R3-M2`: competing catch-handler phis over shared
//!   protected blocks + cycle-safe `handler_phi_stores`, multi-`ExceptionParam`
//!   homing, and normal-vs-exceptional handler jump target separation.
//! - `R3-X5`: `*PropIdx` exact `0..=u32::MAX` bounds (`2^32`, `-1.0`, `-0.0`,
//!   multi-use `0` fall back to `*byvalue`).
//! - `#55` / `#60` / `R3-H1..H4` / `R3-H7` / `R3-M1`: full opcode parity,
//!   `wide.*` encodings, and canonical-vs-custom `NaN` lowering.
//! - `#50` / `R3-H8` / `R3-H9` / `R3-M8`: `MethodDebugInfo` reconstruction,
//!   `CatchBlock::type_class`, lossless `LiteralValue` tag roundtrips, ArkTS
//!   `SourceLang` / `Constructor`, and `256 KiB`-stack `5,000`-deep literal
//!   lowering.

use std::sync::Arc;

use abcd_file::{
    AccessFlags, AnnotationValue, Builder, FileType, LiteralValue, SourceLang as FileSourceLang,
    Type, Version,
};
use abcd_ir::{
    BinOp, CallKind, Catch, ClassData, ClassId, CmpOp, ColumnEntry as IrColumnEntry, Const,
    DebugData, Edge, EdgeKind, FuncId, FunctionKind, LexEnvKind, LineEntry as IrLineEntry,
    LitMethodKind, Loc, Modifiers, Module, Op, OwnStoreKind, SourceLang as IrSourceLang, SuperKey,
    TryRegion, Ty, TypedArrayTag, UnOp, verify_module,
};
use abcd_isa::{Bytecode, BytecodeFlags, Imm, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::regalloc;
use abcd_lower::{
    EntityResolver, LowerOptions, fusion, lower_function, lower_module, rewrite_file,
};

use crate::common::{Halt, Machine, V2Builder};

// ─── R3-X2: IC slot widths, 0xFF skip, and pure 16-bit overflow ──────────────

#[test]
fn instanceof_typeof_and_regexp_allocate_two_ic_slots_matching_isa_flags() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "ic_widths", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        let pat = b.sym("^ab+$");
        let t = b.emit_val(Op::UnaryOp {
            op: UnOp::TypeOf,
            operand: p,
        });
        let iof = b.emit_val(Op::Compare {
            op: CmpOp::InstanceOf,
            left: t,
            right: p,
        });
        let rx = b.emit_val(Op::AllocRegExp {
            pattern: pat,
            flags: 1,
        });
        let sum = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: iof,
            right: rx,
        });
        b.emit_void(Op::Return { value: Some(sum) });
    }
    let lowered = lower_function(&module, func).expect("IC width test must lower");

    let mut seen_slots: Vec<(&str, i64, bool)> = Vec::new();
    for bc in &lowered.bytecodes {
        let one_slot = bc.flags().contains(BytecodeFlags::ONE_SLOT);
        match *bc {
            Bytecode::Typeof(Imm(s))
            | Bytecode::Instanceof(Imm(s), _)
            | Bytecode::Createregexpwithliteral(Imm(s), _, _)
            | Bytecode::Add2(Imm(s), _) => {
                seen_slots.push((bc.mnemonic(), s, one_slot));
            }
            _ => {}
        }
    }
    // Note: N71 not triggered (`max < 0x100`), so dense order is exact:
    // typeof @ 0 (2 slots), instanceof @ 2 (2 slots), createregexpwithliteral @ 4 (2 slots), add2 @ 6 (1 slot) => ic_size = 7!
    assert_eq!(
        seen_slots,
        vec![
            ("typeof", 0, false),
            ("instanceof", 2, false),
            ("createregexpwithliteral", 4, false),
            ("add2", 6, true),
        ]
    );
    assert_eq!(lowered.ic_size, 7);
}

#[test]
fn ic_allocator_never_assigns_reserved_0xff_slot_on_1slot_or_2slot_streams() {
    // (a) 256 1-slot `ldglobalvar` (16-bit IC so N71 doesn't trigger):
    // 0..=254 occupy 255 slots; the 256th skips 0xFF and lands at 0x100!
    let mut m1 = Module::new();
    let f1 = V2Builder::create_function(&mut m1, "skip_ff_1slot", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut m1, f1);
        let g = b.sym("g");
        let mut last = None;
        for _ in 0..256 {
            last = Some(b.emit_val(Op::TryGetGlobal {
                name: g,
                default: None,
            }));
        }
        b.emit_void(Op::Return { value: last });
    }
    let res1 = lower_function(&m1, f1).expect("256 ldglobalvar must lower");
    let slots1: Vec<i64> = res1
        .bytecodes
        .iter()
        .filter_map(|bc| match *bc {
            Bytecode::Ldglobalvar(Imm(s), _) => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(slots1.len(), 256);
    assert!(!slots1.contains(&0xFF), "0xFF is reserved IC_SLOT_INVALID");
    assert_eq!(slots1[254], 0xFE);
    assert_eq!(slots1[255], 0x100);
    assert_eq!(res1.ic_size, 0x101);

    // (b) 128 2-slot `ldobjbyname`: 127 * 2 = 254 (0..=0xFD); the 128th would
    // start at 0xFE..=0xFF (straddling 0xFF) and must skip to 0x100!
    let mut m2 = Module::new();
    let f2 = V2Builder::create_function(&mut m2, "skip_ff_2slot", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut m2, f2);
        let p = b.create_param();
        let prop = b.sym("p");
        for _ in 0..128 {
            let _ = b.emit_val(Op::LoadProp {
                object: p,
                name: prop,
            });
        }
        b.emit_void(Op::Return { value: None });
    }
    let res2 = lower_function(&m2, f2).expect("128 ldobjbyname must lower");
    let slots2: Vec<i64> = res2
        .bytecodes
        .iter()
        .filter_map(|bc| match *bc {
            Bytecode::Ldobjbyname(Imm(s), _) => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(slots2.len(), 128);
    assert!(!slots2.contains(&0xFE) && !slots2.contains(&0xFF));
    assert_eq!(slots2[126], 0xFC);
    assert_eq!(slots2[127], 0x100);
    assert_eq!(res2.ic_size, 0x102);
}

#[test]
fn pure_16bit_ic_stream_beyond_u16_matches_upstream_0xffff_and_0xff_degradation() {
    // Ground-truth mirror of `ic-slot-16-overflow/baseline/input.abc`:
    // - 127 `stobjbyname`: `0x00..=0xFC` (`counter -> 0xFE`)
    // - 128th `stobjbyname`: straddles `0xFE..=0xFF`, skips to `0x100` (`counter -> 0x102`)
    // - 32,638 more `stobjbyname` (total 32,766): reach `0xFFFC` (`counter -> 0xFFFE`)
    // - 1 `trystglobalbyname` (`StoreGlobal` checked): takes `0xFFFE` (`counter -> 0xFFFF`)
    // - 32,767th `stobjbyname`: `counter == 0xFFFF <= 0xFFFF` -> `0xFFFF`, `counter -> 0x10001`
    // - 32,768th `stobjbyname`: `counter == 0x10001 > 0xFFFF` -> degrades to `0xFF`, `ic_size == 0x10001`!
    let mut module = Module::new();
    let func =
        V2Builder::create_function(&mut module, "pure_16bit_overflow", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p = b.create_param();
        let name = b.sym("x");
        for _ in 0..32_766 {
            b.emit_void(Op::StoreProp {
                object: p,
                name,
                value: p,
            });
        }
        b.emit_void(Op::StoreGlobal { name, value: p });
        b.emit_void(Op::StoreProp {
            object: p,
            name,
            value: p,
        });
        b.emit_void(Op::StoreProp {
            object: p,
            name,
            value: p,
        });
        b.emit_void(Op::Return { value: None });
    }

    let file = lower_module(&module, Version::new(12, 0, 6, 0))
        .expect("pure 16-bit IC stream beyond 0xFFFF must lower and materialize cleanly");
    let (_, m_pre) = file.all_methods().next().expect("lowered method");
    assert_eq!(m_pre.body.as_ref().expect("body").ic_size, Some(0x1_0001));

    let encoded = abcd_file::encode(&file).expect("encode 0x10001-slot method");
    let decoded = abcd_file::decode(&encoded).expect("decode 0x10001-slot method");
    let (_, m_out) = decoded.all_methods().next().expect("method");
    let slot_ann = m_out
        .annotations
        .compile_time
        .iter()
        .find(|a| decoded.strings.resolve(a.class_descriptor) == Some("L_ESSlotNumberAnnotation;"))
        .expect("L_ESSlotNumberAnnotation; on decoded method");
    assert_eq!(slot_ann.elements[0].value, AnnotationValue::U32(0x1_0001));
    let body = m_out.body.as_ref().expect("body");

    let stobj_slots: Vec<i64> = body
        .bytecodes()
        .iter()
        .filter_map(|bc| match *bc {
            Bytecode::Stobjbyname(Imm(s), ..) => Some(s),
            _ => None,
        })
        .collect();
    assert_eq!(stobj_slots.len(), 32_768);
    assert_eq!(stobj_slots[126], 0xFC);
    assert_eq!(stobj_slots[127], 0x100);
    assert_eq!(stobj_slots[32_765], 0xFFFC);
    assert_eq!(stobj_slots[32_766], 0xFFFF);
    assert_eq!(stobj_slots[32_767], 0xFF);
}

// ─── R3-X3, R3-X4, R3-M2: Exception handler phis, multi-exc, & normal loops ─

#[test]
fn competing_nested_catch_handler_phis_receive_disjoint_registers_and_cycle_safe_stores() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "nested_catch_phis", FunctionKind::Function);
    let (entry, prot, h1, h2, phi1, phi2);
    {
        let mut b = V2Builder::new(&mut module, func);
        entry = b.entry();
        prot = b.create_block();
        h1 = b.create_block();
        h2 = b.create_block();

        b.add_predecessor(prot, entry);
        b.add_exceptional_predecessor(h1, entry);
        b.add_exceptional_predecessor(h1, prot);
        b.add_exceptional_predecessor(h2, entry);
        b.add_exceptional_predecessor(h2, prot);
        let exc1 = b.create_exception_param(h1);
        let exc2 = b.create_exception_param(h2);

        let c10 = b.konst(Const::number(10.0));
        let v10 = b.emit_val(Op::LoadConst(c10));
        let c20 = b.konst(Const::number(20.0));
        let v20 = b.emit_val(Op::LoadConst(c20));
        b.emit_void(Op::Branch { dest: prot });

        b.set_insert_block(prot);
        let c100 = b.konst(Const::number(100.0));
        let v100 = b.emit_val(Op::LoadConst(c100));
        let c200 = b.konst(Const::number(200.0));
        let v200 = b.emit_val(Op::LoadConst(c200));
        b.emit_void(Op::Return { value: Some(v100) });

        let exc_edge = |from| Edge {
            from,
            kind: EdgeKind::Exceptional,
        };
        b.set_insert_block(h1);
        phi1 = b.emit_val(Op::Phi {
            entries: vec![(exc_edge(entry), v10), (exc_edge(prot), v100)],
        });
        b.emit_void(Op::Return { value: Some(phi1) });

        b.set_insert_block(h2);
        phi2 = b.emit_val(Op::Phi {
            entries: vec![(exc_edge(entry), v20), (exc_edge(prot), v200)],
        });
        b.emit_void(Op::Return { value: Some(phi2) });

        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry, prot],
            catches: vec![Catch {
                handler: h1,
                exception: exc1,
                type_class: None,
            }],
        });
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry, prot],
            catches: vec![Catch {
                handler: h2,
                exception: exc2,
                type_class: None,
            }],
        });
    }
    assert!(verify_module(&module).is_ok());

    let suppression = fusion::analyze(&module, &module.functions[func.index()].blocks);
    let alloc = regalloc::allocate(&module, func, &suppression).expect("regalloc");
    assert_ne!(
        alloc.allocation[&phi1], alloc.allocation[&phi2],
        "competing handler phis over shared protected blocks must not share a register"
    );

    let lowered = lower_function(&module, func).expect("lower nested catch phis");
    let h1_pc = lowered.try_blocks[0].catches[0].handler as usize;
    let h2_pc = lowered.try_blocks[1].catches[0].handler as usize;

    // Run `entry` + `prot` up to `prot`'s `Return` so both pinned stores execute!
    let ret_pc = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Return))
        .unwrap();
    let mut m1 = Machine::new();
    assert_eq!(m1.run_until(&lowered.bytecodes, 0, ret_pc), Halt::Stopped);
    let mut m2 = Machine::new();
    assert_eq!(m2.run_until(&lowered.bytecodes, 0, ret_pc), Halt::Stopped);

    assert_eq!(m1.run_at(&lowered.bytecodes, h1_pc), Halt::Return(100));
    assert_eq!(m2.run_at(&lowered.bytecodes, h2_pc), Halt::Return(200));
}

#[test]
fn shared_handler_with_multiple_exception_params_homes_all_used_params() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "multi_exc", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let h = b.create_block();
        b.add_exceptional_predecessor(h, entry);
        let e1 = b.create_exception_param(h);
        let e2 = b.create_exception_param(h);

        let c1 = b.konst(Const::number(1.0));
        let v1 = b.emit_val(Op::LoadConst(c1));
        b.emit_void(Op::Return { value: Some(v1) });

        b.set_insert_block(h);
        let sum = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: e1,
            right: e2,
        });
        b.emit_void(Op::Return { value: Some(sum) });

        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![
                Catch {
                    handler: h,
                    exception: e1,
                    type_class: None,
                },
                Catch {
                    handler: h,
                    exception: e2,
                    type_class: None,
                },
            ],
        });
    }

    let lowered = lower_function(&module, func).expect("multi-ExceptionParam handler must lower");
    let h_pc = lowered.try_blocks[0].catches[0].handler as usize;
    let mut machine = Machine::new().with_acc(35);
    assert_eq!(machine.run_at(&lowered.bytecodes, h_pc), Halt::Return(70));
}

#[test]
fn catch_handler_with_normal_loop_backedge_preserves_exception_param_across_iterations() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "handler_loop", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let h = b.create_block();
        let loop_body = b.create_block();
        let done = b.create_block();

        b.add_exceptional_predecessor(h, entry);
        b.add_predecessor(h, loop_body);
        b.add_predecessor(loop_body, h);
        b.add_predecessor(done, h);
        let exc = b.create_exception_param(h);

        let c0 = b.konst(Const::number(0.0));
        let v0 = b.emit_val(Op::LoadConst(c0));
        b.emit_void(Op::Return { value: Some(v0) });

        // Handler `h` is ALSO a loop header: iterates `i` from 0 -> 1 -> 2,
        // clobbering `acc` in `loop_body`, then returns `exc + i` when `i == 2`!
        b.set_insert_block(h);
        let (phi_iid, phi_opt) = b.emit(Op::Phi {
            entries: Vec::new(),
        });
        let i_phi = phi_opt.unwrap();
        let c2 = b.konst(Const::number(2.0));
        let two = b.emit_val(Op::LoadConst(c2));
        let cmp = b.emit_val(Op::Compare {
            op: CmpOp::Less,
            left: i_phi,
            right: two,
        });
        b.emit_void(Op::CondBranch {
            cond: cmp,
            true_dest: loop_body,
            false_dest: done,
        });

        b.set_insert_block(loop_body);
        let c1 = b.konst(Const::number(1.0));
        let one = b.emit_val(Op::LoadConst(c1));
        let i_next = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: i_phi,
            right: one,
        });
        // Clobber `acc` with 999 right before the back-edge branch to `h`!
        let c999 = b.konst(Const::number(999.0));
        let _clobber = b.emit_val(Op::LoadConst(c999));
        b.emit_void(Op::Branch { dest: h });

        b.set_insert_block(done);
        let res = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: exc,
            right: i_phi,
        });
        b.emit_void(Op::Return { value: Some(res) });

        module.insts[phi_iid.index()].op = Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Exceptional,
                    },
                    v0,
                ),
                (
                    Edge {
                        from: loop_body,
                        kind: EdgeKind::Normal,
                    },
                    i_next,
                ),
            ],
        };
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler: h,
                exception: exc,
                type_class: None,
            }],
        });
    }
    assert!(verify_module(&module).is_ok());

    let lowered = lower_function(&module, func).expect("handler loop must lower");
    let ret0_pc = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Return))
        .unwrap();
    let mut machine = Machine::new();
    assert_eq!(
        machine.run_until(&lowered.bytecodes, 0, ret0_pc),
        Halt::Stopped
    );
    let h_pc = lowered.try_blocks[0].catches[0].handler as usize;
    machine.acc = 50;
    assert_eq!(
        machine.run_at(&lowered.bytecodes, h_pc),
        Halt::Return(52),
        "normal back-edge into handler must skip ExceptionParam Sta prologue and apply phi copy: {:?}",
        lowered.bytecodes
    );
}

// ─── R3-X5 & R3-H7: *PropIdx bounds, *byvalue fallback, and wide.*byindex ────

#[test]
fn prop_idx_out_of_u32_range_neg_zero_and_multi_use_fall_back_to_byvalue_while_u32_uses_wide() {
    for bad_num in [4_294_967_296.0_f64, -1.0, -0.0] {
        let mut module = Module::new();
        let func = V2Builder::create_function(&mut module, "idx_bounds", FunctionKind::Function);
        {
            let mut b = V2Builder::new(&mut module, func);
            let obj = b.create_param();
            let cid = b.konst(Const::Number(bad_num.to_bits()));
            let idx = b.emit_val(Op::LoadConst(cid));
            let v = b.emit_val(Op::LoadPropIdx {
                object: obj,
                index: idx,
            });
            b.emit_void(Op::Return { value: Some(v) });
        }
        let lowered = lower_function(&module, func).expect("must fall back to ldobjbyvalue");
        assert!(
            !lowered.bytecodes.iter().any(|bc| matches!(
                bc,
                Bytecode::Ldobjbyindex(..) | Bytecode::WideLdobjbyindex(..)
            )),
            "{bad_num} must NOT fuse to *byindex: {:?}",
            lowered.bytecodes
        );
        assert!(
            lowered
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Ldobjbyvalue(..))),
            "{bad_num} must lower via ldobjbyvalue: {:?}",
            lowered.bytecodes
        );
    }

    // Multi-use `0` falls back to `*byvalue`.
    let mut multi_mod = Module::new();
    let multi_fn = V2Builder::create_function(&mut multi_mod, "multi_idx", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut multi_mod, multi_fn);
        let obj = b.create_param();
        let c0 = b.konst(Const::number(0.0));
        let idx = b.emit_val(Op::LoadConst(c0));
        let v = b.emit_val(Op::LoadPropIdx {
            object: obj,
            index: idx,
        });
        b.emit_void(Op::StorePropIdx {
            object: obj,
            index: idx,
            value: v,
        });
        b.emit_void(Op::Return { value: Some(v) });
    }
    let multi_res = lower_function(&multi_mod, multi_fn).expect("multi-use index lowers");
    assert!(
        multi_res
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldobjbyvalue(..)))
            && multi_res
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Stobjbyvalue(..)))
    );

    // `70_000` (`0x1_0000..=u32::MAX`) selects `wide.ldobjbyindex`, `wide.stobjbyindex`, `wide.stownbyindex`.
    let mut wide_mod = Module::new();
    let wide_fn = V2Builder::create_function(&mut wide_mod, "wide_idx", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut wide_mod, wide_fn);
        let obj = b.create_param();
        let c1 = b.konst(Const::number(70_000.0));
        let i1 = b.emit_val(Op::LoadConst(c1));
        let loaded = b.emit_val(Op::LoadPropIdx {
            object: obj,
            index: i1,
        });
        let c2 = b.konst(Const::number(70_001.0));
        let i2 = b.emit_val(Op::LoadConst(c2));
        b.emit_void(Op::StorePropIdx {
            object: obj,
            index: i2,
            value: loaded,
        });
        let c3 = b.konst(Const::number(70_002.0));
        let i3 = b.emit_val(Op::LoadConst(c3));
        b.emit_void(Op::StoreOwnPropIdx {
            object: obj,
            index: i3,
            value: loaded,
            kind: OwnStoreKind::OwnProp,
        });
        b.emit_void(Op::Return {
            value: Some(loaded),
        });
    }
    let wide_res = lower_function(&wide_mod, wide_fn).expect("wide *byindex must lower");
    encode_bytecodes(&wide_res.bytecodes).expect("wide *byindex must encode");
    assert!(
        wide_res
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::WideLdobjbyindex(Imm(70_000))))
            && wide_res
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::WideStobjbyindex(_, Imm(70_001))))
            && wide_res
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::WideStownbyindex(_, Imm(70_002))))
    );
}

// ─── R3-X1 & R3-A7: JumpEqz/JumpNez, CondBranch coercion/inversion, Jmp elision ─

#[test]
fn jump_eqz_jump_nez_fused_and_standalone_plus_boolean_fallthrough_inversion() {
    // 1. Fused `UnOp::JumpEqz` + `CondBranch` emits `Jeqz` with NO `Istrue`.
    let mut m_eqz = Module::new();
    let f_eqz = V2Builder::create_function(&mut m_eqz, "fused_jeqz", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut m_eqz, f_eqz);
        let entry = b.entry();
        let p = b.create_param();
        let t_bb = b.create_block();
        let f_bb = b.create_block();
        b.add_predecessor(t_bb, entry);
        b.add_predecessor(f_bb, entry);
        let cond = b.emit_val(Op::UnaryOp {
            op: UnOp::JumpEqz,
            operand: p,
        });
        b.emit_void(Op::CondBranch {
            cond,
            true_dest: t_bb,
            false_dest: f_bb,
        });
        b.set_insert_block(t_bb);
        let c1 = b.konst(Const::number(11.0));
        let v1 = b.emit_val(Op::LoadConst(c1));
        b.emit_void(Op::Return { value: Some(v1) });
        b.set_insert_block(f_bb);
        let c2 = b.konst(Const::number(22.0));
        let v2 = b.emit_val(Op::LoadConst(c2));
        b.emit_void(Op::Return { value: Some(v2) });
    }
    let res_eqz = lower_function(&m_eqz, f_eqz).expect("fused JumpEqz must lower");
    assert!(
        res_eqz
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jeqz(_)))
            && !res_eqz
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Istrue))
    );
    assert_eq!(
        Machine::new()
            .with_reg(res_eqz.num_regs, 0)
            .run(&res_eqz.bytecodes),
        Halt::Return(11)
    );
    assert_eq!(
        Machine::new()
            .with_reg(res_eqz.num_regs, 5)
            .run(&res_eqz.bytecodes),
        Halt::Return(22)
    );

    // 2. Standalone `UnOp::JumpEqz` / `UnOp::JumpNez` (returned as a value) materializes 0/1.
    let mut m_st = Module::new();
    let f_st = V2Builder::create_function(&mut m_st, "standalone_jeqz", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut m_st, f_st);
        let p = b.create_param();
        let eqz = b.emit_val(Op::UnaryOp {
            op: UnOp::JumpEqz,
            operand: p,
        });
        b.emit_void(Op::Return { value: Some(eqz) });
    }
    let res_st = lower_function(&m_st, f_st).expect("standalone JumpEqz must lower");
    encode_bytecodes(&res_st.bytecodes).expect("standalone JumpEqz internal labels must encode");
    assert_eq!(
        Machine::new()
            .with_reg(res_st.num_regs, 0)
            .run(&res_st.bytecodes),
        Halt::Return(1)
    );
    assert_eq!(
        Machine::new()
            .with_reg(res_st.num_regs, 9)
            .run(&res_st.bytecodes),
        Halt::Return(0)
    );

    // 3. Boolean `CondBranch` whose `true_dest` is immediate RPO fallthrough inverts `Jnez` -> `Jeqz(false_dest)`!
    // Shape: entry branches `(true -> mid, false -> join)`, `mid` branches `-> join`, so RPO is `[entry, mid, join]`!
    let mut m_inv = Module::new();
    let f_inv = V2Builder::create_function(&mut m_inv, "inv_fallthrough", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut m_inv, f_inv);
        let entry = b.entry();
        let p = b.create_param();
        let mid = b.create_block();
        let join = b.create_block();
        b.add_predecessor(mid, entry);
        b.add_predecessor(join, entry);
        b.add_predecessor(join, mid);
        let c0 = b.konst(Const::number(0.0));
        let z = b.emit_val(Op::LoadConst(c0));
        let cmp = b.emit_val(Op::Compare {
            op: CmpOp::Greater,
            left: p,
            right: z,
        });
        b.emit_void(Op::CondBranch {
            cond: cmp,
            true_dest: mid,
            false_dest: join,
        });
        b.set_insert_block(mid);
        let g = b.sym("side_effect");
        b.emit_void(Op::StoreGlobal { name: g, value: p });
        b.emit_void(Op::Branch { dest: join });
        b.set_insert_block(join);
        b.emit_void(Op::Return { value: Some(p) });
    }
    let res_inv = lower_function(&m_inv, f_inv).expect("fallthrough inversion must lower");
    assert!(
        res_inv
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Jeqz(_)))
            && !res_inv
                .bytecodes
                .iter()
                .any(|bc| matches!(bc, Bytecode::Jmp(_))),
        "both entry fallthrough inversion (Jeqz) and mid->join fallthrough Jmp elision must fire: {:?}",
        res_inv.bytecodes
    );
}

// ─── #55, #60, R3-H1..H4, R3-H7, R3-M1: New opcodes, wide.*, canonical NaN ───

#[test]
fn round3_new_opcodes_wide_lexenv_and_canonical_nan_encodings() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "all_new_ops", FunctionKind::AsyncGenerator);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p0 = b.create_param();
        let p1 = b.create_param();

        // #60: canonical NaN -> Ldnan; non-canonical NaN payload -> Fldai!
        let c_canon_nan = b.konst(Const::Number(0x7ff8_0000_0000_0000));
        let v_canon_nan = b.emit_val(Op::LoadConst(c_canon_nan));
        let c_custom_nan = b.konst(Const::Number(0x7ff8_0000_0000_0001));
        let v_custom_nan = b.emit_val(Op::LoadConst(c_custom_nan));

        // R3-M1: LogicalNot -> Isfalse; ToPropertyKey -> CallruntimeTopropertykey; LoadSymbol -> Ldsymbol.
        let v_not = b.emit_val(Op::UnaryOp {
            op: UnOp::LogicalNot,
            operand: v_canon_nan,
        });
        let v_key = b.emit_val(Op::UnaryOp {
            op: UnOp::ToPropertyKey,
            operand: v_custom_nan,
        });
        let v_sym = b.emit_val(Op::LoadSymbol);

        // #55 + R3-H7: LexEnvKind::{Plain, Sendable, Patch} + wide.* above u8!
        let _ = b.emit_val(Op::NewLexEnv {
            num_vars: 300,
            kind: LexEnvKind::Plain,
        });
        let sn_arr = b.konst(Const::ArrayLiteral(Vec::new()));
        let _ = b.emit_val(Op::NewLexEnvWithName {
            num_vars: 301,
            scope_names: sn_arr,
        });
        let _ = b.emit_val(Op::NewLexEnv {
            num_vars: 4,
            kind: LexEnvKind::Sendable,
        });
        let lv1 = b.emit_val(Op::GetLexVar {
            level: 300,
            slot: 2,
            kind: LexEnvKind::Plain,
        });
        b.emit_void(Op::PutLexVar {
            level: 1,
            slot: 300,
            value: lv1,
            kind: LexEnvKind::Sendable,
        });
        let lv_patch = b.emit_val(Op::GetLexVar {
            level: 0,
            slot: 3,
            kind: LexEnvKind::Patch,
        });
        b.emit_void(Op::PutLexVar {
            level: 0,
            slot: 3,
            value: lv_patch,
            kind: LexEnvKind::Patch,
        });
        let rest = b.emit_val(Op::CopyRestArgs { start_index: 300 });

        // R3-H1: LoadSuper(Name) loads `this_value` into acc!
        let sup_name = b.sym("supProp");
        let v_sup = b.emit_val(Op::LoadSuper {
            key: SuperKey::Name(sup_name),
            this_value: p1,
        });

        // R3-H3: OwnStoreKind::{OwnPropWithNameSet, ClassField, DefineProperty}
        let own_name = b.sym("fnField");
        b.emit_void(Op::StoreOwnPropName {
            object: p0,
            name: own_name,
            value: v_sup,
            kind: OwnStoreKind::OwnPropWithNameSet,
        });
        b.emit_void(Op::StoreOwnPropName {
            object: p0,
            name: own_name,
            value: v_sup,
            kind: OwnStoreKind::DefineProperty,
        });
        b.emit_void(Op::StoreOwnPropDyn {
            object: p0,
            key: v_key,
            value: v_not,
            kind: OwnStoreKind::OwnPropWithNameSet,
        });
        b.emit_void(Op::StoreOwnPropDyn {
            object: p0,
            key: v_sym,
            value: rest,
            kind: OwnStoreKind::ClassField,
        });

        // #55 async generator + concurrent + calls (`NewSpread`, `SuperArrow`, `ClassInit`)
        let gen_obj = b.emit_val(Op::CreateAsyncGenerator { func: p0 });
        b.emit_void(Op::SetGeneratorState {
            genobj: gen_obj,
            state: 2,
        });
        let resolved = b.emit_val(Op::AsyncGeneratorResolve {
            genobj: gen_obj,
            value: p0,
            done: v_not,
        });
        let rejected = b.emit_val(Op::AsyncGeneratorReject {
            genobj: gen_obj,
            value: resolved,
        });
        b.emit_void(Op::NotifyConcurrentResult { value: rejected });

        let new_spread = b.emit_val(Op::Call {
            callee: p0,
            this: None,
            args: vec![p1],
            kind: CallKind::NewSpread,
        });
        let sup_arrow = b.emit_val(Op::Call {
            callee: p0,
            this: None,
            args: vec![new_spread, p1],
            kind: CallKind::SuperArrow,
        });
        let cls_init = b.emit_val(Op::Call {
            callee: sup_arrow,
            this: Some(p0),
            args: Vec::new(),
            kind: CallKind::ClassInit,
        });

        b.emit_void(Op::Return {
            value: Some(cls_init),
        });
    }
    assert!(verify_module(&module).is_ok());

    let lowered = lower_function(&module, func).expect("all Round 3 ops must lower");
    encode_bytecodes(&lowered.bytecodes).expect("all Round 3 ops must encode");
    let bcs = &lowered.bytecodes;

    assert!(bcs.iter().any(|bc| matches!(bc, Bytecode::Ldnan)));
    assert!(bcs.iter().any(|bc| matches!(
        bc,
        Bytecode::Fldai(Imm(bits)) if *bits as u64 == 0x7ff8_0000_0000_0001
    )));
    assert!(bcs.iter().any(|bc| matches!(bc, Bytecode::Isfalse)));
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeTopropertykey))
    );
    assert!(bcs.iter().any(|bc| matches!(bc, Bytecode::Ldsymbol)));
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideNewlexenv(Imm(300))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideNewlexenvwithname(Imm(301), _)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeNewsendableenv(Imm(4))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideLdlexvar(Imm(300), Imm(2))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeWidestsendablevar(Imm(1), Imm(300))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideLdpatchvar(Imm(3))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideStpatchvar(Imm(3))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::WideCopyrestargs(Imm(300))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Ldsuperbyname(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Stownbynamewithnameset(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Definepropertybyname(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Stownbyvaluewithnameset(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeDefinefieldbyvalue(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Createasyncgeneratorobj(_)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Setgeneratorstate(Imm(2))))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Asyncgeneratorresolve(..)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Asyncgeneratorreject(_)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeNotifyconcurrentresult))
    );
    assert!(bcs.iter().any(|bc| matches!(bc, Bytecode::Newobjapply(..))));
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::Supercallarrowrange(_, Imm(2), _)))
    );
    assert!(
        bcs.iter()
            .any(|bc| matches!(bc, Bytecode::CallruntimeCallinit(..)))
    );
}

// ─── #50, R3-H8, R3-H9, R3-M8: Debug rebuild, typed Catch, lossless tags, 256 KiB stack ─

#[test]
fn rewrite_file_and_lower_module_rebuild_method_debug_and_clear_stale_locals() {
    let mut b = Builder::new();
    b.set_api(12, "beta1");
    let cls = b.add_global_class();
    b.class_set_source_lang(cls, FileSourceLang::EcmaScript);
    let proto = b.create_proto(Type::Tagged, &[Type::Tagged]);
    let (code, _) = encode_bytecodes(&[Bytecode::Lda(Reg(0)), Bytecode::Return]).unwrap();
    let m1 = b.class_add_method(cls, "with_dbg", proto, AccessFlags::STATIC, &code, 0, 1);
    b.method_set_source_lang(m1, FileSourceLang::EcmaScript);
    let m2 = b.class_add_method(cls, "stripped_dbg", proto, AccessFlags::STATIC, &code, 0, 1);
    b.method_set_source_lang(m2, FileSourceLang::EcmaScript);

    let mut base_file = abcd_file::decode(&b.finalize().unwrap()).unwrap();
    // Seed rich `MethodDebugInfo` (including stale `local_vars`) on `base_file`
    // so both `lift_file` and `rewrite_file` exercise stale-local clearing and
    // `MethodDebugInfo` stripping/rebuilding end-to-end.
    let sf_orig = base_file.strings.get_or_intern("orig.ts");
    let sc_orig = base_file
        .strings
        .get_or_intern("function with_dbg(arg0) { return arg0; }");
    let p_arg0 = base_file.strings.get_or_intern("arg0");
    let empty_s = base_file.strings.get_or_intern("");
    let stale_var = base_file.strings.get_or_intern("stale_local");
    let sf_strip = base_file.strings.get_or_intern("strip.ts");
    for cls_item in base_file.classes.values_mut() {
        for m in &mut cls_item.methods {
            if base_file.strings.resolve(m.name) == Some("with_dbg") {
                m.debug = Some(abcd_file::MethodDebugInfo {
                    source_file: Some(sf_orig),
                    source_code: Some(sc_orig),
                    line_table: vec![abcd_file::LineEntry { index: 0, line: 10 }],
                    column_table: Vec::new(),
                    local_vars: vec![abcd_file::LocalVarInfo {
                        name: stale_var,
                        type_name: empty_s,
                        type_signature: empty_s,
                        reg_number: 0,
                        start: 0,
                        end: 1,
                    }],
                    params: vec![abcd_file::ParamInfo {
                        name: p_arg0,
                        signature: empty_s,
                    }],
                });
            } else if base_file.strings.resolve(m.name) == Some("stripped_dbg") {
                m.debug = Some(abcd_file::MethodDebugInfo {
                    source_file: Some(sf_strip),
                    source_code: None,
                    line_table: vec![abcd_file::LineEntry { index: 0, line: 20 }],
                    column_table: Vec::new(),
                    local_vars: Vec::new(),
                    params: Vec::new(),
                });
            }
        }
    }
    let mut module = lift_file(&base_file).unwrap();

    // Update `with_dbg` with two instructions carrying distinct lines/columns, and strip `stripped_dbg`'s debug!
    let f_with = (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.functions[f.index()].name) == Some("with_dbg"))
        .unwrap();
    let f_strip = (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| module.sym.resolve(module.functions[f.index()].name) == Some("stripped_dbg"))
        .unwrap();
    module.functions[f_strip.index()].debug = None;

    let bb = module.functions[f_with.index()].blocks[0];
    module.blocks[bb.index()].insts.clear();
    let (i_add, i_ret) = {
        let p0 = module.functions[f_with.index()].params[0];
        let mut vb = V2Builder::new(&mut module, f_with);
        let (i1, sum_opt) = vb.emit(Op::BinaryOp {
            op: BinOp::Add,
            left: p0,
            right: p0,
        });
        let (i2, _) = vb.emit(Op::Return { value: sum_opt });
        (i1, i2)
    };
    module.insts[i_add.index()].loc = Some(Loc {
        line: 42,
        column: Some(5),
    });
    module.insts[i_ret.index()].loc = Some(Loc {
        line: 43,
        column: Some(12),
    });
    let sf = module.sym.intern("rebuilt.ts");
    let pname = module.sym.intern("renamed_arg");
    module.functions[f_with.index()].debug = Some(DebugData {
        source_file: Some(sf),
        source_code: Some(Arc::from("const x = 1;")),
        line_table: vec![
            IrLineEntry {
                inst: i_add,
                line: 42,
            },
            IrLineEntry {
                inst: i_ret,
                line: 43,
            },
        ],
        column_table: vec![
            IrColumnEntry {
                inst: i_add,
                column: 5,
            },
            IrColumnEntry {
                inst: i_ret,
                column: 12,
            },
        ],
        local_names: Vec::new(),
        param_names: vec![pname],
        scope_names: None,
    });
    assert!(verify_module(&module).is_ok());

    for out_file in [
        rewrite_file(&module, &base_file, LowerOptions::default()).expect("rewrite_file"),
        lower_module(&module, Version::new(12, 0, 6, 0)).expect("lower_module"),
    ] {
        let encoded = abcd_file::encode(&out_file).expect("encode with rebuilt debug");
        let decoded = abcd_file::decode(&encoded).expect("decode with rebuilt debug");

        let m_with_out = decoded
            .all_methods()
            .find(|(_, m)| decoded.strings.resolve(m.name) == Some("with_dbg"))
            .unwrap()
            .1;
        let dbg = m_with_out.debug.as_ref().expect("rebuilt debug present");
        assert_eq!(
            dbg.source_file.and_then(|s| decoded.strings.resolve(s)),
            Some("rebuilt.ts")
        );
        assert_eq!(
            dbg.source_code.and_then(|s| decoded.strings.resolve(s)),
            Some("const x = 1;")
        );
        assert!(
            dbg.local_vars.is_empty(),
            "stale local_vars must be cleared on rewrite"
        );
        let lines: Vec<u32> = dbg.line_table.iter().map(|e| e.line).collect();
        assert!(
            lines.contains(&42) && lines.contains(&43),
            "rebuilt line_table must preserve lines 42 and 43: {lines:?}"
        );
        for pair in dbg.line_table.windows(2) {
            assert!(pair[0].index < pair[1].index);
        }
        let cols: Vec<u32> = dbg.column_table.iter().map(|e| e.column).collect();
        assert!(
            cols.contains(&5) && cols.contains(&12),
            "rebuilt column_table must preserve columns 5 and 12: {cols:?}"
        );

        let m_strip_out = decoded
            .all_methods()
            .find(|(_, m)| decoded.strings.resolve(m.name) == Some("stripped_dbg"))
            .unwrap()
            .1;
        assert!(
            m_strip_out.debug.is_none(),
            "func.debug = None must clear Method.debug"
        );
    }
}

#[test]
fn typed_catch_arkts_metadata_and_lossless_literal_tags_roundtrip() {
    let mut m = Module::new();
    let global_desc = m.sym.intern("LArkMain;");
    let mut main_cls = ClassData::new(global_desc, global_desc);
    main_cls.modifiers = Modifiers::PUBLIC;
    main_cls.source_lang = IrSourceLang::ArkTS;
    m.classes.push(main_cls);

    let err_desc = m.sym.intern("LMyError;");
    let mut err_cls = ClassData::new(err_desc, err_desc);
    err_cls.source_lang = IrSourceLang::ArkTS;
    let err_cid = ClassId::new(m.classes.len() as u32);
    m.classes.push(err_cls);

    let f_ctor = V2Builder::create_function(&mut m, "ctor", FunctionKind::Constructor);
    let f_arrow = V2Builder::create_function(&mut m, "arrow_fn", FunctionKind::AsyncArrow);
    {
        let mut b = V2Builder::new(&mut m, f_arrow);
        b.emit_void(Op::Return { value: None });
    }

    let ets_sym = m.sym.intern("LIFoo;");
    let s_sym = m.sym.intern("hello");
    let c_i8 = m.consts.push(Const::Int8(7));
    let c_i32 = m.consts.push(Const::Int32(1024));
    let c_f32 = m.consts.push(Const::float32(1.25));
    let c_f64 = m.consts.push(Const::number(3.5));
    let c_acc = m.consts.push(Const::Accessor(2));
    let c_aff = m.consts.push(Const::MethodAffiliate(9));
    let c_bti = m.consts.push(Const::BuiltinTypeIndex(4));
    let c_ets = m.consts.push(Const::EtsImplements(ets_sym));
    let c_null = m.consts.push(Const::LitNull(3));
    let c_str = m.consts.push(Const::String(s_sym));
    let c_get = m
        .consts
        .push(Const::method_ref_with_kind(f_ctor, LitMethodKind::Getter));
    let inner_arr = m.consts.push_array(vec![c_i32]);
    let root_wire_shape = m.consts.push_array(vec![
        c_i8, c_i32, c_f32, c_f64, c_acc, c_aff, c_bti, c_ets, c_null, c_str, c_get, inner_arr,
    ]);
    let c_buf = m.consts.push(Const::LiteralBufferRef(inner_arr));
    let c_ta = m.consts.push(Const::TypedArrayLiteral {
        tag: TypedArrayTag::U8,
        items: vec![c_i8],
    });
    let full_14_shape = m.consts.push_array(vec![
        c_i8, c_i32, c_f32, c_f64, c_acc, c_aff, c_bti, c_ets, c_null, c_str, c_get, inner_arr,
        c_buf, c_ta,
    ]);

    {
        let mut b = V2Builder::new(&mut m, f_ctor);
        let entry = b.entry();
        let handler = b.create_block();
        b.add_exceptional_predecessor(handler, entry);
        let exc = b.create_exception_param(handler);

        let arr = b.emit_val(Op::AllocArray {
            shape: Some(root_wire_shape),
        });
        b.emit_void(Op::Return { value: Some(arr) });

        b.set_insert_block(handler);
        b.emit_void(Op::Return { value: Some(exc) });

        m.functions[f_ctor.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler,
                exception: exc,
                type_class: Some(err_cid),
            }],
        });
    }
    assert!(verify_module(&m).is_ok());

    let file = lower_module(&m, Version::new(12, 0, 6, 0)).expect("lower_module");
    assert_eq!(file.file_type, FileType::Dynamic);
    let ark_cls = file.class_by_str("LArkMain;").expect("LArkMain;");
    assert_eq!(ark_cls.source_lang, FileSourceLang::ArkTs);
    assert!(
        ark_cls.methods[0]
            .access_flags
            .contains(AccessFlags::CONSTRUCTOR)
    );
    let tb = &ark_cls.methods[0].body.as_ref().unwrap().try_blocks[0];
    assert_eq!(
        tb.catches[0]
            .type_class
            .and_then(|s| file.strings.resolve(s)),
        Some("LMyError;")
    );

    let in_mem_lifted = lift_file(&file).expect("in-memory lift_file");
    assert_eq!(in_mem_lifted.functions[0].kind, FunctionKind::Constructor);
    assert_eq!(in_mem_lifted.functions[1].kind, FunctionKind::AsyncArrow);
    assert_eq!(in_mem_lifted.classes[0].source_lang, IrSourceLang::ArkTS);

    let encoded = abcd_file::encode(&file).expect("encode");
    let decoded = abcd_file::decode(&encoded).expect("decode");
    let relifted = lift_file(&decoded).expect("relift");
    assert!(verify_module(&relifted).is_ok());

    let relifted_ark_cls = relifted
        .classes
        .iter()
        .find(|c| relifted.sym.resolve(c.descriptor) == Some("LArkMain;"))
        .expect("relifted LArkMain;");
    assert_eq!(relifted_ark_cls.source_lang, IrSourceLang::ArkTS);
    assert_eq!(relifted.functions[1].kind, FunctionKind::AsyncArrow);
    let caught_cid = relifted.functions[0].try_regions[0].catches[0]
        .type_class
        .expect("typed catch class survives");
    assert_eq!(
        relifted
            .sym
            .resolve(relifted.classes[caught_cid.index()].descriptor),
        Some("LMyError;")
    );

    let root_la = decoded
        .literal_arrays
        .iter()
        .find(|la| la.values.len() == 12)
        .expect("12-element wire literal array");
    assert!(matches!(root_la.values[0], LiteralValue::Integer8(7)));
    assert!(matches!(root_la.values[1], LiteralValue::Integer(1024)));
    assert!(matches!(root_la.values[2], LiteralValue::Float(v) if (v - 1.25).abs() < 1e-6));
    assert!(matches!(root_la.values[3], LiteralValue::Double(v) if (v - 3.5).abs() < 1e-12));
    assert!(matches!(root_la.values[4], LiteralValue::Accessor(2)));
    assert!(matches!(
        root_la.values[5],
        LiteralValue::MethodAffiliate(9)
    ));
    assert!(matches!(
        root_la.values[6],
        LiteralValue::BuiltinTypeIndex(4)
    ));
    assert!(matches!(root_la.values[7], LiteralValue::EtsImplements(_)));
    assert!(matches!(root_la.values[8], LiteralValue::NullValue(3)));
    assert!(matches!(root_la.values[9], LiteralValue::String(_)));
    assert!(matches!(root_la.values[10], LiteralValue::Getter(_)));
    assert!(matches!(root_la.values[11], LiteralValue::LiteralArray(_)));

    // Also verify in-memory `File` materialization + `lift_file` for `LiteralBufferIndex` & `ArrayU8`.
    m.classes[0].scope_names = Some(full_14_shape);
    let mem_file = lower_module(&m, Version::new(12, 0, 6, 0)).expect("lower_module 14-tag");
    let full_la = mem_file
        .literal_arrays
        .iter()
        .find(|la| la.values.len() == 14)
        .expect("14-element materialized literal array");
    assert!(matches!(
        full_la.values[12],
        LiteralValue::LiteralBufferIndex(_)
    ));
    assert!(matches!(full_la.values[13], LiteralValue::ArrayU8(_)));
    let mem_relifted = lift_file(&mem_file).expect("lift_file 14-tag in-memory File");
    assert!(verify_module(&mem_relifted).is_ok());
}

#[test]
fn deep_5000_nested_literal_shape_lowers_and_resolves_on_256kib_stack() {
    let handle = std::thread::Builder::new()
        .name("deep-5000-lit-256k".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut module = Module::new();
            let func = V2Builder::create_function(&mut module, "deep5000", FunctionKind::Function);
            let leaf = module.consts.push(Const::Int32(99));
            let mut cur = module.consts.push_array(vec![leaf]);
            for _ in 1..5_000 {
                cur = module.consts.push_array(vec![cur]);
            }
            {
                let mut b = V2Builder::new(&mut module, func);
                let arr = b.emit_val(Op::AllocArray { shape: Some(cur) });
                b.emit_void(Op::Return { value: Some(arr) });
            }
            let layout = lower_function(&module, func).expect("lower_function on 256 KiB stack");
            let file = lower_module(&module, Version::new(12, 0, 6, 0))
                .expect("lower_module 5000-deep literal on 256 KiB stack");
            assert_eq!(file.literal_arrays.len(), 5_000);
            let resolver = EntityResolver::new(&module, &file);
            let body = resolver
                .to_method_body(func, &layout)
                .expect("EntityResolver 5000-deep literal on 256 KiB stack");
            assert_eq!(body.entities.len(), 1);
            let _ = Ty::Any;
        })
        .expect("spawn 256 KiB thread");
    handle
        .join()
        .expect("5000-deep literal shape must not overflow 256 KiB stack");
}

#[test]
fn definefieldbyvalue_emits_key_then_obj_for_dyn_and_unfused_idx_and_roundtrips() {
    let mut module = Module::new();
    let func = V2Builder::create_function(&mut module, "define_field_dyn", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let p_obj = b.create_param();
        let p_key = b.create_param();
        let p_idx = b.create_param();
        let p_val = b.create_param();
        b.emit_void(Op::StoreOwnPropDyn {
            object: p_obj,
            key: p_key,
            value: p_val,
            kind: OwnStoreKind::ClassField,
        });
        b.emit_void(Op::StoreOwnPropIdx {
            object: p_obj,
            index: p_idx,
            value: p_val,
            kind: OwnStoreKind::ClassField,
        });
        b.emit_void(Op::Return { value: None });
    }
    assert!(verify_module(&module).is_ok());

    let lowered = lower_function(&module, func).expect("definefieldbyvalue must lower");
    let field_ops: Vec<(Reg, Reg)> = lowered
        .bytecodes
        .iter()
        .filter_map(|bc| match *bc {
            Bytecode::CallruntimeDefinefieldbyvalue(_, key_r, obj_r) => Some((key_r, obj_r)),
            _ => None,
        })
        .collect();
    assert_eq!(
        field_ops,
        vec![(Reg(1), Reg(0)), (Reg(2), Reg(0))],
        "callruntime.definefieldbyvalue must pass (key_reg, obj_reg)"
    );

    let file = lower_module(&module, Version::new(12, 0, 6, 0)).expect("lower_module");
    let encoded = abcd_file::encode(&file).expect("encode");
    let decoded = abcd_file::decode(&encoded).expect("decode");
    let relifted = lift_file(&decoded).expect("lift_file");
    let rf = &relifted.functions[0];
    let lifted_stores: Vec<(abcd_ir::ValueId, abcd_ir::ValueId)> = rf
        .blocks
        .iter()
        .flat_map(|&bb| &relifted.blocks[bb.index()].insts)
        .filter_map(|&iid| match relifted.insts[iid.index()].op {
            Op::StoreOwnPropDyn {
                object,
                key,
                kind: OwnStoreKind::ClassField,
                ..
            } => Some((object, key)),
            _ => None,
        })
        .collect();
    assert_eq!(
        lifted_stores,
        vec![(rf.params[0], rf.params[1]), (rf.params[0], rf.params[2])],
        "round-tripped definefieldbyvalue must preserve object vs key operands"
    );
}

#[test]
fn supercallthisrange_suppresses_ldfunction_for_single_and_csed_multi_branch_super() {
    // 1. Single-site `LoadFunction` + `CallKind::Super` (`v2lift` shape).
    let mut m1 = Module::new();
    let f1 = V2Builder::create_function(&mut m1, "ctor1", FunctionKind::Constructor);
    {
        let mut b = V2Builder::new(&mut m1, f1);
        let p0 = b.create_param();
        let lf = b.emit_val(Op::LoadFunction);
        let sup = b.emit_val(Op::Call {
            callee: lf,
            this: None,
            args: vec![p0],
            kind: CallKind::Super,
        });
        b.emit_void(Op::Return { value: Some(sup) });
    }
    let res1 = lower_function(&m1, f1).expect("single supercallthisrange must lower");
    assert!(
        !res1
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldfunction)),
        "single-site super(...) must never emit Bytecode::Ldfunction: {:?}",
        res1.bytecodes
    );
    assert!(
        res1.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Supercallthisrange(_, Imm(1), _)))
    );

    // 2. Two-branch diamond sharing one CSE'd `LoadFunction` (`v2opt` shape).
    let mut m2 = Module::new();
    let f2 = V2Builder::create_function(&mut m2, "ctor2", FunctionKind::Constructor);
    {
        let mut b = V2Builder::new(&mut m2, f2);
        let entry = b.entry();
        let b_then = b.create_block();
        let b_else = b.create_block();
        b.add_predecessor(b_then, entry);
        b.add_predecessor(b_else, entry);

        let flag = b.create_param();
        let arg = b.create_param();
        let lf = b.emit_val(Op::LoadFunction);
        b.emit_void(Op::CondBranch {
            cond: flag,
            true_dest: b_then,
            false_dest: b_else,
        });

        b.set_insert_block(b_then);
        let s1 = b.emit_val(Op::Call {
            callee: lf,
            this: None,
            args: vec![arg],
            kind: CallKind::Super,
        });
        b.emit_void(Op::Return { value: Some(s1) });

        b.set_insert_block(b_else);
        let s2 = b.emit_val(Op::Call {
            callee: lf,
            this: None,
            args: Vec::new(),
            kind: CallKind::Super,
        });
        b.emit_void(Op::Return { value: Some(s2) });
    }
    let res2 = lower_function(&m2, f2).expect("CSE'd supercallthisrange must lower");
    assert!(
        !res2
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldfunction)),
        "CSE'd multi-branch super(...) must never emit Bytecode::Ldfunction: {:?}",
        res2.bytecodes
    );
    assert_eq!(
        res2.bytecodes
            .iter()
            .filter(|bc| matches!(bc, Bytecode::Supercallthisrange(..)))
            .count(),
        2
    );

    // 3. `LoadFunction` also used by `Return` must keep `Bytecode::Ldfunction`.
    let mut m3 = Module::new();
    let f3 = V2Builder::create_function(&mut m3, "ctor3", FunctionKind::Constructor);
    {
        let mut b = V2Builder::new(&mut m3, f3);
        let lf = b.emit_val(Op::LoadFunction);
        let _ = b.emit_val(Op::Call {
            callee: lf,
            this: None,
            args: Vec::new(),
            kind: CallKind::Super,
        });
        b.emit_void(Op::Return { value: Some(lf) });
    }
    let res3 = lower_function(&m3, f3).expect("dual-use LoadFunction must lower");
    assert!(
        res3.bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Ldfunction))
    );
}

#[test]
fn catch_handler_with_normal_backedge_reloads_exception_param_into_acc() {
    let mut module = Module::new();
    let func =
        V2Builder::create_function(&mut module, "handler_acc_reload", FunctionKind::Function);
    {
        let mut b = V2Builder::new(&mut module, func);
        let entry = b.entry();
        let h = b.create_block();
        let loop_body = b.create_block();
        let done = b.create_block();

        b.add_exceptional_predecessor(h, entry);
        b.add_predecessor(h, loop_body);
        b.add_predecessor(loop_body, h);
        b.add_predecessor(done, h);
        let exc = b.create_exception_param(h);

        let c0 = b.konst(Const::number(0.0));
        let v0 = b.emit_val(Op::LoadConst(c0));
        b.emit_void(Op::Return { value: Some(v0) });

        // Inside `h` itself, `Add2` reads `left` (`exc`) in `acc` (`add2 ic, right_reg`).
        // Because `loop_body` jumps back to `h` skipping `Sta(exc_home)` with
        // `acc == 999`, `isel` must NOT assume `acc` holds `exc` at `h` body start!
        b.set_insert_block(h);
        let (phi_iid, phi_opt) = b.emit(Op::Phi {
            entries: Vec::new(),
        });
        let i_phi = phi_opt.unwrap();
        let sum_in_h = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: exc,
            right: i_phi,
        });
        let c1 = b.konst(Const::number(1.0));
        let one = b.emit_val(Op::LoadConst(c1));
        let cmp = b.emit_val(Op::Compare {
            op: CmpOp::Less,
            left: i_phi,
            right: one,
        });
        b.emit_void(Op::CondBranch {
            cond: cmp,
            true_dest: loop_body,
            false_dest: done,
        });

        b.set_insert_block(loop_body);
        let c1_b = b.konst(Const::number(1.0));
        let one_b = b.emit_val(Op::LoadConst(c1_b));
        let i_next = b.emit_val(Op::BinaryOp {
            op: BinOp::Add,
            left: i_phi,
            right: one_b,
        });
        let c999 = b.konst(Const::number(999.0));
        let _clobber = b.emit_val(Op::LoadConst(c999));
        b.emit_void(Op::Branch { dest: h });

        b.set_insert_block(done);
        b.emit_void(Op::Return {
            value: Some(sum_in_h),
        });

        module.insts[phi_iid.index()].op = Op::Phi {
            entries: vec![
                (
                    Edge {
                        from: entry,
                        kind: EdgeKind::Exceptional,
                    },
                    v0,
                ),
                (
                    Edge {
                        from: loop_body,
                        kind: EdgeKind::Normal,
                    },
                    i_next,
                ),
            ],
        };
        module.functions[func.index()].try_regions.push(TryRegion {
            protected: vec![entry],
            catches: vec![Catch {
                handler: h,
                exception: exc,
                type_class: None,
            }],
        });
    }
    assert!(verify_module(&module).is_ok());

    let lowered = lower_function(&module, func).expect("handler loop must lower");
    let cb = &lowered.try_blocks[0].catches[0];
    let h_start = cb.handler as usize;
    let h_end = (cb.handler + cb.len) as usize;
    let Bytecode::Sta(exc_reg) = lowered.bytecodes[h_start] else {
        panic!(
            "expected handler prologue Sta at pc {h_start}: {:?}",
            lowered.bytecodes
        );
    };
    assert!(
        lowered.bytecodes[h_start + 1..h_end]
            .iter()
            .any(|bc| matches!(*bc, Bytecode::Lda(r) if r == exc_reg)),
        "handler with normal predecessor must emit explicit Lda({exc_reg:?}) after prologue: {:?}",
        &lowered.bytecodes[h_start..h_end]
    );

    let ret0_pc = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Return))
        .unwrap();
    let mut m = Machine::new();
    assert_eq!(m.run_until(&lowered.bytecodes, 0, ret0_pc), Halt::Stopped);
    m.acc = 40;
    assert_eq!(m.run_at(&lowered.bytecodes, h_start), Halt::Return(41));
}
