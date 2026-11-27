//! Wave 2 integration tests (`#49`, `#71`, `#72`, `#84` Part 2b):
//! 1. `decode_lazy` (`MethodCode::Span`) -> `lift_file` produces
//!    `modules_structurally_eq == Ok(())` vs `decode` (`MethodCode::Decoded`).
//! 2. Multi-class production-threshold parallel `lift_file_with_options` across
//!    `1`, `2`, and `4` Rayon threads (`256 KiB` worker stacks) matches
//!    `parallel: false` bit-for-bit (`modules_structurally_eq == Ok(())`) and
//!    preserves lowest-method `LiftError` determinism.
//! 3. `LiftOptions { retain_tail_capacity: true, .. }` preserves structural
//!    equivalence while retaining pre-reserved arena tail capacity.

use std::sync::Arc;

use abcd_file::{
    AccessFlags, Builder, CatchBlockDef, CodeEntity, MethodCode, Type, decode, decode_lazy,
};
use abcd_ir::{modules_structurally_eq, verify_module};
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::{LiftError, LiftOptions, lift_file, lift_file_with_options};

const PLACEHOLDER: EntityId = EntityId(u16::MAX as u32);

/// Build a multi-class `.abc` container exceeding the production parallel
/// threshold (`>= 32` methods and `>= 1,024` bytecodes), exercising shared
/// literal arrays, foreign catch descriptors, branching/SSA phis, lone-surrogate
/// strings, and cross-method `Definefunc` references.
fn build_large_multiclass_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let proto = b.create_proto(Type::Void, &[]);

    let shared_lit = b.add_literal_array("shared_arr");
    let lit_s0 = b.add_string("shared_item_0");
    let lit_s1 = b.add_string("shared_item_1");
    b.literal_array_add_string(shared_lit, lit_s0);
    b.literal_array_add_string(shared_lit, lit_s1);
    b.literal_array_add_integer(shared_lit, 77);

    let foreign_err_a = b.add_foreign_class("Lext/ErrorA;");
    let foreign_err_b = b.add_foreign_class("Lext/ErrorB;");

    for cls_idx in 0..4u32 {
        let cls = b.add_class(&format!("Lpkg/Mod{cls_idx};"));
        for m_idx in 0..10u32 {
            let global_ord = (cls_idx * 10 + m_idx) as i64;
            let prop_str = b.add_string(&format!("prop_{cls_idx}_{m_idx}"));
            let mut body_insns = Vec::with_capacity(36);
            body_insns.push(Bytecode::Createarraywithbuffer(Imm(0), PLACEHOLDER)); // 0 (lit)
            body_insns.push(Bytecode::Sta(Reg(0))); // 1
            body_insns.push(Bytecode::Lda(Reg(4))); // 2 (arg0)
            body_insns.push(Bytecode::Jeqz(Label(8))); // 3 -> else at 8
            body_insns.push(Bytecode::Ldai(Imm(global_ord))); // 4
            body_insns.push(Bytecode::Ldobjbyname(Imm(0), PLACEHOLDER)); // 5 (str)
            body_insns.push(Bytecode::Sta(Reg(1))); // 6
            body_insns.push(Bytecode::Jmp(Label(11))); // 7 -> join at 11
            body_insns.push(Bytecode::Ldai(Imm(global_ord + 100))); // 8
            body_insns.push(Bytecode::Add2(Imm(1), Reg(0))); // 9
            body_insns.push(Bytecode::Sta(Reg(1))); // 10
            // Pad arithmetic chain so total bytecodes across 40 methods > 1,280.
            for step in 0..18i64 {
                body_insns.push(Bytecode::Lda(Reg(1)));
                body_insns.push(Bytecode::Ldai(Imm(step)));
                body_insns.push(Bytecode::Add2(Imm(2), Reg(1)));
                body_insns.push(Bytecode::Sta(Reg(1)));
            }
            let catch_pc_idx = body_insns.len() + 2;
            body_insns.push(Bytecode::Lda(Reg(1)));
            body_insns.push(Bytecode::Return);
            body_insns.push(Bytecode::Sta(Reg(2))); // catch handler
            body_insns.push(Bytecode::Lda(Reg(2)));
            body_insns.push(Bytecode::Return);

            let (encoded, offsets) = encode_bytecodes(&body_insns).unwrap();
            let code_h = b.create_code(&encoded, 4, 5);
            let catch_type = if (cls_idx + m_idx) % 2 == 0 {
                Some(foreign_err_a)
            } else {
                Some(foreign_err_b)
            };
            let handler_off = offsets[catch_pc_idx];
            b.code_add_try_block(
                code_h,
                offsets[0],
                offsets[catch_pc_idx - 2] - offsets[0],
                &[CatchBlockDef {
                    type_class: catch_type,
                    handler_pc: handler_off,
                    code_size: encoded.len() as u32 - handler_off,
                }],
            );
            let mh = b.class_add_method(
                cls,
                &format!("m_{m_idx}"),
                proto,
                AccessFlags::PUBLIC | AccessFlags::STATIC,
                &[],
                0,
                0,
            );
            b.method_set_code(mh, code_h);
            b.relocate_code_id(mh, offsets[0], 0, CodeEntity::LiteralArray(shared_lit))
                .unwrap();
            b.relocate_code_id(mh, offsets[5], 0, CodeEntity::String(prop_str))
                .unwrap();
        }
    }

    b.finalize().unwrap()
}

#[test]
fn lazy_span_and_parallel_options_produce_structurally_identical_modules() {
    let abc_bytes: Arc<[u8]> = build_large_multiclass_abc().into();
    let eager_file = decode(&abc_bytes).expect("eager decode");
    let lazy_file = decode_lazy(Arc::clone(&abc_bytes)).expect("lazy decode");

    let total_methods: usize = lazy_file.classes.values().map(|c| c.methods.len()).sum();
    let total_insns: usize = lazy_file
        .all_methods()
        .filter_map(|(_, m)| m.body.as_ref())
        .map(abcd_file::MethodBody::insn_count)
        .sum();
    assert_eq!(total_methods, 40);
    assert!(
        total_insns >= 1_024,
        "fixture must exceed production parallel threshold (got {total_insns})"
    );
    assert!(
        lazy_file
            .all_methods()
            .all(|(_, m)| matches!(m.body.as_ref().map(|b| &b.code), Some(MethodCode::Span(_))))
    );

    let seq_eager = lift_file_with_options(
        &eager_file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect("sequential eager lift");
    assert!(verify_module(&seq_eager).errors.is_empty());

    let default_lazy = lift_file(&lazy_file).expect("default lift on lazy spans");
    assert!(verify_module(&default_lazy).errors.is_empty());
    assert_eq!(modules_structurally_eq(&seq_eager, &default_lazy), Ok(()));

    for threads in [1usize, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(256 * 1024)
            .build()
            .unwrap();
        let par_lazy = pool
            .install(|| {
                lift_file_with_options(
                    &lazy_file,
                    &LiftOptions {
                        retain_tail_capacity: false,
                        parallel: true,
                    },
                )
            })
            .expect("parallel lazy lift");
        assert!(verify_module(&par_lazy).errors.is_empty());
        assert_eq!(
            modules_structurally_eq(&seq_eager, &par_lazy),
            Ok(()),
            "parallel lazy lift diverged at {threads} Rayon threads"
        );
    }
}

#[test]
fn retain_tail_capacity_preserves_ir_equivalence_and_arena_headroom() {
    let abc_bytes: Arc<[u8]> = build_large_multiclass_abc().into();
    let lazy_file = decode_lazy(abc_bytes).expect("lazy decode");

    let shrunk = lift_file(&lazy_file).expect("default shrunk lift");
    assert_eq!(shrunk.blocks.capacity(), shrunk.blocks.len());
    assert_eq!(shrunk.insts.capacity(), shrunk.insts.len());
    assert_eq!(shrunk.values.capacity(), shrunk.values.len());

    for parallel in [false, true] {
        let retained = lift_file_with_options(
            &lazy_file,
            &LiftOptions {
                retain_tail_capacity: true,
                parallel,
            },
        )
        .expect("retain_tail_capacity lift");
        assert!(verify_module(&retained).errors.is_empty());
        assert_eq!(
            modules_structurally_eq(&shrunk, &retained),
            Ok(()),
            "retain_tail_capacity (parallel={parallel}) must be 100% structurally identical"
        );
        assert!(retained.classes.capacity() > retained.classes.len());
        assert!(retained.functions.capacity() > retained.functions.len());
        assert!(retained.blocks.capacity() > retained.blocks.len());
        assert!(retained.insts.capacity() > retained.insts.len());
        assert!(retained.values.capacity() > retained.values.len());
    }
}

#[test]
fn parallel_lift_with_options_preserves_lowest_method_error_above_threshold() {
    let abc_bytes = build_large_multiclass_abc();
    let mut file = decode(&abc_bytes).expect("decode");

    let keys: Vec<_> = file
        .classes
        .iter()
        .filter(|(_, c)| !c.methods.is_empty())
        .map(|(&k, _)| k)
        .collect();
    // Corrupt non-external class 1 method 2 (global index 12 -> ParamCountOverflow)
    // and class 3 method 5 (global index 35 -> EmptyBytecode).
    file.classes.get_mut(&keys[1]).unwrap().methods[2]
        .body
        .as_mut()
        .unwrap()
        .num_args = u32::from(u16::MAX) + 7;
    file.classes.get_mut(&keys[3]).unwrap().methods[5]
        .body
        .as_mut()
        .unwrap()
        .code = MethodCode::Decoded(Vec::new());

    let want = u32::from(u16::MAX) + 7;
    let seq_err = lift_file_with_options(
        &file,
        &LiftOptions {
            retain_tail_capacity: false,
            parallel: false,
        },
    )
    .expect_err("sequential error");
    assert!(matches!(seq_err, LiftError::ParamCountOverflow(n) if n == want));

    for threads in [1usize, 2, 4] {
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .stack_size(256 * 1024)
            .build()
            .unwrap();
        let par_err = pool
            .install(|| {
                lift_file_with_options(
                    &file,
                    &LiftOptions {
                        retain_tail_capacity: false,
                        parallel: true,
                    },
                )
            })
            .expect_err("parallel error");
        assert!(
            matches!(par_err, LiftError::ParamCountOverflow(n) if n == want),
            "threads={threads}: got {par_err:?}"
        );
    }
}
