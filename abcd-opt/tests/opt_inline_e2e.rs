//! D2 inline rewrite — end-to-end tests: real bytecode files →
//! `abcd_lift::lift_file` → `abcd_opt::inline::inline_module` →
//! `abcd_ir2::verify_module` → `abcd_lower::lower_function` → the
//! deterministic simulator, with the inline-OFF run as the behavioral
//! oracle (inlining must not change observable behavior).

mod common;

use abcd_file::{AccessFlags, Builder, CatchBlockDef, File, Type};
use abcd_ir2::verify_module;
use abcd_ir2::{FuncId, Module};
use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg, encode as encode_bytecodes};
use abcd_lift::lift_file;
use abcd_lower::lower_function;
use abcd_opt::inline::{InlinePolicy, inline_module};

use common::{Halt, Machine};

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(|i| FuncId::new(i as u32))
        .find(|&f| {
            module
                .func(f)
                .is_some_and(|d| module.sym.resolve(d.name) == Some(name))
        })
        .unwrap_or_else(|| panic!("function {name}"))
}

/// Build a file with two static methods on the global class, in the
/// es2abc frame convention (vendored MethodLiteral: no
/// L_ESCallTypeAnnotation → 0xF → three implicit leading arg slots
/// [func, new.target, this]; the formal is a3):
///
/// ```text
/// g(x):  ldai 1; add2 imm, v3; return        // return x + 1
/// f():   ldai 41; sta v0; definefunc g;      // v0 = 41
///        callarg1 imm, v0; return            // return g(41)
/// ```
fn build_call_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto_void = builder.create_proto(Type::Void, &[]);
    let proto_int = builder.create_proto(Type::Void, &[Type::I32]);

    let (g_code, _) = encode_bytecodes(&[
        Bytecode::Ldai(Imm(1)),
        Bytecode::Add2(Imm(0), Reg(3)),
        Bytecode::Return,
    ])
    .unwrap();
    let g = builder.class_add_method(class, "g", proto_int, AccessFlags::STATIC, &g_code, 0, 4);

    let placeholder = EntityId(u16::MAX as u32);
    let (f_code, f_offsets) = encode_bytecodes(&[
        Bytecode::Ldai(Imm(41)),
        Bytecode::Sta(Reg(0)),
        Bytecode::Definefunc(Imm(0), placeholder, Imm(1)),
        Bytecode::Callarg1(Imm(0), Reg(0)),
        Bytecode::Return,
    ])
    .unwrap();
    let f = builder.class_add_method(class, "f", proto_void, AccessFlags::STATIC, &f_code, 1, 3);
    builder
        .relocate_code_id(f, f_offsets[2], 0, abcd_file::CodeEntity::Method(g))
        .unwrap();
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// E2E: the inlined program behaves identically to the non-inlined one,
/// and the call instruction is actually gone from the lowered output
/// (the pass fired end to end). The simulator is record-and-inspect at
/// calls, so the oracle executes the call MANUALLY: run f to its call
/// record, run g with the recorded argument, and compose the result.
#[test]
fn lift_inline_verify_lower_simulate_preserves_behavior() {
    let file = build_call_file();

    // Oracle: inline OFF. f halts at the call record with v0 = 41.
    let module = lift_file(&file).expect("lifts");
    let f = func_by_name(&module, "f");
    let g = func_by_name(&module, "g");
    let f_oracle = lower_function(&module, f).expect("oracle f lowers");
    let g_oracle = lower_function(&module, g).expect("oracle g lowers");
    let mut machine = Machine::new();
    let call = machine.run(&f_oracle.bytecodes);
    let Halt::CallRange { argc: 1, start } = call else {
        panic!("inline-off f must halt at its call record: {call:?}")
    };
    let arg = machine.reg(start);
    assert_eq!(arg, 41, "the call argument is 41");
    // The ABI: arguments live ABOVE the declared frame (v[num_regs +
    // arg_index]); g's sole formal is a3 (three implicit slots lead).
    let arg_slot = g_oracle.num_regs + 3;
    let mut callee_machine = Machine::new().with_reg(arg_slot, arg);
    let oracle_result = callee_machine.run(&g_oracle.bytecodes);
    assert_eq!(oracle_result, Halt::Return(42), "g(41) = 42");

    // Inline ON.
    let mut module = lift_file(&file).expect("lifts");
    let pre = verify_module(&module);
    assert!(pre.is_ok(), "lifted module verifies: {:?}", pre.errors);
    let report = inline_module(&mut module, &InlinePolicy::default());
    assert_eq!(report.sites_inlined, 1, "the call site fires: {report:?}");
    let post = verify_module(&module);
    assert!(
        post.is_ok(),
        "inlined module verifies (hard gate): {:?}",
        post.errors
    );

    let f = func_by_name(&module, "f");
    let inlined = lower_function(&module, f).expect("inlined lowers");
    let mut machine = Machine::new();
    let halt = machine.run(&inlined.bytecodes);
    assert_eq!(halt, oracle_result, "behavior is preserved");

    // The pass fired end to end: no call instruction remains in f's
    // lowered stream, and the callee's add2 is present inline.
    assert!(
        !inlined
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Callarg1(..) | Bytecode::Callrange(..))),
        "the call is gone after inlining: {:?}",
        inlined.bytecodes
    );
    assert!(
        inlined
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Add2(..))),
        "the callee body is spliced in: {:?}",
        inlined.bytecodes
    );
}

/// Build a file whose `f` calls `g` INSIDE a try region:
///
/// ```text
/// g():  ldai 42; return
/// f():  definefunc g; callarg0; jmp end   <- try [0..3)
///       ldai 777; return                  <- catch-all handler [3..5)
/// end:  return                            <- 5 (jmp target)
/// ```
fn build_try_call_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);

    let (g_code, _) = encode_bytecodes(&[Bytecode::Ldai(Imm(42)), Bytecode::Return]).unwrap();
    let g = builder.class_add_method(class, "g", proto, AccessFlags::STATIC, &g_code, 0, 3);

    let placeholder = EntityId(u16::MAX as u32);
    let (f_code, f_offsets) = encode_bytecodes(&[
        Bytecode::Definefunc(Imm(0), placeholder, Imm(0)), // 0
        Bytecode::Callarg0(Imm(0)),                        // 1
        Bytecode::Jmp(Label(5)),                           // 2
        Bytecode::Ldai(Imm(777)),                          // 3 (handler)
        Bytecode::Return,                                  // 4 (handler ret)
        Bytecode::Return,                                  // 5 (normal end)
    ])
    .unwrap();
    let f = builder.class_add_method(class, "f", proto, AccessFlags::STATIC, &f_code, 0, 3);
    builder
        .relocate_code_id(f, f_offsets[0], 0, abcd_file::CodeEntity::Method(g))
        .unwrap();
    let code = builder.create_code(&f_code, 0, 0);
    builder.code_add_try_block(
        code,
        f_offsets[0],
        f_offsets[3] - f_offsets[0],
        &[CatchBlockDef {
            type_class: None,
            handler_pc: f_offsets[3],
            code_size: f_offsets[5] - f_offsets[3],
        }],
    );
    builder.method_set_code(f, code);
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// E2E exception semantics: with the call site inside a try region, the
/// inlined body's instructions must still dispatch to the handler (the
/// module-docs exception-edge rule, observable at the VM-dispatch
/// level): the reconstructed try range covers the inlined `ldai 42`,
/// and simulating an exception at that point reaches the handler.
#[test]
fn inline_inside_try_keeps_exception_dispatch() {
    let file = build_try_call_file();
    let mut module = lift_file(&file).expect("lifts");
    let report = inline_module(&mut module, &InlinePolicy::default());
    assert_eq!(report.sites_inlined, 1, "the call site fires: {report:?}");
    let post = verify_module(&module);
    assert!(
        post.is_ok(),
        "inlined module verifies (hard gate): {:?}",
        post.errors
    );

    let f = func_by_name(&module, "f");
    let lowered = lower_function(&module, f).expect("inlined try function lowers");

    // Normal path: f() = g() = 42.
    let mut machine = Machine::new();
    let halt = machine.run(&lowered.bytecodes);
    assert_eq!(halt, Halt::Return(42), "normal path preserved");

    // The inlined `ldai 42` lies inside the reconstructed try range —
    // exactly the VM's PC-range containment test (FindCatchBlock).
    let inlined_ldai = lowered
        .bytecodes
        .iter()
        .position(|bc| matches!(bc, Bytecode::Ldai(Imm(v)) if *v == 42))
        .expect("the callee body is inlined");
    assert!(
        lowered.try_blocks.iter().any(|tb| {
            (tb.start as usize) <= inlined_ldai && inlined_ldai < (tb.start + tb.len) as usize
        }),
        "the inlined body is covered by the try range: pc={inlined_ldai}, tries={:?}",
        lowered.try_blocks
    );

    // Exception at the inlined instruction: dispatch reaches the
    // handler, which returns 777.
    let handler_pc = lowered.try_blocks[0].catches[0].handler as usize;
    let mut machine = Machine::new();
    let stopped = machine.run_until(&lowered.bytecodes, 0, inlined_ldai);
    assert_eq!(stopped, Halt::Stopped);
    let halted = machine.run_at(&lowered.bytecodes, handler_pc);
    assert_eq!(halted, Halt::Return(777), "exception dispatch preserved");
}
