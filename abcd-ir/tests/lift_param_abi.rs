//! Parameter ABI regressions (Phase 2.2, B5 + entry seeding + copy-in
//! prologue).
//!
//! Frame convention (vendor static_core/runtime/include/method.h): the
//! runtime frame is `num_vregs + num_args` registers; arguments arrive in
//! the TOP slots `v[num_vregs + i]`. Lowering keeps parameter values in
//! vreg homes at the bottom of the frame and emits a copy-in prologue
//! (`mov home_i, v[num_regs + i]`) at the start of the entry block, so
//! `to_method_body`'s `num_vregs = num_regs` / `num_args = param_count`
//! split is exact.
//!
//! B5: on 12.0.x+ files protos carry no shorty (format fact #A7), so
//! `method.arg_types` is empty even when the decoded code header declares
//! `num_args > 0`. Lift must seed `param_count` from the code header's
//! `num_args`, not from `arg_types.len()`.

mod common;

use std::collections::HashMap;

use abcd_file::{AccessFlags, Builder, File, FileType, FunctionKind, Type, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::{FuncId, StringId};
use abcd_ir::inst::InstData;
use abcd_ir::lift::lift_file;
use abcd_ir::lower::regalloc::{self, RegAlloc, RegSlot};
use abcd_ir::lower::{isel, lower_function, to_method_body};
use abcd_ir::module::Module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, EntityId, Reg, encode as encode_bytecodes};

use common::{Halt, Machine};

const SENTINEL: i64 = 4242;

/// Build a 12.x file whose global class carries one static method
/// `identity` with the given code-header frame, whose body is
/// `lda v[num_vregs] (arg0); return`. On 12.x the proto carries no shorty
/// (#A7), so `arg_types` decodes empty while `num_args` is real.
fn build_12x_identity_file(num_vregs: u32, num_args: u32) -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) =
        encode_bytecodes(&[Bytecode::Lda(Reg(num_vregs as u16)), Bytecode::Return]).unwrap();
    builder.class_add_method(
        class,
        "identity",
        proto,
        AccessFlags::STATIC,
        &code,
        num_vregs,
        num_args,
    );
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

/// Build a 12.x file with two one-argument identity methods (`first`,
/// `second`) in the global class: `lda v1 (arg0); return` each.
fn build_12x_two_function_file() -> File {
    let mut builder = Builder::new();
    builder.set_api(12, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::Void, &[]);
    let (code, _) = encode_bytecodes(&[Bytecode::Lda(Reg(1)), Bytecode::Return]).unwrap();
    for name in ["first", "second"] {
        builder.class_add_method(class, name, proto, AccessFlags::STATIC, &code, 1, 1);
    }
    builder.deduplicate();
    abcd_file::decode(&builder.finalize().unwrap()).unwrap()
}

fn method_by_name<'a>(file: &'a File, name: &str) -> &'a abcd_file::Method {
    file.all_methods()
        .find(|(_, m)| file.strings.resolve(m.name) == Some(name))
        .unwrap_or_else(|| panic!("method {name}"))
        .1
}

fn func_by_name(module: &Module, name: &str) -> FuncId {
    (0..module.functions.len())
        .map(FuncId::from_index)
        .find(|&f| module.strings.get(module.func(f).name) == name)
        .unwrap_or_else(|| panic!("function {name}"))
}

/// B5: on 12.x, `param_count` must come from the code header's `num_args`
/// (3), not from the empty `arg_types` (0). A lowered frame that declares
/// `num_args = 0` while callers push 3 arguments crashes the VM.
#[test]
fn b5_param_count_comes_from_code_header_on_12x() {
    let file = build_12x_identity_file(2, 3);
    let method = method_by_name(&file, "identity");
    assert_eq!(method.body.as_ref().unwrap().num_args, 3);
    assert!(
        method.arg_types.is_empty(),
        "12.x protos carry no shorty (#A7): arg_types must decode empty"
    );

    let module = lift_file(&file).expect("lift");
    let func_id = func_by_name(&module, "identity");
    assert_eq!(
        module.func(func_id).param_count,
        3,
        "param_count must be seeded from the code header num_args"
    );
    assert!(
        module.func(func_id).param_types.is_empty(),
        "param_types stay advisory: empty on 12.x, shorter than param_count"
    );
}

/// Regression: on 9.x files the proto shorty is present and
/// `arg_types.len() == num_args`; seeding from the code header must keep
/// that behavior identical.
#[test]
fn param_count_matches_shorty_on_9x() {
    let mut builder = Builder::new();
    builder.set_api(9, "");
    let class = builder.add_global_class();
    let proto = builder.create_proto(Type::F64, &[Type::F64, Type::F64, Type::F64]);
    let (code, _) = encode_bytecodes(&[Bytecode::Lda(Reg(2)), Bytecode::Return]).unwrap();
    builder.class_add_method(class, "identity", proto, AccessFlags::STATIC, &code, 2, 3);
    builder.deduplicate();
    let file = abcd_file::decode(&builder.finalize().unwrap()).unwrap();

    let method = method_by_name(&file, "identity");
    assert_eq!(method.body.as_ref().unwrap().num_args, 3);
    assert_eq!(
        method.arg_types.len(),
        3,
        "9.x protos carry a shorty: arg_types must decode"
    );

    let module = lift_file(&file).expect("lift");
    let func_id = func_by_name(&module, "identity");
    assert_eq!(module.func(func_id).param_count, 3);
    assert_eq!(module.func(func_id).param_types.len(), 3);
}

/// End-to-end: a bytecode read of an arg-slot register must resolve to the
/// ABI argument. Decode → lift → lower → `to_method_body`, then simulate
/// the lowered bytecodes on a frame laid out by the vendor ABI
/// (`regs[num_vregs + i]` hold the arguments at entry).
#[test]
fn arg_slot_read_returns_the_abi_argument_end_to_end() {
    let file = build_12x_identity_file(2, 3);
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_empty());
    let func_id = func_by_name(&module, "identity");

    let result = lower_function(&module, func_id).expect("lower");
    let body = to_method_body(&module, func_id, &result, &file).expect("method body");
    assert_eq!(body.num_args, 3, "lowered frame must declare the args");
    assert_eq!(body.num_vregs, u32::from(result.num_regs));

    // Copy-in prologue: the first num_args bytecodes move the ABI top
    // slots into the parameter homes at the bottom of the frame.
    for (i, bc) in body.bytecodes.iter().take(3).enumerate() {
        let Bytecode::Mov(dst, src) = bc else {
            panic!("bytecode {i} must be a copy-in Mov, got {bc:?}");
        };
        let _ = dst;
        assert_eq!(
            src.0 as u32,
            u32::from(result.num_regs) + i as u32,
            "copy-in must read the ABI top slot v[num_regs + {i}]"
        );
    }

    // ABI frame: the argument sits at regs[num_vregs + 0].
    let mut machine = Machine::new().with_reg(result.num_regs, SENTINEL);
    let halt = machine.run(&body.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(SENTINEL),
        "lda of the arg0 slot must return the caller's argument (bytecodes: {:?})",
        body.bytecodes
    );
}

/// Parameter values belong to their function: in a multi-function module
/// the second function's parameter is NOT `Value::from_index(0)`. Register
/// allocation and the copy-in prologue must key on the function's own
/// parameter values, not on arena indices.
#[test]
fn second_function_params_lower_with_their_own_homes() {
    let file = build_12x_two_function_file();
    let module = lift_file(&file).expect("lift");
    assert!(verify_module(&module).is_empty());
    let second = func_by_name(&module, "second");
    let first = func_by_name(&module, "first");
    assert_ne!(second, first);
    assert_eq!(module.func(second).param_count, 1);

    let result = lower_function(&module, second).expect("lower second");
    let body = to_method_body(&module, second, &result, &file).expect("method body");
    assert_eq!(body.num_args, 1);

    let mut machine = Machine::new().with_reg(result.num_regs, SENTINEL);
    let halt = machine.run(&body.bytecodes);
    assert_eq!(
        halt,
        Halt::Return(SENTINEL),
        "the second function's arg0 must come from its own parameter value \
         (bytecodes: {:?})",
        body.bytecodes
    );
}

/// The copy-in prologue copies from an ABI slot into a register home; a
/// parameter colored `Acc` (possible only with a hand-crafted allocation —
/// `mcs_color` pre-assigns parameters to registers) has no register home
/// and must be a hard error, never a silent path.
#[test]
fn acc_colored_param_is_a_hard_lower_error() {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "f", FunctionKind::Function, 1);
    let p;
    {
        let mut builder = IRBuilder::new(&mut module, func);
        p = builder.create_func_param(0, IrType::default());
        builder.emit_void(InstData::Return { value: Some(p) });
    }

    let alloc = RegAlloc {
        allocation: HashMap::from([(p, RegSlot::Acc)]),
        phi_copies: HashMap::new(),
        num_regs: 1,
        copy_temp: None,
        spill_slot: Some(RegSlot::Reg(1)),
    };
    let rpo = regalloc::compute_rpo(&module, func);
    let string_map: HashMap<StringId, EntityId> = HashMap::new();
    let err = isel::select(&module, func, &alloc, &rpo, &string_map)
        .expect_err("an Acc-colored parameter must be a hard LowerError");
    assert!(
        matches!(
            err,
            abcd_ir::lower::LowerError::AccColoredParam { value, .. } if value == p
        ),
        "expected AccColoredParam, got {err:?}"
    );
}
