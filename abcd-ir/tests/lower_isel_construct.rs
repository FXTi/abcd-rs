//! P3 regression (V3): construct calls round-trip as `newobjrange`, never
//! as a plain call form.
//!
//! Vendor facts:
//! - `newobjrange imm1:u16, imm2:u8, v:in:top` (abcd-isa-sys/vendor/isa/isa.yaml
//!   ~:535): imm1 is the IC slot (two_slot), imm2 the argument count
//!   INCLUDING the constructor, v the u8 START of the consecutive register
//!   window. `wide.newobjrange imm:u16, v:in:top` (~:540): u16 argc, STILL a
//!   u8 start, and NO IC slot operand — same wide-shape rule S2 established
//!   for the call range family.
//! - The constructor is the FIRST register of the range and argc counts it:
//!   `ctor = GET_VREG_VALUE(firstArgRegIdx)`, `firstArgIdx =
//!   firstArgRegIdx + 1`, `length = numArgs - 1`, and the slow path passes
//!   the ctor as BOTH func and newTarget — `SlowRuntimeStub::NewObjRange(
//!   thread, ctor, ctor, firstArgIdx, length)`
//!   (arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:4205,
//!   wide twin :4476). A plain call leaves NewTarget undefined, which is
//!   exactly the V3 failure ('ProxyConstructor: NewTarget is undefined',
//!   'class constructor cannot called without new').
//! - Corpus pandasm (exports/corpus/9.0.0.0/local/proxy/baseline/reference.pa:38):
//!   `newobjrange 0x5, 0x3, v6` — IC slot 0x5, argc 3 (ctor + 2 args),
//!   window start v6 with v6 = the Proxy constructor.

mod common;

use abcd_file::{FileType, FunctionKind, Version};
use abcd_ir::builder::IRBuilder;
use abcd_ir::entity::FuncId;
use abcd_ir::inst::{CallKind, InstData};
use abcd_ir::lower::lower_function;
use abcd_ir::module::Module;
use abcd_ir::opt::optimize_module;
use abcd_ir::types::IrType;
use abcd_ir::verify::verify_module;
use abcd_isa::{Bytecode, Reg};

use common::{Halt, Machine};

/// Build `f(ctor) { return new ctor(1000, 1001, ..., 1000+argc-1) }` with
/// one literal per argument.
fn build_construct(argc: usize) -> (Module, FuncId) {
    let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
    let func = IRBuilder::create_function(&mut module, "ctor", FunctionKind::Function, 1);
    let mut builder = IRBuilder::new(&mut module, func);
    let ctor = builder.create_func_param(0, IrType::default());
    let args: Vec<_> = (0..argc)
        .map(|i| {
            builder.emit_val(
                InstData::LiteralNumber(1000.0 + i as f64),
                IrType::default(),
            )
        })
        .collect();
    let call = builder.emit_val(
        InstData::Call {
            kind: CallKind::Construct,
            callee: ctor,
            args,
        },
        IrType::default(),
    );
    builder.emit_void(InstData::Return { value: Some(call) });
    (module, func)
}

/// Any plain-call form (the pre-fix mis-lowering of a construct site).
fn is_plain_call_form(bc: &Bytecode) -> bool {
    matches!(
        bc,
        Bytecode::Callarg0(..)
            | Bytecode::Callarg1(..)
            | Bytecode::Callargs2(..)
            | Bytecode::Callargs3(..)
            | Bytecode::Callrange(..)
            | Bytecode::WideCallrange(..)
            | Bytecode::Callthis0(..)
            | Bytecode::Callthis1(..)
            | Bytecode::Callthis2(..)
            | Bytecode::Callthis3(..)
            | Bytecode::Callthisrange(..)
            | Bytecode::WideCallthisrange(..)
    )
}

/// (a) Narrow: a 3-argument Construct lowers to `newobjrange` with
/// argc = 4 (the constructor counts) and the reserved window filled
/// [ctor, arg0, arg1, arg2] in order — never `callargs3` (which would
/// leave NewTarget undefined).
#[test]
fn construct_three_args_selects_newobjrange_with_ctor_first_window() {
    const CTOR: i64 = 4242;

    let (module, func) = build_construct(3);
    let result = lower_function(&module, func).expect("construct must lower");
    abcd_isa::encode(&result.bytecodes).expect("construct must encode");

    let (argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Newobjrange(_ic, argc, Reg(start)) => Some((argc.0, *start)),
            _ => None,
        })
        .expect("newobjrange must be emitted for a 3-arg construct");
    assert_eq!(
        argc, 4,
        "argc counts the constructor (vendor numArgs includes it)"
    );
    assert!(
        base <= 255,
        "the window start must fit the u8 start operand, got {base}"
    );
    assert!(
        !result.bytecodes.iter().any(is_plain_call_form),
        "a construct must never lower to a plain call form (bytecodes: {:?})",
        result.bytecodes
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::WideNewobjrange(..))),
        "argc+1 = 4 fits the narrow form"
    );

    // Simulate: the window Mov copies must place the constructor at window
    // slot 0 and argument j at window slot 1 + j, in order. The single
    // parameter (the constructor) arrives in the ABI top slot Reg(num_regs).
    let mut machine = Machine::new().with_reg(result.num_regs, CTOR);
    let halt = machine.run(&result.bytecodes);
    let Halt::NewObjRange { argc, start } = halt else {
        panic!(
            "expected execution to stop at newobjrange, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(argc, 4);
    assert_eq!(start, base);
    assert_eq!(
        machine.reg(start),
        CTOR,
        "window slot v{start} must hold the constructor (bytecodes: {:?})",
        result.bytecodes
    );
    for j in 0..3u16 {
        assert_eq!(
            machine.reg(start + 1 + j),
            1000 + j as i64,
            "window slot v{} must hold argument {j} (bytecodes: {:?})",
            start + 1 + j,
            result.bytecodes
        );
    }
}

/// (b) Wide: argc+1 > 255 cannot encode in the narrow u8 argc field — a
/// 300-argument Construct selects `wide.newobjrange 301, v<base>` with
/// base ≤ 255 and NO IC slot consumed (S2's wide-shape rule applies to
/// newobjrange too, isa.yaml ~:540).
#[test]
fn construct_beyond_255_args_selects_wide_newobjrange() {
    const ARGC: usize = 300;
    const CTOR: i64 = 777;

    let (module, func) = build_construct(ARGC);
    let result = lower_function(&module, func).expect("300-arg construct must lower");
    abcd_isa::encode(&result.bytecodes).expect("300-arg construct must encode");

    let (argc, base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::WideNewobjrange(argc, Reg(start)) => Some((argc.0, *start)),
            _ => None,
        })
        .expect("wide.newobjrange must be emitted for argc+1 > 255");
    assert_eq!(argc, ARGC as i64 + 1);
    assert!(
        base <= 255,
        "the wide form's start register is STILL u8, got {base}"
    );
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Newobjrange(..))),
        "the narrow newobjrange cannot encode argc+1 = {}",
        ARGC + 1
    );
    assert!(
        !result.bytecodes.iter().any(is_plain_call_form),
        "a construct must never lower to a plain call form (bytecodes: {:?})",
        result.bytecodes
    );

    let mut machine = Machine::new().with_reg(result.num_regs, CTOR);
    let halt = machine.run(&result.bytecodes);
    let Halt::WideNewObjRange { argc, start } = halt else {
        panic!(
            "expected execution to stop at wide.newobjrange, got {halt:?} (bytecodes: {:?})",
            result.bytecodes
        );
    };
    assert_eq!(argc, ARGC as i64 + 1);
    assert_eq!(start, base);
    assert_eq!(
        machine.reg(start),
        CTOR,
        "window slot v{start} must hold the constructor"
    );
    for j in 0..ARGC {
        assert_eq!(
            machine.reg(start + 1 + j as u16),
            1000 + j as i64,
            "window slot v{} must hold argument {j}",
            start + 1 + j as u16
        );
    }
}

/// (c) Boundary: argc+1 = 255 still fits the narrow u8 argc field — a
/// 254-argument Construct keeps `newobjrange` (with its IC slot).
#[test]
fn construct_at_u8_boundary_keeps_narrow_newobjrange() {
    let (module, func) = build_construct(254);
    let result = lower_function(&module, func).expect("254-arg construct must lower");
    abcd_isa::encode(&result.bytecodes).expect("254-arg construct must encode");

    let (argc, _base) = result
        .bytecodes
        .iter()
        .find_map(|bc| match bc {
            Bytecode::Newobjrange(_ic, argc, Reg(start)) => Some((argc.0, *start)),
            _ => None,
        })
        .expect("argc+1 = 255 must keep the narrow newobjrange");
    assert_eq!(argc, 255);
    assert!(
        !result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::WideNewobjrange(..))),
        "argc+1 = 255 fits the narrow form"
    );
}

/// (d) Optimizer treatment: a Construct call is side-effecting (DCE keeps
/// it even when the result is unused) and both the constructor and the
/// arguments are uses. The function must survive `optimize_module` +
/// `verify_module` with the Construct intact and still lower to
/// `newobjrange` afterwards.
#[test]
fn construct_survives_optimize_and_verify() {
    let (mut module, func) = build_construct(2);
    assert!(verify_module(&module).is_empty());

    optimize_module(&mut module);
    let errors = verify_module(&module);
    assert!(errors.is_empty(), "post-optimize verify: {errors:?}");

    let constructs: Vec<_> = module
        .func(func)
        .blocks
        .iter()
        .flat_map(|&bb| module.block(bb).insts.iter())
        .filter(|&&inst_id| {
            matches!(
                &module.inst(inst_id).data,
                InstData::Call {
                    kind: CallKind::Construct,
                    ..
                }
            )
        })
        .collect();
    assert_eq!(
        constructs.len(),
        1,
        "DCE must keep the side-effecting Construct call"
    );

    let result = lower_function(&module, func).expect("optimized construct must lower");
    assert!(
        result
            .bytecodes
            .iter()
            .any(|bc| matches!(bc, Bytecode::Newobjrange(..))),
        "the optimized construct still lowers to newobjrange (bytecodes: {:?})",
        result.bytecodes
    );
    assert!(
        !result.bytecodes.iter().any(is_plain_call_form),
        "the optimized construct must not lower to a plain call form (bytecodes: {:?})",
        result.bytecodes
    );
}
