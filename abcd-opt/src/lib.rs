//! # abcd-opt — optimization passes for the SSA IR (`abcd-ir`)
//!
//! Format-independent optimization pipeline over [`abcd_ir::Module`]:
//! [`peephole`] (local constant folding), [`sccp`] (sparse conditional
//! constant propagation), [`dce`] (effects-driven aggressive dead code
//! elimination + CFG simplification), and [`copyprop`] (trivial-phi and copy
//! elimination). [`inline`] provides a guarded single-callee SSA function
//! inliner on an **opt-in** basis (never run by [`optimize_module`], preserving
//! function boundaries for callers such as `abcd-decompile`).
//!
//! ## Format independence (structurally enforced)
//!
//! Every pass operates on [`abcd_ir::Module`] alone (`design/ir.md`). This
//! crate's `Cargo.toml` `[dependencies]` list **only** `abcd-ir` — never
//! `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`, or
//! `abcd-lower`.
//!
//! ## ECMAScript & exception soundness invariants (`design/decisions.md`)
//!
//! - **Operand evaluation order**: both fold engines evaluate non-commutative
//!   binary/comparison operators in ArkCompiler's operand order (`vreg OP acc`,
//!   encoded on IR instructions as `right OP left`).
//! - **Signed zero & IEEE-754 identity**: folds preserve `-0.0` bit-exactly via
//!   [`Const::Number`](abcd_ir::Const); `StrictEq` compares numbers with IEEE
//!   `==` (`0 === -0` is `true`, `NaN !== NaN`), while canonical `NaN` / `±∞`
//!   values lower back to dedicated `ldnan` / `ldinfinity` opcodes.
//! - **Abstract equality & coercion**: `Eq`/`NotEq` and arithmetic folds never
//!   mis-coerce `null` or `undefined` to `0.0`.
//! - **Unary & bitwise semantics**: `UnOp::BitNot` performs 32-bit bitwise NOT
//!   whereas `UnOp::LogicalNot` performs boolean negation; bitwise and shift
//!   folds apply ECMA-262 `ToInt32` / `ToUint32` (wrapping modulo 2^32,
//!   mapping `NaN`/`±Infinity` to `+0`), never Rust's saturating float casts.
//! - **SCCP exception soundness**: reachability traverses
//!   [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) edges (including blocks
//!   ending in `Return`/`Unreachable`), and [`ValueDef::ExceptionParam`](abcd_ir::ValueDef)
//!   plus handler-block phis evaluate to lattice `Bottom`.
//! - **Effects-derived ADCE**: instruction essentiality is derived solely from
//!   [`Op::effects_in`](abcd_ir::Op::effects_in) and
//!   [`Effects::is_removable_if_unused`](abcd_ir::Effects::is_removable_if_unused)
//!   (`T3` / `R2-D2` contract), preserving untyped coercing operations and
//!   global stores while sweeping proven-pure instructions, pure reads/allocs,
//!   and dead `FunctionData::frame_init_consts` — keeping
//!   [`abcd_ir::verify_module`] clean after every pass.
//!
//! ## Library rule
//!
//! No panics on data: arena lookups return `Option`; passes skip what
//! they cannot soundly rewrite.

#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod analysis;
pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use abcd_ir::{FuncId, Module};

/// A function-level optimization pass.
pub trait FuncPass {
    /// Run the pass on `func` within `module`.
    /// Returns `true` if the IR was modified.
    fn run(&self, module: &mut Module, func: FuncId) -> bool;
}

/// ECMA-262 ToInt32, shared by BOTH constant-fold engines (N42).
///
/// Rust's `n as i32` SATURATES (out-of-range clamps to ±2^31, NaN → 0);
/// JS bitwise/shift operators WRAP mod 2^32 and map NaN/±Infinity to +0.
/// Matches the vendored conversion used by every `*2` bitwise/shift fast
/// path, `base::NumberHelper::DoubleToInt(d, INT32_BITS)`
/// (arkcompiler_ets_runtime-master ecmascript/base/number_helper.cpp:1137-
/// 1158 — truncate toward zero, keep the low 32 bits, reinterpret as
/// signed; the explicit `SaturateTruncDoubleToInt32` is a different
/// function those handlers do NOT call).
pub(crate) fn to_int32(n: f64) -> i32 {
    if !n.is_finite() || n == 0.0 {
        return 0;
    }
    // Exact: f64 `%` is fmod (exactly rounded) and every integer in
    // [0, 2^32) is exactly representable, so the wrap loses nothing.
    let wrapped = n.trunc() % 4294967296.0;
    let positive = if wrapped < 0.0 {
        wrapped + 4294967296.0
    } else {
        wrapped
    };
    (positive as u32) as i32
}

/// ECMA-262 ToUint32 — the same wrap, reinterpreted unsigned. The shift
/// count mask `& 0x1f` applies AFTER this conversion: a negative count
/// wraps to a large unsigned value and then masks (e.g. -1 → 31), it is
/// not saturated to 0 first.
pub(crate) fn to_uint32(n: f64) -> u32 {
    to_int32(n) as u32
}

/// Run the full optimization pipeline on a single function.
/// Pipeline: peephole → sccp → adce + cfg-simplify → copyprop → peephole
/// → adce + cfg-simplify.
/// Returns `true` if any pass modified the IR.
pub fn optimize_func(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;

    // Round 1: peephole → sccp → adce + cfg simplify → copyprop
    changed |= peephole::Peephole.run(module, func);
    changed |= sccp::Sccp.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    changed |= copyprop::CopyProp.run(module, func);

    // Round 2: peephole → adce + cfg simplify (cleanup)
    changed |= peephole::Peephole.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);

    changed
}

/// Run the optimization pipeline on all functions in the module. Bodyless
/// functions (external/native declarations) are skipped.
pub fn optimize_module(module: &mut Module) -> bool {
    let func_count = module.functions.len();
    let mut changed = false;
    for i in 0..func_count {
        let func_id = FuncId::new(i as u32);
        let Some(func) = module.func(func_id) else {
            continue;
        };
        if func.blocks.is_empty() {
            continue;
        }
        changed |= optimize_func(module, func_id);
    }
    changed
}
