//! Optimization pass infrastructure and pipeline.

pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use crate::entity::FuncId;
use crate::module::Module;

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
/// Pipeline: peephole → sccp → dce → copyprop → peephole → dce
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

/// Run the optimization pipeline on all functions in the module.
pub fn optimize_module(module: &mut Module) -> bool {
    let func_count = module.functions.len();
    let mut changed = false;
    for i in 0..func_count {
        let func_id = FuncId::from_index(i);
        if module.func(func_id).blocks.is_empty() {
            continue;
        }
        changed |= optimize_func(module, func_id);
    }
    changed
}
