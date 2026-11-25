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
//! crate's `Cargo.toml` `[dependencies]` list **only** `abcd-ir` and pure-Rust
//! zero-dep `libm` (for cross-platform deterministic IEEE-754 math) — never
//! `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`, or
//! `abcd-lower`.
//!
//! ## ECMAScript & exception soundness invariants (`design/decisions.md`)
//!
//! - **Operand evaluation order**: both fold engines evaluate non-commutative
//!   binary/comparison operators in ArkCompiler's operand order (`vreg OP acc`,
//!   encoded on IR instructions as `right OP left`).
//! - **Signed zero, canonical `NaN`, & ECMA-262 `**`**: folds preserve `-0.0`
//!   bit-exactly via [`Const::Number`] while canonicalizing
//!   computed `NaN` values to `0x7ff8_0000_0000_0000` (`#60`) and evaluating
//!   exponentiation per ECMA-262 `Number::exponentiate` over `libm::pow`
//!   (`R3-H6`). `Sccp`'s lattice meet compares numbers bitwise (`+0.0` and
//!   `-0.0` meet to `Bottom`, `R3-H5`), whereas `StrictEq` compares numbers
//!   with IEEE `==` (`0 === -0` is `true`, `NaN !== NaN`).
//! - **Abstract equality & coercion**: `Eq`/`NotEq` and arithmetic folds never
//!   mis-coerce `null` or `undefined` to `0.0`, and instructions carrying
//!   [`Ty::Static`] skip dynamic JS `f64` folding (`R3-A11`).
//! - **Unary, `jeqz`/`jnez`, & bitwise semantics**: `UnOp::BitNot` performs
//!   32-bit bitwise NOT, `UnOp::LogicalNot` performs boolean negation, and
//!   [`UnOp::JumpEqz`](abcd_ir::UnOp::JumpEqz) /
//!   [`UnOp::JumpNez`](abcd_ir::UnOp::JumpNez) match ArkCompiler's exact raw
//!   branch predicates (`R3-X1`); bitwise and shift folds apply ECMA-262
//!   `ToInt32` / `ToUint32` (wrapping modulo 2^32, mapping `NaN`/`±Infinity`
//!   to `+0`), never Rust's saturating float casts.
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

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

pub mod analysis;
pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use abcd_ir::{Const, FuncId, InstId, Module, Ty};

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

/// Canonical quiet `NaN` bit pattern (`+qNaN`, `#60`).
pub(crate) const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;

/// Normalize an `f64` produced by constant folding so any `NaN` maps to
/// [`CANONICAL_NAN_BITS`] while `-0.0` (`0x8000_0000_0000_0000`) and all finite
/// / infinite bit patterns survive verbatim (`#60`).
#[inline]
pub(crate) fn canonicalize_f64_bits(v: f64) -> u64 {
    if v.is_nan() {
        CANONICAL_NAN_BITS
    } else {
        v.to_bits()
    }
}

/// Construct a [`Const::Number`] with canonicalized `NaN` bits (`#60`).
#[inline]
pub(crate) fn canonical_number_const(v: f64) -> Const {
    Const::Number(canonicalize_f64_bits(v))
}

/// Whether `x` is a finite odd integer in IEEE-754 `f64`. Any finite integer
/// with `|x| >= 2^53` (`9007199254740992.0`) has unit-in-the-last-place `>= 2`
/// and is therefore even.
#[inline]
fn is_odd_integral(x: f64) -> bool {
    if !x.is_finite() || x.trunc() != x {
        return false;
    }
    let abs = x.abs();
    if abs >= 9_007_199_254_740_992.0 {
        return false;
    }
    (abs as u64) & 1 == 1
}

/// ECMA-262 §6.1.6.1.3 `Number::exponentiate(base, exponent)` (`#56` `R3-H6`),
/// delegating general finite cases to pure-Rust `libm::pow` with canonicalized
/// `NaN` bits (`#60`).
pub(crate) fn ecma_pow(base: f64, exponent: f64) -> f64 {
    let nan = f64::from_bits(CANONICAL_NAN_BITS);
    if exponent.is_nan() {
        return nan;
    }
    if exponent == 0.0 {
        return 1.0;
    }
    if base.is_nan() {
        return nan;
    }
    if exponent == f64::INFINITY {
        let abs_b = base.abs();
        return if abs_b > 1.0 {
            f64::INFINITY
        } else if abs_b == 1.0 {
            nan
        } else {
            0.0
        };
    }
    if exponent == f64::NEG_INFINITY {
        let abs_b = base.abs();
        return if abs_b > 1.0 {
            0.0
        } else if abs_b == 1.0 {
            nan
        } else {
            f64::INFINITY
        };
    }
    if base == f64::INFINITY {
        return if exponent > 0.0 { f64::INFINITY } else { 0.0 };
    }
    if base == f64::NEG_INFINITY {
        let odd = is_odd_integral(exponent);
        return if exponent > 0.0 {
            if odd {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            }
        } else if odd {
            -0.0
        } else {
            0.0
        };
    }
    if base == 0.0 {
        if !base.is_sign_negative() {
            return if exponent > 0.0 { 0.0 } else { f64::INFINITY };
        }
        let odd = is_odd_integral(exponent);
        return if exponent > 0.0 {
            if odd { -0.0 } else { 0.0 }
        } else if odd {
            f64::NEG_INFINITY
        } else {
            f64::INFINITY
        };
    }
    if base < 0.0 && exponent.is_finite() && exponent.trunc() != exponent {
        return nan;
    }
    let r = libm::pow(base, exponent);
    f64::from_bits(canonicalize_f64_bits(r))
}

/// Whether `inst_id`'s result or any of its operands carries a static ArkTS
/// [`Ty::Static`] annotation (`R3-A11` / `#36` — dynamic JS `f64` / `ToInt32`
/// folds must not rewrite static integer/float ops).
pub(crate) fn has_static_ty(module: &Module, inst_id: InstId) -> bool {
    let Some(inst) = module.inst(inst_id) else {
        return false;
    };
    if let Some(res) = inst.result
        && matches!(module.value(res).map(|v| &v.ty), Some(Ty::Static(_)))
    {
        return true;
    }
    let mut static_operand = false;
    inst.op.for_each_operand(|v| {
        if !static_operand && matches!(module.value(v).map(|val| &val.ty), Some(Ty::Static(_))) {
            static_operand = true;
        }
    });
    static_operand
}

/// Run the full optimization pipeline on a single function.
/// Pipeline: peephole → sccp → adce + cfg-simplify → copyprop → peephole
/// → adce + cfg-simplify → trailing copyprop (+ adce).
/// Returns `true` if any pass modified the IR.
pub fn optimize_func(module: &mut Module, func: FuncId) -> bool {
    let mut changed = false;

    // Round 1: peephole → sccp → adce + cfg simplify → copyprop
    changed |= peephole::Peephole.run(module, func);
    changed |= sccp::Sccp.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    changed |= copyprop::CopyProp.run(module, func);

    // Round 2: peephole → adce + cfg simplify → trailing copyprop (`R3-A12`)
    changed |= peephole::Peephole.run(module, func);
    changed |= dce::Adce.run(module, func);
    changed |= dce::CfgSimplify.run(module, func);
    if copyprop::CopyProp.run(module, func) {
        changed = true;
        let _ = dce::Adce.run(module, func);
    }

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
