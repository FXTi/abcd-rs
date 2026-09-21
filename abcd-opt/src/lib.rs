//! # abcd-opt — optimization passes for the SSA IR (`abcd-ir`)
//!
//! The v0.2 port of v0.1's `abcd-ir/src/opt` pipeline (migration P3 of
//! `design/ir-v0.2.md`): [`peephole`] (constant folding), [`sccp`] (sparse
//! conditional constant propagation), [`dce`] (aggressive dead code
//! elimination + CFG simplification), and [`copyprop`] (trivial-phi
//! elimination). [`inline`] is the D2 (2026-09-21) rewrite of v0.1's
//! N44-quarantined inliner on the v0.2 IR — OPT-IN ONLY, never wired
//! into [`optimize_module`] (the corpus byte-identity gates measure the
//! default pipeline).
//!
//! ## Format independence (hard, structurally enforced)
//!
//! Every pass operates on [`abcd_ir::Module`] alone. This crate's
//! `Cargo.toml` [dependencies] list **only** `abcd-ir` (the IR) — never
//! `abcd-file`, `abcd-isa`, `abcd-file-sys`, `abcd-isa-sys`, `abcd-lift`,
//! or `abcd-lower` (the format-coupled crates are dev-dependencies only,
//! for the end-to-end regression tests) — the crate graph is the
//! enforcement mechanism.
//!
//! ## The v0.1 behavioral contract that survives the port
//!
//! - **N36**: both fold engines evaluate non-commutative operators in
//!   vendored operand order (`vreg OP acc`, i.e. `right OP left` in IR
//!   field terms — lift's `binary_op`/`compare` emit `left = acc`,
//!   `right = vreg`).
//! - **N37**: folds preserve `-0.0` (constants are bit-exact
//!   [`Const::Number`](abcd_ir::Const) payloads; no fold canonicalizes
//!   `-0.0` to `+0.0`).
//! - **N38**: SCCP exception soundness — reachability includes
//!   [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) edges, handler-block
//!   phis are forced to lattice Bottom, and `Eq`/`NotEq` never
//!   ToNumber-coerce nullish operands.
//! - **N39**: `UnOp::BitNot` (vendor `not`) is bitwise; `LogicalNot` is
//!   the boolean one.
//! - **N40**: `StrictEq` folds with host `==` on numbers (`0 === -0`
//!   true, `NaN !== NaN`), never a bit comparison.
//! - **N41**: `null` is never coerced to `0.0` by a fold.
//! - **N42**: bitwise/shift folds use ECMA-262 [`to_int32`]/[`to_uint32`]
//!   (wrap mod 2^32, NaN/±Inf → +0), not Rust's saturating casts.
//! - **N47**: SCCP's edge seeding does not stop at `Return`/`Unreachable`
//!   terminators — exception edges are still added.
//! - **N48/N50**: ADCE essentiality is DERIVED from
//!   [`Op::effects`](abcd_ir::Op::effects) (T3) — no hand-maintained
//!   list; see [`dce`].
//! - **N27/N28**: passes keep the module verifier-clean (no empty phis on
//!   reachable blocks, no copyprop residue); the corpus driver re-verifies
//!   after optimizing.
//!
//! ## Accepted byte divergences from the v0.1 optimizer (gate 2)
//!
//! Maintainer ruling (2026-09-21, v2-P3): the v2opt rewrite diverges from
//! the v0.1 opt rewrite on exactly the 53 N62 files (lift-layer literal
//! array dedup, accepted) plus 90 files in three attributed, VM-neutral
//! mechanisms — `1149/1149 − 53 N62 − 90 (P3-M1/P3-M2/N63)`:
//!
//! - **P3-M1 (72 files)** — fold re-materialization keeps opcode
//!   identity: a folded canonical-NaN/+∞ pools as `Const::Number` bits
//!   and lowers back to `ldnan`/`ldinfinity`, where v0.1's
//!   `LiteralNumber` fold degraded to `fldai`.
//! - **P3-M2 (12 files)** — ADCE essentiality is effects-derived, and
//!   the honest `DefineFunc`/`AllocClosure` records (vendor
//!   `RuntimeDefinefunc` runs no user code,
//!   runtime_stubs-inl.h:2459-2505) let ADCE delete dead
//!   definefunc+closure chains that v0.1's conservative hand-list kept.
//! - **N63 (6 files)** — v0.1's SCCP left exception-param values at
//!   lattice Top (the identity element), folding phis that mix a
//!   constant with the exception object down to the constant; v0.2
//!   resolves [`ValueDef::ExceptionParam`](abcd_ir::ValueDef) to Bottom
//!   and keeps the phi — strictly more sound.
//!
//! ## Library rule
//!
//! No panics on data: arena lookups return `Option`; passes skip what
//! they cannot soundly rewrite.

#![deny(missing_docs)]

pub mod analysis;
pub mod copyprop;
pub mod dce;
pub mod inline;
pub mod peephole;
pub mod sccp;

use abcd_ir::{FuncId, Module};

/// A function-level optimization pass (v0.1 `opt::FuncPass`).
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
/// → adce + cfg-simplify (v0.1 `opt::optimize_func`).
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

/// Run the optimization pipeline on all functions in the module
/// (v0.1 `opt::optimize_module`). Bodyless functions (external/native
/// declarations) are skipped.
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
