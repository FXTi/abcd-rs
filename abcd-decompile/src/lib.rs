//! # abcd-decompile — bytecode → JS/TS decompiler (Stage A: expression recovery)
//!
//! The decompiler consumes the **lifted (pre-opt) v0.2 IR** and produces
//! readable JavaScript in three stages (design/decompile.md §4):
//!
//! - **Stage A — expression recovery** (THIS crate, d-P2): SSA def-use →
//!   expression trees, per basic block. Inline/temporary decisions read the
//!   IR's effect table ([`abcd_ir::Effects`]); phis become temporaries with
//!   per-predecessor assignment records (out-of-SSA at AST level);
//!   `ExceptionParam` values become `catch (e)` bindings; names come from
//!   `DebugData`/`Sym` hints through the [`legalize`]r. The output is an
//!   internal expression tree ([`expr`]) + per-block statement lists
//!   ([`recover::RecoveredFunc`]) with a stable text form ([`dump`]) —
//!   **not** final JS text.
//! - **Stage B — control-flow structuring** (d-P3): region-tree consumption
//!   (`abcd-analysis::control::regions`), JS desugaring fold rules
//!   (for-of/for-in, guard elision at the region level, literal folds).
//! - **Stage C — emission** (d-P4): precedence-correct pretty-printing,
//!   module/class/function emission, the recompile-and-run gate.
//!
//! ## Pipeline rules (design/decompile.md §3.2, restated as law)
//!
//! 1. **The `abcd-opt` `inline` pass must never run before decompile** —
//!    it destroys function boundaries, the one structural fact a reader
//!    cares most about.
//! 2. Guard ops (the `Throw*` family) are **elided on purpose**, never
//!    silently: every elision is recorded as an
//!    [`recover::Stmt::Elided`] node with the op name and source location
//!    (gen1 lesson: silent wrongness is worse than loud absence).
//! 3. Anything Stage A cannot yet express becomes an explicit
//!    [`expr::Expr::Fallback`] / [`recover::Stmt::Fallback`] node naming
//!    the op — the fallback-honesty rule. The §5 fitness table's "hard 7"
//!    ops are exactly such nodes (see [`fitness`]).
//!
//! ## Stage A scope notes (deliberate)
//!
//! - **Block-local + phi wiring only.** The conservative v1 inline rule
//!   requires def and use in the *same block*; cross-block inlining
//!   (dominance-based) and region-tree consumption are d-P3.
//! - Object/array literal builders keep their `AllocObject`/`AllocArray`
//!   shape + own-store sequence; the FOLD into a single literal is a d-P3
//!   desugar rule. [`recover::builder_hook`] exposes the sequence.
//! - Template literals are cooked-only (IR gap G4, registered by d-P0).

#![deny(missing_docs)]

pub mod consts;
pub mod dump;
pub mod expr;
pub mod fitness;
pub mod legalize;
pub mod names;
pub mod recover;

pub use recover::{RecoveredFunc, recover_func};
