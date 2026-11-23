//! # abcd-decompile — bytecode → JS/TS decompiler
//!
//! Consumes the **lifted (pre-opt) SSA IR** ([`abcd_ir::Module`]) and emits
//! readable JavaScript (or TypeScript-annotated output on ≤11-format files) in
//! three stages (`design/decompile.md` §4):
//!
//! - **Stage A — expression recovery** ([`recover`], [`expr`], [`names`]):
//!   SSA def-use → per-block expression trees using [`abcd_ir::Effects`]
//!   barrier checks; phis become temporaries with per-predecessor `PhiAssign`
//!   records; `ExceptionParam` values bind `catch (e)` clauses; lexical,
//!   private, and G2 module-var names resolve from IR/debug evidence.
//! - **Stage B — control-flow structuring & desugaring** ([`structure`],
//!   [`folds`], [`classfold`]): pattern-independent structuring over
//!   [`abcd_analysis::control::structure_regions`], `TryRegion` / `finally` / cut-try
//!   projection, class reconstruction, raw+cooked template literals,
//!   `for..of` / `for..in` / `for await..of`, and generator / async /
//!   async-generator / `yield*` state-machine folds.
//! - **Stage C — emission** ([`emit`]): precedence-exact pretty-printing
//!   ([`decompile_module`]), module imports/exports, and explicit fallback /
//!   elided-guard annotations.
//!
//! ## Pipeline rules (`design/decompile.md` §3.2)
//!
//! 1. **The `abcd-opt` `inline` pass must never run before decompile** —
//!    it destroys function boundaries, the structural unit readers rely on.
//! 2. Guard ops (`Throw*`, `AsyncFunctionEnter`) are **elided on purpose**
//!    and recorded as [`recover::Stmt::Elided`] markers with source locations.
//! 3. Any unrecovered op or un-folded state-machine residual renders as an
//!    explicit [`expr::Expr::Fallback`] / [`recover::Stmt::Fallback`] comment
//!    naming the op (see [`fitness`]) — never silently dropped.

#![deny(missing_docs)]

pub mod classfold;
pub mod consts;
pub mod dump;
pub mod emit;
pub mod expr;
pub mod fitness;
pub mod folds;
pub mod legalize;
pub mod names;
pub mod recover;
pub mod structure;

pub use emit::{DecompiledModule, EmitOptions, decompile_module};
pub use recover::{RecoveredFunc, recover_func};
pub use structure::{SNode, Structured, structure_func};
