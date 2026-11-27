//! Mechanism integration tests (`design/analysis.md`, `design/decisions.md`):
//! one test per taint mechanism over a hand-built IR module (using the
//! builders in `common` that preserve IR verifier invariants).

use crate::common;
use abcd_ir::{CallKind, Op};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};
use common::*;

/// The standard config: all `func_main_0` params are sources, `print`
/// is the sink, no builtin summaries (tests register exactly what they
/// exercise).
pub(super) fn std_config() -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        ..TaintConfig::default()
    }
}

/// `print(...)` call in block `b` over `args`; returns the call inst.
pub(super) fn print_call(
    m: &mut abcd_ir::Module,
    b: abcd_ir::BlockId,
    args: Vec<abcd_ir::ValueId>,
) -> abcd_ir::InstId {
    let print = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: print,
            this: None,
            args,
            kind: CallKind::Dynamic,
        },
    )
}

/// The std config plus the full builtin registry (including
/// prototype-family entries).
pub(super) fn builtin_config() -> TaintConfig {
    TaintConfig {
        builtin_summaries: true,
        ..std_config()
    }
}

/// `recv.leaf(args...)` with an explicit `this` receiver; returns the
/// call's result value.
pub(super) fn method_call(
    m: &mut abcd_ir::Module,
    b: abcd_ir::BlockId,
    recv: abcd_ir::ValueId,
    leaf: &str,
    args: Vec<abcd_ir::ValueId>,
) -> abcd_ir::ValueId {
    let name = intern(m, leaf);
    let f = emit(m, b, Op::LoadProp { object: recv, name });
    emit(
        m,
        b,
        Op::Call {
            callee: f,
            this: Some(recv),
            args,
            kind: CallKind::Dynamic,
        },
    )
}

mod ifds_and_rung1;
mod prototype_and_gap;
mod stdlib_and_scaling;
