//! Regression tests for GitHub Issue #94 (Parts 1–3: `abcd-taint`):
//! - `D6`: Zero-copy `FlowSink::pass_through()` parity with `*_flow` wrappers
//! - `D5`, `R1`, `R2`, `T1`, `R3`: Concrete-singleton strong-update discipline,
//!   `EdgeKind::Exceptional` strong-kill ban, and partly-unknown store receivers
//! - `R4`: Separated `uncaught_edge_set` + multi-frame uncaught-exit witness paths
//! - `R5`: Dynamic ECMAScript `class Sub extends Base` virtual `this.method()` override
//! - `cut_first`: 2-step property reads (`source().a.b` and `x.a.b = source()`)
//! - `BodyStep` excess actuals (`arguments` / `...rest`) & `exclusive` summary bypass
//! - `R7`: `globalThis` (`LoadGlobalObject`) `Mov`-peeled transfer & reader cone
//! - `#private` fields (`LoadPrivate`, `StorePrivate`, `DefinePrivate`)
//! - `R8`: `export * as ns` namespace re-exports & `GetModuleNamespace`
//! - `R10`: Rung 0/1 captured `LexVar` `level` shift
//! - `D3`: Steady-state `EntryModel` OHOS lifecycle & `OhmUrl` specifier normalization
//! - `names.rs` / `prototype.rs` diamond DAG memoization, `call_base_value` `Mov` peeling,
//!   `gap.rs` `DefineMethod` callback resolution, and `L6` `Endpoint::parse`.

use crate::common::*;
use abcd_ir::{CallKind, Module, Op, ValueId};
use abcd_taint::{SinkSpec, SourceSpec, TaintConfig};

pub(super) fn std_config_at(rung: u8) -> TaintConfig {
    TaintConfig {
        sources: vec![SourceSpec::FunctionParams {
            name: "func_main_0".to_owned(),
            params: None,
        }],
        sinks: vec![SinkSpec::Call {
            name: "print".to_owned(),
        }],
        builtin_summaries: false,
        alias_rung: rung,
        ..TaintConfig::default()
    }
}

pub(super) fn emit_print(m: &mut Module, b: abcd_ir::BlockId, arg: ValueId) -> abcd_ir::InstId {
    let p = try_get_global(m, b, "print");
    push_inst(
        m,
        b,
        Op::Call {
            callee: p,
            this: None,
            args: vec![arg],
            kind: CallKind::Dynamic,
        },
    )
}

mod heap_and_dispatch;
mod scopes_esm_and_ohos;
