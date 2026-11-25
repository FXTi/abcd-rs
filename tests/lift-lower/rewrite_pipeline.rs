//! Shared decode → lift → verify → lower → encode pipeline helpers for the
//! corpus rewrite suites (`corpus_lower_oracle`, `test262_vm`). Extracted
//! verbatim from `corpus_lower_oracle.rs` so every suite runs the SAME
//! front-end + `rewrite_fixture` path (test262 P2).

use std::fmt;

use abcd_file::File;
use abcd_ir::{Module, verify_module};
use abcd_lift::lift_file;
use abcd_lower::{LowerError, rewrite_file};

/// Fixed SKIP category vocabulary (mirrors the v0.1 driver's; the
/// histogram keys are gate evidence — keep them stable).
pub(crate) enum SkipCategory {
    /// Front-end failure: read, decode, or lift.
    Lift,
    /// Structural verifier failure.
    Verify,
    /// `LowerError::UnsupportedInstruction` — payload is the instruction.
    LowerUnsupported(String),
    /// `LowerError::UntraceableEntity` — payload is the `EntityKind`.
    LowerUntraceable(String),
    /// Any other lower / to_method_body (relocation) error.
    LowerOther,
    /// `abcd_file::encode` failure.
    Encode,
    /// A panic caught by `catch_unwind`.
    Panic,
}

impl fmt::Display for SkipCategory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SkipCategory::Lift => write!(f, "lift"),
            SkipCategory::Verify => write!(f, "verify"),
            SkipCategory::LowerUnsupported(inst) => write!(f, "lower-unsupported:{inst}"),
            SkipCategory::LowerUntraceable(kind) => write!(f, "lower-untraceable:{kind}"),
            SkipCategory::LowerOther => write!(f, "lower-other"),
            SkipCategory::Encode => write!(f, "encode"),
            SkipCategory::Panic => write!(f, "panic"),
        }
    }
}

pub(crate) type Skip = (SkipCategory, String);

/// Classify a `LowerError` into the fixed category vocabulary.
fn lower_category(error: &LowerError) -> SkipCategory {
    match error {
        LowerError::UnsupportedInstruction { message, .. } => {
            SkipCategory::LowerUnsupported(message.clone())
        }
        LowerError::UntraceableEntity { kind, .. } => {
            SkipCategory::LowerUntraceable(format!("{kind:?}"))
        }
        _ => SkipCategory::LowerOther,
    }
}

/// Front-end stage: read → decode → v0.2 lift → ir2 verify.
pub(crate) fn front_end(path: &std::path::Path) -> Result<(File, Module), Skip> {
    let data = std::fs::read(path).map_err(|e| (SkipCategory::Lift, format!("read: {e}")))?;
    let file =
        abcd_file::decode(&data).map_err(|e| (SkipCategory::Lift, format!("decode: {e}")))?;
    let module = lift_file(&file).map_err(|e| (SkipCategory::Lift, format!("lift: {e}")))?;
    let report = verify_module(&module);
    if !report.is_ok() {
        return Err((SkipCategory::Verify, format!("verify: {:?}", report.errors)));
    }
    Ok((file, module))
}

/// Lower every function of `module`, splice the bodies into a clone of
/// `file`, and encode. Returns the encoded bytes and the function count.
/// All-or-nothing: the first lower/relocate/encode error aborts the
/// fixture; nothing is written by the caller in that case.
///
/// `options` selects the v0.1 parity target: default (lift) for
/// `v2lift`; `prune_unused_frame_init_consts` for `v2opt` — the
/// optimizer deletes the last use of a frame-initial constant, and the
/// v0.1 pipeline's ADCE swept the seed INSTRUCTION in that case (the
/// v0.2 seed is instruction-less, so the lower must skip the
/// materialization — see `LowerOptions`).
/// Lower every function of `module` via `abcd_lower::rewrite_file` (syncing
/// `MethodBody::entities`, `_ESSlotNumberAnnotation` IC counts, synthesized
/// pool entries, and reconstructed `MethodDebugInfo` — `#50`, `#57` `R3-H8`)
/// and encode. Returns the encoded bytes and lowered function count.
pub(crate) fn rewrite_fixture(
    module: &Module,
    file: &File,
    options: abcd_lower::LowerOptions,
) -> Result<(Vec<u8>, usize), Skip> {
    let functions = module
        .functions
        .iter()
        .filter(|f| !f.blocks.is_empty())
        .count();
    let rebuilt =
        rewrite_file(module, file, options).map_err(|e| (lower_category(&e), format!("{e}")))?;
    let encoded =
        abcd_file::encode(&rebuilt).map_err(|e| (SkipCategory::Encode, format!("encode: {e}")))?;
    Ok((encoded, functions))
}

/// Catch panics from an arbitrary stage so one bad fixture reports as a
/// skip instead of aborting the whole evidence run.
pub(crate) fn guarded<T>(stage: impl FnOnce() -> Result<T, Skip>) -> Result<T, Skip> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(stage)) {
        Ok(result) => result,
        Err(payload) => {
            let reason = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "unknown panic".to_string());
            Err((SkipCategory::Panic, format!("panic: {reason}")))
        }
    }
}
