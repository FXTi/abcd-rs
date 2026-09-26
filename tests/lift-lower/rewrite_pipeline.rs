//! Shared decode → lift → verify → lower → encode pipeline helpers for the
//! corpus rewrite suites (`corpus_lower_oracle`, `test262_vm`). Extracted
//! verbatim from `corpus_lower_oracle.rs` so every suite runs the SAME
//! front-end + `rewrite_fixture` path (test262 P2).

use std::fmt;

use abcd_file::File;
use abcd_ir::{verify_module, FuncId, Module};
use abcd_lift::lift_file;
use abcd_lower::{lower_function_with_options, to_method_body, LowerError};

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
pub(crate) fn rewrite_fixture(
    module: &Module,
    file: &File,
    options: abcd_lower::LowerOptions,
) -> Result<(Vec<u8>, usize), Skip> {
    // Function i corresponds to the i-th method in lift order (classes in
    // file order, methods in declaration order — the lift's pass-1
    // reservation order, which is `File::all_methods()` order).
    //
    // Bodyless functions (external/native declarations, lifted as
    // block-less external FunctionData) keep their `None` body; every
    // other function lowers to a fresh MethodBody.
    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id).expect("function-table index");
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let name = module.sym.resolve(func.name).unwrap_or("?").to_string();
        let lowered = lower_function_with_options(module, func_id, options)
            .map_err(|e| (lower_category(&e), format!("lower {name}: {e}")))?;
        let body = to_method_body(module, func_id, &lowered, file)
            .map_err(|e| (lower_category(&e), format!("to_method_body {name}: {e}")))?;
        bodies.push(Some(body));
    }
    let functions = bodies.iter().filter(|b| b.is_some()).count();

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("a lowered body for every method that had one"));
            }
        }
    }
    assert!(cursor.next().is_none());

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
