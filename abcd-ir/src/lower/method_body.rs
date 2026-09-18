//! Produce an encodable [`abcd_file::MethodBody`] from a lowered function.
//!
//! [`lower_function`](super::lower_function) emits entity operands (strings,
//! method ids, literal-array ids) whose raw values are pre-resolved source
//! references, not method-local indices. `abcd_file::encode` relocates such
//! operands through `MethodBody.entity_offsets` (raw operand → source-file
//! offset) and `Builder::relocate_code_id` — the same channel the
//! decode → encode path uses. This module derives those relocation entries
//! from the module's recorded source mappings and the selection-time
//! [`EntityTrace`] records:
//!
//! - `StringId` / `MethodId` operands carry the source-file offset itself
//!   (isel resolves them through `module.string_entities`, populated by
//!   lift's `resolve_entity`). The relocation entry is the identity
//!   `(kind, offset) → offset`, valid because `abcd_file::encode` treats the
//!   raw operand purely as a lookup key and overwrites the operand bytes
//!   with the relocated index. An operand that is not a recorded source
//!   offset of the given file (identity fallback for hand-built modules, or
//!   a stale offset from a different file) is a hard error.
//! - `LiteralarrayId` operands carry the decoded literal-array table index
//!   (lift's `resolve_literal_array` maps source offset → index). The
//!   relocation entry `(kind, index) → offset` is recovered by inverting
//!   `File::literal_array_offsets`; an index with no table entry is a hard
//!   error.

use std::collections::HashMap;

use abcd_file::{File, MethodBody};
use abcd_isa::EntityKind;

use crate::entity::FuncId;
use crate::module::Module;

use super::layout::LayoutResult;
use super::{EntityTrace, LowerError};

/// Build an encodable [`MethodBody`] for a lowered function.
///
/// `file` is the source file the module was lifted from: it provides the
/// entity-offset table (string/method offset → name) and the literal-array
/// offset ↔ index mapping the relocation entries must agree with.
///
/// Every entity operand of every emitted bytecode must be traceable to a
/// source-file offset recorded in `module` and resolvable in `file`;
/// otherwise [`LowerError::UntraceableEntity`] is returned. There is no
/// silent pass-through of untraceable operands.
pub fn to_method_body(
    module: &Module,
    func_id: FuncId,
    result: &LayoutResult,
    file: &File,
) -> Result<MethodBody, LowerError> {
    let func = module.func(func_id);

    // Invert the file's literal-array table: decoded index → source offset.
    let mut la_index_to_offset: HashMap<u32, u32> =
        HashMap::with_capacity(file.literal_array_offsets.len());
    for (&offset, &index) in &file.literal_array_offsets {
        la_index_to_offset.insert(index, offset);
    }

    let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
    for bc in &result.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset = match kind {
                EntityKind::StringId | EntityKind::MethodId => {
                    // The raw operand must be a selection-time-traced source
                    // offset that resolves in this file's entity map. Decode
                    // guarantees entity_map coverage for every offset a
                    // method body's string/method operands reference
                    // (abcd-file/src/decode.rs:256-270).
                    match result.entity_traces.get(&id.0) {
                        Some(EntityTrace::Traced) if file.entity_map.contains_key(&id.0) => id.0,
                        _ => {
                            return Err(LowerError::UntraceableEntity {
                                func: func_id,
                                kind,
                                raw: id.0,
                            });
                        }
                    }
                }
                EntityKind::LiteralarrayId => match la_index_to_offset.get(&id.0) {
                    Some(&offset) => offset,
                    None => {
                        return Err(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        });
                    }
                },
            };
            entity_offsets.insert((kind, id.0), offset);
        }
    }

    Ok(MethodBody {
        // Convention (abcd-file/src/decode.rs:717-723): num_vregs counts the
        // method's own registers only, num_args the arguments; the runtime
        // frame is num_vregs + num_args with args in the top slots
        // (vendor static_core/runtime/include/method.h:514). The lowering
        // frame numbers every used register from 0 (params included), so
        // num_regs is the vreg count and param_count the arg count.
        num_vregs: u32::from(result.num_regs),
        num_args: u32::from(func.param_count),
        bytecodes: result.bytecodes.clone(),
        entity_offsets,
        try_blocks: result.try_blocks.clone(),
    })
}
