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
//! - `StringId` operands carry the source-file offset of a STRING entity
//!   (isel resolves them through `module.string_entities`, which lift
//!   populates for `EntityKind::StringId` resolutions only). The relocation
//!   entry is the identity `(kind, offset) → offset`, valid because
//!   `abcd_file::encode` treats the raw operand purely as a lookup key and
//!   overwrites the operand bytes with the relocated index.
//! - `MethodId` operands carry the source-file offset of the referenced
//!   METHOD, recorded per use-site by lift onto the IR instruction itself
//!   (`InstData::DefineFunc::method_offset` etc.) — the name is not the
//!   identity (two methods can share a name; a method name can collide with
//!   a string of the same content). The offset must be a selection-time
//!   MethodId trace AND a member of the file's method set
//!   (`File::all_methods()`), matching encode's `methods_by_offset` lookup.
//! - A string/method operand that is not traceable (identity fallback for
//!   hand-built modules, or a stale offset from a different file) is a hard
//!   error.
//! - `LiteralarrayId` operands carry the decoded literal-array table index
//!   (lift's `resolve_literal_array` maps source offset → index). The
//!   relocation entry `(kind, index) → offset` is recovered by inverting
//!   `File::literal_array_offsets`; an index with no table entry is a hard
//!   error.

use std::collections::HashMap;
use std::collections::HashSet;

use abcd_file::{File, MethodBody};
use abcd_isa::EntityKind;

use crate::entity::FuncId;
use crate::module::Module;

use super::layout::LayoutResult;
use super::{EntityTrace, LowerError};

/// Build an encodable [`MethodBody`] for a lowered function.
///
/// `file` is the source file the module was lifted from: it provides the
/// entity-offset table (string/method offset → name), the method set, and
/// the literal-array offset ↔ index mapping the relocation entries must
/// agree with.
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

    // The file's method offsets: encode resolves MethodId operands through
    // `methods_by_offset`, so a MethodId operand must name a real method of
    // this file — a string offset or a stale foreign offset is a hard error.
    let method_offsets: HashSet<u32> = file.all_methods().map(|(_, m)| m.offset).collect();

    let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
    for bc in &result.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset = match kind {
                EntityKind::StringId => {
                    // The raw operand must be a selection-time-traced source
                    // offset that resolves in this file's entity map. Decode
                    // guarantees entity_map coverage for every offset a
                    // method body's string/method operands reference
                    // (abcd-file/src/decode.rs:256-270).
                    match result.entity_traces.get(&(kind, id.0)) {
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
                EntityKind::MethodId => {
                    // Method identity is the source offset carried on the IR
                    // instruction (traced as MethodId at selection time);
                    // membership in the file's method set is the exact
                    // precondition of encode's methods_by_offset lookup.
                    match result.entity_traces.get(&(kind, id.0)) {
                        Some(EntityTrace::Traced) if method_offsets.contains(&id.0) => id.0,
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
        // (vendor static_core/runtime/include/method.h:514). Under the
        // copy-in prologue this split is EXACT: parameter values are pinned
        // to vreg homes at the bottom of the lowering frame (inside
        // num_regs, alongside the reserved copy-temp/spill slots), and the
        // prologue Moves the ABI top slots Reg(num_regs + i) into those
        // homes at entry. Args live above the declared vregs, never
        // aliasing a local slot.
        num_vregs: u32::from(result.num_regs),
        num_args: u32::from(func.param_count),
        bytecodes: result.bytecodes.clone(),
        entity_offsets,
        try_blocks: result.try_blocks.clone(),
    })
}
