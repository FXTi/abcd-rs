//! Entity resolution: bytecode `EntityId` → [`Sym`] / [`FuncId`] /
//! [`ConstId`], and literal arrays → typed [`Const`] trees.
//!
//! The S1/N2 lessons, applied: a method reference's identity is its
//! source-file offset, resolved through the pass-1 method table to a
//! [`FuncId`] — never name-keyed (two methods can share a name; a name
//! can collide with a string entity). Strings are content-keyed symbols.
//! Literal arrays become typed [`Const`] trees (N52: no raw offsets
//! anywhere — typed `ARRAY_*` payloads, which the v0.1 file model keeps
//! as raw file offsets, are resolved through
//! `File::literal_array_offsets` here).

use abcd_file::{File, LiteralValue, MethodBody};
use abcd_ir::module::FunctionKind;
use abcd_ir::op::MemberAttrs;
use abcd_ir::{Const, ConstId, FuncId, Sym};
use abcd_isa::{EntityId, EntityKind};

use crate::{LiftError, Lifter};

/// Resolve an [`EntityId`] through the owning method's typed index
/// mapping to a symbol (string-pool entities).
pub fn resolve_sym(
    lf: &mut Lifter,
    body: &MethodBody,
    id: EntityId,
    kind: EntityKind,
) -> Result<Sym, LiftError> {
    let Some(offset) = body.entity_offsets.get(&(kind, id.0)) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    let Some(file_sid) = lf.file.resolve_entity(*offset) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    lf.sym_of_file_sid(file_sid)
        .ok_or(LiftError::UnresolvedEntity(id.0))
}

/// Resolve a method-reference [`EntityId`] to its display name and its
/// function-table index.
///
/// `body.entity_offsets[(MethodId, raw)]` gives the exact offset for
/// THIS use-site (decode records it per operand), so two same-named
/// methods referenced from one body resolve to their own offsets; the
/// offset then maps to the pass-1 [`FuncId`].
pub fn resolve_method(
    lf: &mut Lifter,
    body: &MethodBody,
    id: EntityId,
) -> Result<(Sym, FuncId), LiftError> {
    let Some(&offset) = body.entity_offsets.get(&(EntityKind::MethodId, id.0)) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    let Some(func_id) = lf.func_of_method_offset(offset) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    let Some(file_sid) = lf.file.resolve_entity(offset) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    let name = lf
        .sym_of_file_sid(file_sid)
        .ok_or(LiftError::UnresolvedEntity(id.0))?;
    Ok((name, func_id))
}

/// Resolve a method source-file offset to its [`FuncId`] (literal-array
/// method references — the same identity path as
/// [`resolve_method`]).
pub fn func_of_offset(lf: &Lifter, offset: u32) -> Result<FuncId, LiftError> {
    lf.func_of_method_offset(offset)
        .ok_or(LiftError::UnresolvedEntity(offset))
}

/// Resolve a literal-array [`EntityId`] to its decoded table index.
fn literal_table_index(file: &File, body: &MethodBody, id: EntityId) -> Result<u32, LiftError> {
    let Some(&offset) = body.entity_offsets.get(&(EntityKind::LiteralarrayId, id.0)) else {
        return Err(LiftError::UnresolvedEntity(id.0));
    };
    file.literal_array_offsets
        .get(&offset)
        .copied()
        .ok_or(LiftError::UnresolvedEntity(id.0))
}

/// Resolve a literal-array [`EntityId`] to its pooled shape constant.
pub fn resolve_literal_const(
    lf: &mut Lifter,
    body: &MethodBody,
    id: EntityId,
) -> Result<ConstId, LiftError> {
    let idx = literal_table_index(lf.file, body, id)?;
    const_for_literal_array(lf, idx)
}

/// Parse the per-member attribute payloads (B2 — [`MemberAttrs`]) out of
/// a class member buffer (the literal array behind
/// `defineclasswithbuffer` / `callruntime.definesendableclass`).
///
/// Vendor-grounded member form (arkcompiler_ets_runtime-master): each
/// member is the literal-entry triple `string:<name>`,
/// `method|getter|setter|generator_method:<ref>`,
/// `method_affiliate:<length>` — the runtime collapse keeps (name,
/// value) pairs where the method-kind tag sets the materialized
/// function's `FunctionKind` and the affiliate materializes it
/// (`ecmascript/jspandafile/literal_data_extractor.cpp:588-624`). The
/// trailing `i32` is the count of NON-STATIC members ("hidden in the
/// last index of Literal buffer",
/// `ecmascript/jspandafile/class_info_extractor.cpp:36-42`); pairs
/// at-or-past that count install on the class object (static) —
/// `class_info_extractor.cpp:78` and `extractBegin = nonStaticNum * 2`.
///
/// The result parallels the pooled buffer's `MethodRef` sequence (the
/// same member order). A buffer outside this grounded form (accessor
/// payloads, data-valued members, nested arrays, a missing/mismatched
/// trailing count) yields an EMPTY vector — the documented conservative
/// fallback: consumers treat the attributes as unknown, never guessed.
pub fn class_member_attrs(
    lf: &mut Lifter,
    body: &MethodBody,
    id: EntityId,
    is_sendable: bool,
) -> Result<Vec<MemberAttrs>, LiftError> {
    let idx = literal_table_index(lf.file, body, id)?;
    class_member_attrs_for_index(lf.file, idx, is_sendable)
}

/// Parse the per-member attribute payloads ([`MemberAttrs`]) out of the
/// decoded literal array at `table_idx` (shared by entity-relocated modern /
/// decoded-legacy class buffers and direct-table-index `deprecated.*` tests).
pub fn class_member_attrs_for_index(
    file: &File,
    table_idx: u32,
    is_sendable: bool,
) -> Result<Vec<MemberAttrs>, LiftError> {
    let Some(arr) = file.literal_arrays.get(table_idx as usize) else {
        return Err(LiftError::LiteralArrayOutOfRange(table_idx));
    };
    let raw_values = &arr.values;
    // Sendable class buffers (`callruntime.definesendableclass`) append a
    // trailing `lit_offset` (`LiteralValue::LiteralArray` after decode, or
    // `LiteralValue::LiteralBufferIndex`) pointing to the field-type layout
    // literal array after the `i32` non-static member count
    // (`ClassInfoExtractor::BuildSendableClassInfoExtractor`). Strip that
    // single trailing slot only for sendable classes so `defineclasswithbuffer`
    // keeps rejecting unexpected nested arrays.
    let values = match (is_sendable, raw_values.last()) {
        (true, Some(LiteralValue::LiteralArray(_) | LiteralValue::LiteralBufferIndex(_))) => {
            &raw_values[..raw_values.len() - 1]
        }
        _ => raw_values.as_slice(),
    };
    let conservative = Vec::new();
    let mut kinds: Vec<FunctionKind> = Vec::new();
    let mut have_name = false;
    let mut pending_kind: Option<FunctionKind> = None;
    let mut non_static: Option<usize> = None;
    for (pos, v) in values.iter().enumerate() {
        let last = pos + 1 == values.len();
        match v {
            LiteralValue::String(_) => {
                if have_name || pending_kind.is_some() {
                    return Ok(conservative);
                }
                have_name = true;
            }
            LiteralValue::Method(_)
            | LiteralValue::GeneratorMethod(_)
            | LiteralValue::AsyncGeneratorMethod(_)
            | LiteralValue::Getter(_)
            | LiteralValue::Setter(_) => {
                if !have_name || pending_kind.is_some() {
                    return Ok(conservative);
                }
                pending_kind = Some(match v {
                    LiteralValue::Method(_) => FunctionKind::Function,
                    LiteralValue::GeneratorMethod(_) => FunctionKind::Generator,
                    LiteralValue::AsyncGeneratorMethod(_) => FunctionKind::AsyncGenerator,
                    LiteralValue::Getter(_) => FunctionKind::Getter,
                    LiteralValue::Setter(_) => FunctionKind::Setter,
                    _ => unreachable!("matched above"),
                });
            }
            LiteralValue::MethodAffiliate(_) => {
                let Some(kind) = pending_kind.take() else {
                    return Ok(conservative);
                };
                if !have_name {
                    return Ok(conservative);
                }
                have_name = false;
                kinds.push(kind);
            }
            // The trailing non-static member count (the vendor's "last
            // index" slot). Any other position/shape is ungrounded.
            LiteralValue::Integer(n) if last && !have_name && pending_kind.is_none() => {
                let Ok(count) = usize::try_from(*n) else {
                    return Ok(conservative);
                };
                non_static = Some(count);
            }
            _ => return Ok(conservative),
        }
    }
    if have_name || pending_kind.is_some() {
        return Ok(conservative);
    }
    let Some(non_static) = non_static else {
        return Ok(conservative);
    };
    if non_static > kinds.len() {
        return Ok(conservative);
    }
    Ok(kinds
        .into_iter()
        .enumerate()
        .map(|(i, kind)| MemberAttrs {
            is_static: i >= non_static,
            kind,
        })
        .collect())
}

/// Convert the literal array at `table_idx` into a pooled shape
/// constant.
pub fn const_for_literal_array(lf: &mut Lifter, table_idx: u32) -> Result<ConstId, LiftError> {
    let tree = const_tree_for_literal_array(lf, table_idx)?;
    Ok(lf.const_shape(tree))
}

/// Step outcome when converting one [`LiteralValue`] without native
/// call-stack recursion.
enum LitStep {
    /// Immediate scalar, string, or method-ref constant.
    Ready(Const),
    /// Nested literal-array reference at `table_idx` to expand on the
    /// explicit work stack.
    NestedArray(u32),
}

/// Active frame on the iterative literal-array conversion stack.
struct LitFrame<'f> {
    table_idx: u32,
    values: &'f [LiteralValue],
    next_elem: usize,
    consts: Vec<Const>,
}

/// Look up `table_idx` in the memo cache or validate and activate a new
/// [`LitFrame`] for iterative expansion.
fn enter_literal_array<'f>(
    lf: &mut Lifter<'f>,
    table_idx: u32,
) -> Result<Result<Const, LitFrame<'f>>, LiftError> {
    if let Some(tree) = lf.lit_cache.get(&table_idx) {
        return Ok(Ok(tree.clone()));
    }
    let file = lf.file;
    let Some(arr) = file.literal_arrays.get(table_idx as usize) else {
        return Err(LiftError::LiteralArrayOutOfRange(table_idx));
    };
    if !lf.lit_active.insert(table_idx) {
        return Err(LiftError::LiteralArrayCycle(table_idx));
    }
    Ok(Err(LitFrame {
        table_idx,
        values: &arr.values,
        next_elem: 0,
        consts: Vec::with_capacity(arr.values.len()),
    }))
}

/// Convert the literal array at `table_idx` into its [`Const`] tree
/// iteratively (memoized, cycle-guarded, O(1) native stack). Literal
/// shapes are inline TREES in v0.2's constant pool — a nested array is
/// embedded by value, so this returns the tree itself rather than a pool
/// reference.
fn const_tree_for_literal_array(lf: &mut Lifter, table_idx: u32) -> Result<Const, LiftError> {
    let first = match enter_literal_array(lf, table_idx)? {
        Ok(cached) => return Ok(cached),
        Err(frame) => frame,
    };
    let mut stack = vec![first];

    while let Some(next_elem) = stack.last().map(|f| f.next_elem) {
        let top_idx = stack.len() - 1;
        let values = stack[top_idx].values;
        if next_elem < values.len() {
            let v = &values[next_elem];
            stack[top_idx].next_elem += 1;
            let step = match step_literal_value(lf, v) {
                Ok(s) => s,
                Err(e) => {
                    for f in &stack {
                        lf.lit_active.remove(&f.table_idx);
                    }
                    return Err(e);
                }
            };
            match step {
                LitStep::Ready(c) => {
                    if let Some(parent) = stack.last_mut() {
                        parent.consts.push(c);
                    }
                }
                LitStep::NestedArray(child_idx) => match enter_literal_array(lf, child_idx) {
                    Ok(Ok(cached)) => {
                        if let Some(parent) = stack.last_mut() {
                            parent.consts.push(cached);
                        }
                    }
                    Ok(Err(child_frame)) => stack.push(child_frame),
                    Err(e) => {
                        for f in &stack {
                            lf.lit_active.remove(&f.table_idx);
                        }
                        return Err(e);
                    }
                },
            }
        } else {
            let Some(finished) = stack.pop() else {
                break;
            };
            lf.lit_active.remove(&finished.table_idx);
            let tree = Const::ArrayLiteral(finished.consts);
            lf.lit_cache.insert(finished.table_idx, tree.clone());
            if let Some(parent) = stack.last_mut() {
                parent.consts.push(tree);
            } else {
                return Ok(tree);
            }
        }
    }

    unreachable!("literal-array stack always returns when popping the root frame")
}

/// Convert one literal value to a [`Const`] (N52: every reference is
/// resolved — no raw offsets cross into the IR).
pub(crate) fn const_for_literal_value(
    lf: &mut Lifter,
    v: &LiteralValue,
) -> Result<Const, LiftError> {
    match step_literal_value(lf, v)? {
        LitStep::Ready(c) => Ok(c),
        LitStep::NestedArray(idx) => const_tree_for_literal_array(lf, idx),
    }
}

/// Classify a single [`LiteralValue`] into an immediate [`Const`] or a
/// nested literal-array index without recursing.
fn step_literal_value(lf: &mut Lifter, v: &LiteralValue) -> Result<LitStep, LiftError> {
    Ok(match v {
        LiteralValue::Bool(b) => LitStep::Ready(Const::Bool(*b)),
        LiteralValue::Integer8(n) => LitStep::Ready(Const::number(*n as f64)),
        LiteralValue::Integer(n) => LitStep::Ready(Const::number(*n as f64)),
        LiteralValue::Float(f) => LitStep::Ready(Const::number(*f as f64)),
        LiteralValue::Double(d) => LitStep::Ready(Const::number(*d)),
        LiteralValue::String(sid) | LiteralValue::EtsImplements(sid) => {
            let sym = lf
                .sym_of_file_sid(*sid)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            LitStep::Ready(Const::String(sym))
        }
        // Method references resolve offset → FuncId through the pass-1
        // method table (kind-precise identity, S1/N2).
        LiteralValue::Method(offset)
        | LiteralValue::GeneratorMethod(offset)
        | LiteralValue::AsyncGeneratorMethod(offset)
        | LiteralValue::Getter(offset)
        | LiteralValue::Setter(offset) => {
            LitStep::Ready(Const::MethodRef(func_of_offset(lf, *offset)?))
        }
        // Small numeric payloads with no dedicated Const variant
        // (accessor-kind tag, affiliate index, builtin-type index) —
        // content preserved as numbers (documented).
        LiteralValue::Accessor(n) => LitStep::Ready(Const::number(*n as f64)),
        LiteralValue::MethodAffiliate(n) => LitStep::Ready(Const::number(*n as f64)),
        LiteralValue::BuiltinTypeIndex(n) => LitStep::Ready(Const::number(*n as f64)),
        LiteralValue::NullValue(_) => LitStep::Ready(Const::Null),
        // Nested literal arrays: decode rewrites THIS variant's payload
        // to a table index (decode.rs "Rewrite nested references").
        LiteralValue::LiteralArray(idx) => LitStep::NestedArray(idx.0),
        // LiteralBufferIndex payloads are NOT rewritten by decode —
        // they are raw file offsets (same N52 class as the typed
        // arrays; corpus: sendable-class fixtures carry
        // `lit_offset:0x…` entries).
        LiteralValue::LiteralBufferIndex(raw) => {
            let idx = typed_array_table_index(lf.file, raw.0)
                .ok_or(LiftError::UnresolvedEntity(raw.0))?;
            LitStep::NestedArray(idx)
        }
        // Typed ARRAY_* payloads are RAW FILE OFFSETS in the v0.1 file
        // model (N52 — decode rewrites only `LiteralArray`); resolve
        // through the offset→index map. Hand-built models carry direct
        // indices instead: accept those as a fallback (documented).
        LiteralValue::ArrayU1(raw)
        | LiteralValue::ArrayU8(raw)
        | LiteralValue::ArrayI8(raw)
        | LiteralValue::ArrayU16(raw)
        | LiteralValue::ArrayI16(raw)
        | LiteralValue::ArrayU32(raw)
        | LiteralValue::ArrayI32(raw)
        | LiteralValue::ArrayU64(raw)
        | LiteralValue::ArrayI64(raw)
        | LiteralValue::ArrayF32(raw)
        | LiteralValue::ArrayF64(raw)
        | LiteralValue::ArrayString(raw) => {
            let idx = typed_array_table_index(lf.file, raw.0)
                .ok_or(LiftError::UnresolvedEntity(raw.0))?;
            // Element-type tag (u8/i32/f64/string…) is not part of
            // v0.2's Const — the elements carry their values; the tag
            // is a lowering concern (documented divergence).
            LitStep::NestedArray(idx)
        }
    })
}

/// Resolve a typed-array payload: raw file offset → literal-array table
/// index (N52), with a direct-index fallback for hand-built models.
fn typed_array_table_index(file: &File, raw: u32) -> Option<u32> {
    if let Some(&idx) = file.literal_array_offsets.get(&raw) {
        return Some(idx);
    }
    if (raw as usize) < file.literal_arrays.len() {
        return Some(raw);
    }
    None
}
