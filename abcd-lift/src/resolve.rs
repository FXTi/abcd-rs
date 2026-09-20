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
use abcd_ir2::{Const, ConstId, FuncId, Sym};
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

/// Convert the literal array at `table_idx` into a pooled shape
/// constant.
pub fn const_for_literal_array(lf: &mut Lifter, table_idx: u32) -> Result<ConstId, LiftError> {
    let tree = const_tree_for_literal_array(lf, table_idx)?;
    Ok(lf.const_shape(tree))
}

/// Convert the literal array at `table_idx` into its [`Const`] tree
/// (memoized, cycle-guarded). Literal shapes are inline TREES in v0.2's
/// constant pool — a nested array is embedded by value, so this returns
/// the tree itself rather than a pool reference.
fn const_tree_for_literal_array(lf: &mut Lifter, table_idx: u32) -> Result<Const, LiftError> {
    if let Some(tree) = lf.lit_cache.get(&table_idx) {
        return Ok(tree.clone());
    }
    if (table_idx as usize) >= lf.file.literal_arrays.len() {
        return Err(LiftError::LiteralArrayOutOfRange(table_idx));
    }
    if !lf.lit_active.insert(table_idx) {
        return Err(LiftError::LiteralArrayCycle(table_idx));
    }
    let result = (|| {
        let values = lf.file.literal_arrays[table_idx as usize].values.clone();
        let mut consts = Vec::with_capacity(values.len());
        for v in &values {
            consts.push(const_for_literal_value(lf, v)?);
        }
        Ok(Const::ArrayLiteral(consts))
    })();
    lf.lit_active.remove(&table_idx);
    let tree = result?;
    lf.lit_cache.insert(table_idx, tree.clone());
    Ok(tree)
}

/// Convert one literal value to a [`Const`] (N52: every reference is
/// resolved — no raw offsets cross into the IR).
pub(crate) fn const_for_literal_value(
    lf: &mut Lifter,
    v: &LiteralValue,
) -> Result<Const, LiftError> {
    Ok(match v {
        LiteralValue::Bool(b) => Const::Bool(*b),
        LiteralValue::Integer8(n) => Const::number(*n as f64),
        LiteralValue::Integer(n) => Const::number(*n as f64),
        LiteralValue::Float(f) => Const::number(*f as f64),
        LiteralValue::Double(d) => Const::number(*d),
        LiteralValue::String(sid) | LiteralValue::EtsImplements(sid) => {
            let sym = lf
                .sym_of_file_sid(*sid)
                .ok_or(LiftError::UnresolvedEntity(0))?;
            Const::String(sym)
        }
        // Method references resolve offset → FuncId through the pass-1
        // method table (kind-precise identity, S1/N2).
        LiteralValue::Method(offset)
        | LiteralValue::GeneratorMethod(offset)
        | LiteralValue::AsyncGeneratorMethod(offset)
        | LiteralValue::Getter(offset)
        | LiteralValue::Setter(offset) => Const::MethodRef(func_of_offset(lf, *offset)?),
        // Small numeric payloads with no dedicated Const variant
        // (accessor-kind tag, affiliate index, builtin-type index) —
        // content preserved as numbers (documented).
        LiteralValue::Accessor(n) => Const::number(*n as f64),
        LiteralValue::MethodAffiliate(n) => Const::number(*n as f64),
        LiteralValue::BuiltinTypeIndex(n) => Const::number(*n as f64),
        LiteralValue::NullValue(_) => Const::Null,
        // Nested literal arrays: decode rewrites THIS variant's payload
        // to a table index (decode.rs "Rewrite nested references").
        LiteralValue::LiteralArray(idx) => const_tree_for_literal_array(lf, idx.0)?,
        // LiteralBufferIndex payloads are NOT rewritten by decode —
        // they are raw file offsets (same N52 class as the typed
        // arrays; corpus: sendable-class fixtures carry
        // `lit_offset:0x…` entries).
        LiteralValue::LiteralBufferIndex(raw) => {
            let idx = typed_array_table_index(lf.file, raw.0)
                .ok_or(LiftError::UnresolvedEntity(raw.0))?;
            const_tree_for_literal_array(lf, idx)?
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
            const_tree_for_literal_array(lf, idx)?
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
