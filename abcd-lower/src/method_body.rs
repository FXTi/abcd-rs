//! Produce an encodable [`abcd_file::MethodBody`] from a lowered function.
//!
//! [`lower_function`](crate::lower_function) emits entity operands whose
//! raw values are module-scoped IR identities (never source-file offsets —
//! `design/ir.md` §1, `design/decisions.md` `ADR-01`):
//!
//! - `StringId` operands carry the raw [`Sym`] arena index;
//! - `MethodId` operands carry the module function-table index
//!   ([`FuncId`]) of the referenced method;
//! - `LiteralarrayId` operands carry the [`ConstId`] of the literal shape.
//!
//! `abcd_file::encode` first encodes `MethodBody.bytecodes` via
//! `abcd_isa::encode` (where every entity operand occupies a 16-bit `id:u16`
//! slot) and then relocates those slots through `MethodBody.entity_offsets`
//! (`(kind, local_id) → source-file offset`) and `Builder::relocate_code_id`.
//! Because module-wide [`Sym`] / [`FuncId`] / [`ConstId`] arenas in large
//! `--merge-abc` bundles routinely exceed `65,536` entries (#32),
//! `relocate_and_compact_entities` compacts each method's raw IR entity IDs
//! into deduplicated method-local `u16` indices (`0, 1, 2, …` per
//! [`EntityKind`] in first-appearance order) inside `MethodBody.bytecodes`
//! while keying `MethodBody.entity_offsets` by those same compacted `u16` IDs.
//! Source-file offsets are resolved by inverting `abcd-lift`'s forward
//! resolution in `resolve.rs`:
//!
//! - a [`Sym`] resolves by MUTF-8 CONTENT to a string-pool entity of the
//!   file (`File::entity_map`: offset → interned string). Several offsets
//!   may share one content; encode resolves string operands
//!   content-addressed, so any of them produces identical output — the
//!   smallest offset is chosen for determinism;
//! - a [`FuncId`] resolves by function-table position to the method's
//!   source-file offset (`File::all_methods()` order is the lift's
//!   function-table reservation order by construction);
//! - a [`ConstId`] literal shape resolves BY CONTENT to a literal-array
//!   table index (structural match mirroring `abcd-lift`'s
//!   `const_for_literal_value`), then to the array's source offset by
//!   inverting [`File::literal_array_offsets`]; the smallest matching
//!   table index is chosen for determinism.
//!
//! An entity that cannot be traced this way (a symbol with no
//! equal-content string in the file, an out-of-range function-table
//! index, a shape no literal array matches) is a hard
//! [`LowerError::UntraceableEntity`], and a single method referencing more
//! than `65,536` distinct entities of one kind is a hard
//! [`LowerError::EntityIndexOverflow`] — nothing is invented, truncated, or
//! passed through silently.

use std::collections::HashMap;

use abcd_file::{File, LiteralValue, MethodBody};
use abcd_ir::{Const, ConstId, FuncId, Module, Sym};
use abcd_isa::{Bytecode, EntityId, EntityKind};
use rayon::prelude::*;

use crate::layout::LayoutResult;
use crate::{LowerError, LowerOptions, lower_function_with_options};

/// Build an encodable [`MethodBody`] for a lowered function.
///
/// `file` is the source file the module was lifted from: it provides the
/// string table, the method table, and the literal-array table the IR
/// entities must resolve against.
///
/// When lowering an entire module, prefer constructing [`EntityResolver`]
/// once (or calling [`lower_module_bodies`]) rather than calling this
/// per-function wrapper in a loop (#29).
///
/// Every entity operand of every emitted bytecode must be traceable to a
/// source-file offset; otherwise [`LowerError::UntraceableEntity`] is
/// returned. There is no silent pass-through of untraceable operands.
pub fn to_method_body(
    module: &Module,
    func_id: FuncId,
    result: &LayoutResult,
    file: &File,
) -> Result<MethodBody, LowerError> {
    EntityResolver::new(module, file).to_method_body(func_id, result)
}

/// Lower every function in `module` in parallel and relocate its entity
/// operands through a single shared [`EntityResolver`] (#29).
///
/// Bodyless functions (`blocks.is_empty()`) yield `None`; errors are
/// deterministic (the lowest [`FuncId`]'s error wins, matching sequential
/// `0..module.functions.len()` lowering).
pub fn lower_module_bodies(
    module: &Module,
    file: &File,
    options: LowerOptions,
) -> Result<Vec<Option<MethodBody>>, LowerError> {
    let resolver = EntityResolver::new(module, file);
    let results: Vec<Result<Option<MethodBody>, LowerError>> = (0..module.functions.len())
        .into_par_iter()
        .map(|i| {
            let func_id = FuncId::new(i as u32);
            let Some(func) = module.func(func_id) else {
                return Ok(None);
            };
            if func.blocks.is_empty() {
                return Ok(None);
            }
            let layout = lower_function_with_options(module, func_id, options)?;
            let body = resolver.to_method_body(func_id, &layout)?;
            Ok(Some(body))
        })
        .collect();
    results.into_iter().collect()
}

/// Module-scoped reverse entity resolver: IR identities → source-file
/// offsets (`design/ir.md` §5, `ADR-10`).
///
/// Built once per `(Module, File)` pair and safe to share across threads
/// (`Sync`). All lookups (`string_offset`, `method_offset`,
/// `literal_array_offset`) run in `O(1)` amortized time.
pub struct EntityResolver<'a> {
    module: &'a Module,
    /// Canonical MUTF-8 wire bytes → smallest source offset of a string entity
    /// with those exact bytes (#30).
    string_offsets: HashMap<Box<[u8]>, u32>,
    /// Function-table position → method source offset (`all_methods()`
    /// order = the lift's reservation order).
    method_offsets: Vec<u32>,
    /// Literal-array table index → source offset (inverted
    /// `literal_array_offsets`).
    literal_index_to_offset: HashMap<u32, u32>,
    /// Canonical `Const::ArrayLiteral` shape → smallest matching
    /// literal-array table index.
    shape_to_min_index: HashMap<Const, u32>,
}

impl<'a> EntityResolver<'a> {
    /// Index `file`'s string, method, and literal-array tables once for
    /// `module`.
    pub fn new(module: &'a Module, file: &File) -> Self {
        let mut string_offsets: HashMap<Box<[u8]>, u32> =
            HashMap::with_capacity(file.entity_map.len());
        // Smallest offset wins on duplicate content (encode resolves
        // string operands content-addressed, so any valid entry produces
        // identical output; the choice only needs to be deterministic).
        let mut entries: Vec<(u32, abcd_file::StringId)> =
            file.entity_map.iter().map(|(&o, &s)| (o, s)).collect();
        entries.sort_unstable();
        for (offset, sid) in entries {
            if let Some(bytes) = file.strings.to_mutf8_bytes(sid) {
                string_offsets
                    .entry(bytes.into_owned().into_boxed_slice())
                    .or_insert(offset);
            }
        }
        let method_offsets: Vec<u32> = file.all_methods().map(|(_, m)| m.offset).collect();
        let mut method_offset_to_index: HashMap<u32, u32> =
            HashMap::with_capacity(method_offsets.len());
        for (i, &off) in method_offsets.iter().enumerate() {
            method_offset_to_index.entry(off).or_insert(i as u32);
        }
        let literal_index_to_offset: HashMap<u32, u32> = file
            .literal_array_offsets
            .iter()
            .map(|(&offset, &index)| (index, offset))
            .collect();

        let mut shape_to_min_index: HashMap<Const, u32> =
            HashMap::with_capacity(file.literal_arrays.len());
        let mut cache: Vec<Option<Option<Const>>> = vec![None; file.literal_arrays.len()];
        for idx in 0..file.literal_arrays.len() as u32 {
            if let Some(shape) =
                build_literal_array_const(module, file, &method_offset_to_index, &mut cache, idx)
            {
                shape_to_min_index.entry(shape).or_insert(idx);
            }
        }

        Self {
            module,
            string_offsets,
            method_offsets,
            literal_index_to_offset,
            shape_to_min_index,
        }
    }

    /// Relocate a lowered function's [`LayoutResult`] into an encodable
    /// [`MethodBody`].
    pub fn to_method_body(
        &self,
        func_id: FuncId,
        result: &LayoutResult,
    ) -> Result<MethodBody, LowerError> {
        let param_count = self
            .module
            .func(func_id)
            .map(|f| f.params.len())
            .unwrap_or_default();

        let (bytecodes, entity_offsets) =
            relocate_and_compact_entities(func_id, &result.bytecodes, |kind, raw| match kind {
                EntityKind::StringId => {
                    self.string_offset(Sym::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
                EntityKind::MethodId => {
                    self.method_offset(FuncId::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
                EntityKind::LiteralarrayId => self.literal_array_offset(ConstId::new(raw)).ok_or(
                    LowerError::UntraceableEntity {
                        func: func_id,
                        kind,
                        raw,
                    },
                ),
            })?;

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            bytecodes,
            entity_offsets,
            try_blocks: result.try_blocks.clone(),
            ic_size: Some(result.ic_size),
        })
    }

    /// [`Sym`] → source offset of an equal-MUTF-8-content string entity.
    pub(crate) fn string_offset(&self, sym: Sym) -> Option<u32> {
        let bytes = self.module.sym.to_mutf8_bytes(sym)?;
        self.string_offsets.get(bytes.as_ref()).copied()
    }

    /// [`FuncId`] → source offset of the method at that function-table
    /// position.
    pub(crate) fn method_offset(&self, func: FuncId) -> Option<u32> {
        self.method_offsets.get(func.index()).copied()
    }

    /// [`ConstId`] (a literal shape) → source offset of the smallest
    /// literal-array table entry whose content matches the shape.
    pub(crate) fn literal_array_offset(&self, shape: ConstId) -> Option<u32> {
        let tree = self.module.consts.get(shape)?;
        let &index = self.shape_to_min_index.get(tree)?;
        self.literal_index_to_offset.get(&index).copied()
    }
}

/// Explicit stack frame for iterative literal-array shape conversion.
struct LitArrayFrame {
    idx_usize: usize,
    depth: u32,
    next_elem: usize,
    items: Vec<Const>,
}

/// Convert `file.literal_arrays[table_idx]` into its canonical [`Const`]
/// shape (the exact inverse of `abcd-lift`'s `const_for_literal_array`)
/// using an explicit stack (zero recursion), returning `None` if any
/// element uses an uninterned string, unknown method offset, non-shape
/// literal tag, cycle, or nesting depth > 64.
fn build_literal_array_const(
    module: &Module,
    file: &File,
    method_offset_to_index: &HashMap<u32, u32>,
    cache: &mut [Option<Option<Const>>],
    table_idx: u32,
) -> Option<Const> {
    let root_usize = table_idx as usize;
    let root_la = file.literal_arrays.get(root_usize)?;
    // Memoize depth-valid conversions (`None` inside `Some(None)` marks
    // either an active cycle or a permanently non-representable array).
    if let Some(cached) = &cache[root_usize] {
        return cached.clone();
    }
    cache[root_usize] = Some(None);
    let mut stack = vec![LitArrayFrame {
        idx_usize: root_usize,
        depth: 0,
        next_elem: 0,
        items: Vec::with_capacity(root_la.values.len()),
    }];

    'outer: while let Some(mut frame) = stack.pop() {
        while frame.next_elem < file.literal_arrays[frame.idx_usize].values.len() {
            let v = &file.literal_arrays[frame.idx_usize].values[frame.next_elem];
            frame.next_elem += 1;
            let nested_idx = match v {
                LiteralValue::LiteralArray(idx) => Some(idx.0),
                LiteralValue::LiteralBufferIndex(raw)
                | LiteralValue::ArrayU1(raw)
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
                | LiteralValue::ArrayString(raw) => Some(typed_array_table_index(file, raw.0)?),
                _ => None,
            };
            if let Some(child_idx) = nested_idx {
                let child_depth = frame.depth + 1;
                if child_depth > 64 {
                    return None;
                }
                let child_usize = child_idx as usize;
                let child_la = file.literal_arrays.get(child_usize)?;
                if let Some(cached) = &cache[child_usize] {
                    frame.items.push(cached.clone()?);
                } else {
                    cache[child_usize] = Some(None);
                    let child_cap = child_la.values.len();
                    stack.push(frame);
                    stack.push(LitArrayFrame {
                        idx_usize: child_usize,
                        depth: child_depth,
                        next_elem: 0,
                        items: Vec::with_capacity(child_cap),
                    });
                    continue 'outer;
                }
            } else {
                frame.items.push(scalar_literal_value_const(
                    module,
                    file,
                    method_offset_to_index,
                    v,
                )?);
            }
        }

        let out = Const::ArrayLiteral(frame.items);
        cache[frame.idx_usize] = Some(Some(out.clone()));
        if let Some(parent) = stack.last_mut() {
            parent.items.push(out);
        } else {
            return Some(out);
        }
    }
    None
}

fn scalar_literal_value_const(
    module: &Module,
    file: &File,
    method_offset_to_index: &HashMap<u32, u32>,
    v: &LiteralValue,
) -> Option<Const> {
    match v {
        LiteralValue::Bool(vb) => Some(Const::Bool(*vb)),
        LiteralValue::Integer8(n) => Some(Const::Number((*n as f64).to_bits())),
        LiteralValue::Integer(n) => Some(Const::Number((*n as f64).to_bits())),
        LiteralValue::Float(x) => Some(Const::Number((*x as f64).to_bits())),
        LiteralValue::Double(x) => Some(Const::Number(x.to_bits())),
        LiteralValue::Accessor(n) => Some(Const::Number(f64::from(*n).to_bits())),
        LiteralValue::MethodAffiliate(n) => Some(Const::Number(f64::from(*n).to_bits())),
        LiteralValue::BuiltinTypeIndex(n) => Some(Const::Number(f64::from(*n).to_bits())),
        LiteralValue::String(sid) | LiteralValue::EtsImplements(sid) => {
            if let Some(raw) = file.strings.raw_mutf8(*sid) {
                module.sym.get_raw_mutf8(raw).map(Const::String)
            } else {
                file.strings
                    .as_str(*sid)
                    .and_then(|s| module.sym.get(s))
                    .map(Const::String)
            }
        }
        LiteralValue::Method(off)
        | LiteralValue::GeneratorMethod(off)
        | LiteralValue::AsyncGeneratorMethod(off)
        | LiteralValue::Getter(off)
        | LiteralValue::Setter(off) => method_offset_to_index
            .get(off)
            .map(|&idx| Const::MethodRef(FuncId::new(idx))),
        LiteralValue::NullValue(_) => Some(Const::Null),
        LiteralValue::LiteralArray(_)
        | LiteralValue::LiteralBufferIndex(_)
        | LiteralValue::ArrayU1(_)
        | LiteralValue::ArrayU8(_)
        | LiteralValue::ArrayI8(_)
        | LiteralValue::ArrayU16(_)
        | LiteralValue::ArrayI16(_)
        | LiteralValue::ArrayU32(_)
        | LiteralValue::ArrayI32(_)
        | LiteralValue::ArrayU64(_)
        | LiteralValue::ArrayI64(_)
        | LiteralValue::ArrayF32(_)
        | LiteralValue::ArrayF64(_)
        | LiteralValue::ArrayString(_) => None,
    }
}

fn typed_array_table_index(file: &File, raw: u32) -> Option<u32> {
    if let Some(&idx) = file.literal_array_offsets.get(&raw) {
        return Some(idx);
    }
    if (raw as usize) < file.literal_arrays.len() {
        return Some(raw);
    }
    None
}

/// Method-local `(EntityKind, u16_local_id) → source-file offset` relocation map.
pub(crate) type EntityOffsetMap = HashMap<(EntityKind, u32), u32>;

/// Resolve every entity operand in `bytecodes` through `resolve` and compact
/// module-global `EntityId(u32)` values into method-local `u16` placeholder
/// indices (`0, 1, 2, …` per [`EntityKind`] in first-appearance order, #32).
///
/// `abcd_isa::encode` encodes entity operands into 16-bit `id:u16` fields
/// before `abcd_file::encode` rewrites them from `MethodBody.entity_offsets`,
/// so leaving module-global `Sym` / `FuncId` / `ConstId` values (`>= 65,536` on
/// large merged bundles) in `MethodBody.bytecodes` fails bytecode encoding.
pub(crate) fn relocate_and_compact_entities(
    func_id: FuncId,
    bytecodes: &[Bytecode],
    mut resolve: impl FnMut(EntityKind, u32) -> Result<u32, LowerError>,
) -> Result<(Vec<Bytecode>, EntityOffsetMap), LowerError> {
    let mut out_bytecodes = bytecodes.to_vec();
    let mut entity_offsets: EntityOffsetMap = HashMap::new();
    let mut local_ids: HashMap<(EntityKind, u32), u16> = HashMap::new();
    let mut next_string: u32 = 0;
    let mut next_method: u32 = 0;
    let mut next_literal: u32 = 0;

    for bc in &mut out_bytecodes {
        let expected_len = bc.entity_operands().len();
        let mut visited = 0usize;
        for_each_entity_operand_mut(bc, |kind, id_mut| {
            visited += 1;
            let raw = id_mut.0;
            let local_id = if let Some(&existing) = local_ids.get(&(kind, raw)) {
                existing
            } else {
                let offset = resolve(kind, raw)?;
                let counter = match kind {
                    EntityKind::StringId => &mut next_string,
                    EntityKind::MethodId => &mut next_method,
                    EntityKind::LiteralarrayId => &mut next_literal,
                };
                let assigned = u16::try_from(*counter)
                    .map_err(|_| LowerError::EntityIndexOverflow(func_id))?;
                *counter += 1;
                local_ids.insert((kind, raw), assigned);
                entity_offsets.insert((kind, u32::from(assigned)), offset);
                assigned
            };
            *id_mut = EntityId(u32::from(local_id));
            Ok(())
        })?;
        debug_assert_eq!(
            visited,
            expected_len,
            "for_each_entity_operand_mut out of sync with Bytecode::entity_operands for {}",
            bc.mnemonic()
        );
        debug_assert_eq!(bc.entity_operands().len(), expected_len);
    }

    Ok((out_bytecodes, entity_offsets))
}

/// Visit every [`EntityId`] operand of `bc` mutably in ISA signature order,
/// matching `abcd_isa::Bytecode::entity_operands` across all 44 entity-bearing
/// bytecode variants (including dual-entity class-definition instructions).
fn for_each_entity_operand_mut(
    bc: &mut Bytecode,
    mut f: impl FnMut(EntityKind, &mut EntityId) -> Result<(), LowerError>,
) -> Result<(), LowerError> {
    match bc {
        Bytecode::Createarraywithbuffer(_, id1)
        | Bytecode::Createobjectwithbuffer(_, id1)
        | Bytecode::Newlexenvwithname(_, id1)
        | Bytecode::WideNewlexenvwithname(_, id1)
        | Bytecode::CallruntimeCreateprivateproperty(_, id1) => {
            f(EntityKind::LiteralarrayId, id1)?;
        }
        Bytecode::Definefunc(_, id1, _)
        | Bytecode::Definemethod(_, id1, _)
        | Bytecode::DeprecatedDefineclasswithbuffer(id1, _, _, _, _) => {
            f(EntityKind::MethodId, id1)?;
        }
        Bytecode::Defineclasswithbuffer(_, id1, id2, _, _)
        | Bytecode::CallruntimeDefinesendableclass(_, id1, id2, _, _) => {
            f(EntityKind::MethodId, id1)?;
            f(EntityKind::LiteralarrayId, id2)?;
        }
        Bytecode::LdaStr(id0)
        | Bytecode::Tryldglobalbyname(_, id0)
        | Bytecode::Trystglobalbyname(_, id0)
        | Bytecode::Ldglobalvar(_, id0)
        | Bytecode::Ldobjbyname(_, id0)
        | Bytecode::Stobjbyname(_, id0, _)
        | Bytecode::Ldsuperbyname(_, id0)
        | Bytecode::Stconsttoglobalrecord(_, id0)
        | Bytecode::Sttoglobalrecord(_, id0)
        | Bytecode::Ldthisbyname(_, id0)
        | Bytecode::Stthisbyname(_, id0)
        | Bytecode::Createregexpwithliteral(_, id0, _)
        | Bytecode::Stownbyname(_, id0, _)
        | Bytecode::Stglobalvar(_, id0)
        | Bytecode::Stownbynamewithnameset(_, id0, _)
        | Bytecode::Stsuperbyname(_, id0, _)
        | Bytecode::Ldbigint(id0)
        | Bytecode::Definefieldbyname(_, id0, _)
        | Bytecode::Definepropertybyname(_, id0, _)
        | Bytecode::Callthis0withname(_, id0, _)
        | Bytecode::Callthis1withname(_, id0, _, _)
        | Bytecode::Callthis2withname(_, id0, _, _, _)
        | Bytecode::Callthis3withname(_, id0, _, _, _, _)
        | Bytecode::Callthisrangewithname(_, _, id0, _)
        | Bytecode::ThrowUndefinedifholewithname(id0)
        | Bytecode::WideCallthisrangewithname(_, id0, _)
        | Bytecode::DeprecatedGetmodulenamespace(id0)
        | Bytecode::DeprecatedStmodulevar(id0)
        | Bytecode::DeprecatedLdobjbyname(id0, _)
        | Bytecode::DeprecatedLdsuperbyname(id0, _)
        | Bytecode::DeprecatedLdmodulevar(id0, _)
        | Bytecode::DeprecatedStconsttoglobalrecord(id0)
        | Bytecode::DeprecatedStlettoglobalrecord(id0)
        | Bytecode::DeprecatedStclasstoglobalrecord(id0) => {
            f(EntityKind::StringId, id0)?;
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use abcd_isa::{Imm, Reg};

    #[test]
    fn all_44_entity_bytecode_variants_compact_above_u16_and_encode() {
        let hi_a = EntityId(70_000);
        let hi_b = EntityId(80_000);
        let r = Reg(0);
        let imm = Imm(0);
        let sample = vec![
            Bytecode::Createarraywithbuffer(imm, hi_a),
            Bytecode::Createobjectwithbuffer(imm, hi_a),
            Bytecode::Definefunc(imm, hi_a, imm),
            Bytecode::Definemethod(imm, hi_a, imm),
            Bytecode::Defineclasswithbuffer(imm, hi_a, hi_b, imm, r),
            Bytecode::LdaStr(hi_a),
            Bytecode::Tryldglobalbyname(imm, hi_a),
            Bytecode::Trystglobalbyname(imm, hi_a),
            Bytecode::Ldglobalvar(imm, hi_a),
            Bytecode::Ldobjbyname(imm, hi_b),
            Bytecode::Stobjbyname(imm, hi_a, r),
            Bytecode::Ldsuperbyname(imm, hi_a),
            Bytecode::Stconsttoglobalrecord(imm, hi_a),
            Bytecode::Sttoglobalrecord(imm, hi_a),
            Bytecode::Ldthisbyname(imm, hi_a),
            Bytecode::Stthisbyname(imm, hi_a),
            Bytecode::Createregexpwithliteral(imm, hi_a, imm),
            Bytecode::Stownbyname(imm, hi_a, r),
            Bytecode::Stglobalvar(imm, hi_a),
            Bytecode::Stownbynamewithnameset(imm, hi_a, r),
            Bytecode::Newlexenvwithname(imm, hi_b),
            Bytecode::Stsuperbyname(imm, hi_a, r),
            Bytecode::Ldbigint(hi_a),
            Bytecode::Definefieldbyname(imm, hi_a, r),
            Bytecode::Definepropertybyname(imm, hi_a, r),
            Bytecode::Callthis0withname(imm, hi_a, r),
            Bytecode::Callthis1withname(imm, hi_a, r, r),
            Bytecode::Callthis2withname(imm, hi_a, r, r, r),
            Bytecode::Callthis3withname(imm, hi_a, r, r, r, r),
            Bytecode::Callthisrangewithname(imm, imm, hi_a, r),
            Bytecode::WideNewlexenvwithname(imm, hi_a),
            Bytecode::CallruntimeCreateprivateproperty(imm, hi_a),
            Bytecode::CallruntimeDefinesendableclass(imm, hi_b, hi_a, imm, r),
            Bytecode::ThrowUndefinedifholewithname(hi_a),
            Bytecode::DeprecatedDefineclasswithbuffer(hi_a, imm, imm, r, r),
            Bytecode::WideCallthisrangewithname(imm, hi_a, r),
            Bytecode::DeprecatedGetmodulenamespace(hi_a),
            Bytecode::DeprecatedStmodulevar(hi_a),
            Bytecode::DeprecatedLdobjbyname(hi_a, r),
            Bytecode::DeprecatedLdsuperbyname(hi_a, r),
            Bytecode::DeprecatedLdmodulevar(hi_a, imm),
            Bytecode::DeprecatedStconsttoglobalrecord(hi_a),
            Bytecode::DeprecatedStlettoglobalrecord(hi_a),
            Bytecode::DeprecatedStclasstoglobalrecord(hi_a),
        ];
        assert_eq!(sample.len(), 44);

        let (compacted, offsets) =
            relocate_and_compact_entities(FuncId::new(0), &sample, |_kind, raw| Ok(raw + 0x1000))
                .expect("compaction must succeed");
        for bc in &compacted {
            for (kind, id) in bc.entity_operands() {
                assert!(id.0 <= u32::from(u16::MAX), "uncompacted operand in {bc:?}");
                assert!(offsets.contains_key(&(kind, id.0)));
            }
        }
        abcd_isa::encode(&compacted).expect("all compacted entity instructions must encode");
    }

    #[test]
    fn entity_index_overflow_above_65536_distinct_in_one_method_errors_loudly() {
        let bytecodes: Vec<Bytecode> = (0..=u32::from(u16::MAX) + 1)
            .map(|i| Bytecode::LdaStr(EntityId(i)))
            .collect();
        let err = relocate_and_compact_entities(FuncId::new(7), &bytecodes, |_, raw| Ok(raw + 1))
            .expect_err("65537 distinct strings in one method must overflow u16");
        assert!(matches!(err, LowerError::EntityIndexOverflow(f) if f == FuncId::new(7)));
    }
}
