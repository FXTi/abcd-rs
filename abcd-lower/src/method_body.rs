//! Produce an encodable [`abcd_file::MethodBody`] from a lowered function.
//!
//! [`lower_function`](crate::lower_function) emits entity operands whose
//! raw values are module-scoped IR identities (never source-file offsets —
//! `design/ir.md` §1, `design/decisions.md` `ADR-01`, `#50` `R3-D2`):
//!
//! - `StringId` operands carry the raw [`Sym`] arena index;
//! - `MethodId` operands carry the module function-table index
//!   ([`FuncId`]) of the referenced method;
//! - `LiteralarrayId` operands carry the [`ConstId`] of the literal shape.
//!
//! `abcd_file::encode` first encodes `MethodBody.bytecodes` via
//! `abcd_isa::encode` (where every entity operand occupies a 16-bit `id:u16`
//! slot) and then relocates those slots through `MethodBody.entities`
//! (`(kind, local_id) → EntityRef`) and `Builder::relocate_code_id`.
//! Because module-wide [`Sym`] / [`FuncId`] / [`ConstId`] arenas in large
//! `--merge-abc` bundles routinely exceed `65,536` entries (#32),
//! `relocate_and_compact_entities` compacts each method's raw IR entity IDs
//! into deduplicated method-local `u16` indices (`0, 1, 2, …` per
//! [`EntityKind`] in first-appearance order) inside `MethodBody.bytecodes`
//! while keying `MethodBody.entities` by those same compacted `u16` IDs:
//!
//! - a [`Sym`] resolves by MUTF-8 CONTENT to an interned [`abcd_file::StringId`]
//!   of the file (`EntityRef::String`), preserving optional wire
//!   `source_offset` provenance when present on existing method bodies;
//! - a [`FuncId`] resolves by function-table position to its dense
//!   [`abcd_file::MethodIdx`] (`File::all_methods()` order is the lift's
//!   function-table reservation order by construction);
//! - a [`ConstId`] literal shape resolves BY TAG-EXACT CONTENT (`#57` `R3-H9`)
//!   to the smallest matching [`abcd_file::LiteralArrayIdx`] via a flat,
//!   hash-consed shape interner (`O(N)` time, `O(1)` call stack).
//!
//! An entity that cannot be traced this way (a symbol with no equal-content
//! string in the file, an out-of-range function-table index, a shape no
//! literal array matches, or an untraceable catch exception class) is a hard
//! [`LowerError::UntraceableEntity`], a single method referencing more than
//! `65,536` distinct entities of one kind is a hard
//! [`LowerError::EntityIndexOverflow`], and any ISA/visitor operand-count
//! mismatch is a release-active [`LowerError::EntityOperandMismatch`] (`R3-M9`).

use std::collections::{HashMap, HashSet};

use abcd_file::{
    CatchBlock, EntityRef, File, LiteralArrayIdx, LiteralValue, MethodBody, MethodIdx, StringId,
    TryBlock,
};
use abcd_ir::{Const, ConstId, FuncId, LitMethodKind, Module, Sym, TypedArrayTag};
use abcd_isa::{Bytecode, EntityId, EntityKind};
use rayon::prelude::*;

use crate::layout::{LayoutResult, LoweredTryBlock};
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
/// file entity; otherwise [`LowerError::UntraceableEntity`] is returned.
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

/// Hash-consed flat shape identifier (eliminates recursive `Drop`, `Hash`, and
/// `PartialEq` across arbitrarily deep nested literal arrays).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ShapeId(u32);

/// Tag-exact, non-recursive canonical element of a literal-array shape (`#57`
/// `R3-H9`), keeping `Integer8` / `Integer` / `Float` / `Double` / `Accessor` /
/// `MethodAffiliate` / `BuiltinTypeIndex` / `EtsImplements` / `LitMethodKind` /
/// `LiteralBufferIndex` / `TypedArrayTag` distinct.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum FlatLitElem {
    Bool(bool),
    Int8(u8),
    Int32(u32),
    Float32(u32),
    Double(u64),
    String(Sym),
    EtsImplements(Sym),
    MethodRef { func: FuncId, kind: LitMethodKind },
    Accessor(u8),
    MethodAffiliate(u16),
    BuiltinTypeIndex(u8),
    LitNull(u8),
    Array(ShapeId),
    LiteralBufferRef(ShapeId),
    ArrayU1(Vec<bool>),
    ArrayU8(Vec<u8>),
    ArrayI8(Vec<i8>),
    ArrayU16(Vec<u16>),
    ArrayI16(Vec<i16>),
    ArrayU32(Vec<u32>),
    ArrayI32(Vec<i32>),
    ArrayU64(Vec<u64>),
    ArrayI64(Vec<i64>),
    ArrayF32(Vec<u32>),
    ArrayF64(Vec<u64>),
    ArrayString(Vec<Sym>),
}

/// Module-scoped reverse entity resolver: IR identities → [`EntityRef`]
/// handles (`design/ir.md` §5, `ADR-10`, `#50` `R3-D2`).
///
/// Built once per `(Module, File)` pair and safe to share across threads
/// (`Sync`). Lookups run in `O(1)` amortized time for strings and methods and
/// `O(shape_size)` iterative bottom-up hash-consing for literal shapes.
pub struct EntityResolver<'a> {
    module: &'a Module,
    /// Canonical MUTF-8 wire bytes → first [`StringId`] in `file.strings` (#30).
    string_ids: HashMap<Box<[u8]>, StringId>,
    /// Optional wire `source_offset` provenance preserved from existing
    /// `MethodBody::entities` entries (smallest offset wins deterministically).
    string_source_offsets: HashMap<StringId, u32>,
    /// Total method count in `file.all_methods()` (`FuncId` reservation bound).
    method_count: usize,
    /// Hash-consed flat element sequence → canonical [`ShapeId`].
    shape_interner: HashMap<Vec<FlatLitElem>, ShapeId>,
    /// Canonical [`ShapeId`] → smallest matching [`LiteralArrayIdx`] in `file`.
    shape_to_min_index: HashMap<ShapeId, LiteralArrayIdx>,
}

impl<'a> EntityResolver<'a> {
    /// Index `file`'s string, method, and literal-array tables once for
    /// `module`.
    pub fn new(module: &'a Module, file: &File) -> Self {
        let mut string_ids: HashMap<Box<[u8]>, StringId> =
            HashMap::with_capacity(file.strings.len());
        for i in 0..file.strings.len() {
            let sid = StringId::new(i as u32);
            if let Some(bytes) = file.strings.to_mutf8_bytes(sid) {
                string_ids
                    .entry(bytes.into_owned().into_boxed_slice())
                    .or_insert(sid);
            }
        }

        let mut string_source_offsets: HashMap<StringId, u32> = HashMap::new();
        let mut method_count = 0usize;
        for (_, method) in file.all_methods() {
            method_count += 1;
            if let Some(body) = &method.body {
                for entity in body.entities.values() {
                    if let EntityRef::String {
                        id,
                        source_offset: Some(off),
                    } = *entity
                    {
                        string_source_offsets
                            .entry(id)
                            .and_modify(|cur| *cur = (*cur).min(off))
                            .or_insert(off);
                    }
                }
            }
        }

        let num_lits = file.literal_arrays.len();
        let mut shape_interner: HashMap<Vec<FlatLitElem>, ShapeId> =
            HashMap::with_capacity(num_lits);
        let mut shape_to_min_index: HashMap<ShapeId, LiteralArrayIdx> =
            HashMap::with_capacity(num_lits);
        // `0` = unvisited, `1` = active on workstack, `2` = finished (`resolved` holds result).
        let mut state: Vec<u8> = vec![0; num_lits];
        let mut resolved: Vec<Option<ShapeId>> = vec![None; num_lits];

        for idx in 0..num_lits as u32 {
            if let Some(shape_id) = intern_file_literal_array(
                module,
                file,
                method_count,
                &mut state,
                &mut resolved,
                &mut shape_interner,
                idx,
            ) {
                shape_to_min_index
                    .entry(shape_id)
                    .or_insert(LiteralArrayIdx(idx));
            }
        }

        Self {
            module,
            string_ids,
            string_source_offsets,
            method_count,
            shape_interner,
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

        let (bytecodes, entities) =
            relocate_and_compact_entities(func_id, &result.bytecodes, |kind, raw| match kind {
                EntityKind::StringId => {
                    self.string_ref(Sym::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
                EntityKind::MethodId => {
                    self.method_ref(FuncId::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
                EntityKind::LiteralarrayId => {
                    self.literal_array_ref(ConstId::new(raw))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw,
                        })
                }
            })?;

        let try_blocks = self.resolve_try_blocks(&result.try_blocks, func_id)?;

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            bytecodes,
            entities,
            try_blocks,
            ic_size: Some(result.ic_size),
        })
    }

    /// [`Sym`] → interned [`StringId`] in `file.strings` matching exact MUTF-8 wire bytes.
    pub(crate) fn string_id(&self, sym: Sym) -> Option<StringId> {
        let bytes = self.module.sym.to_mutf8_bytes(sym)?;
        self.string_ids.get(bytes.as_ref()).copied()
    }

    /// [`Sym`] → [`EntityRef::String`] carrying preserved `source_offset` when known.
    pub(crate) fn string_ref(&self, sym: Sym) -> Option<EntityRef> {
        let id = self.string_id(sym)?;
        Some(EntityRef::String {
            id,
            source_offset: self.string_source_offsets.get(&id).copied(),
        })
    }

    /// [`FuncId`] → [`EntityRef::Method`] at that dense function-table index.
    pub(crate) fn method_ref(&self, func: FuncId) -> Option<EntityRef> {
        (func.index() < self.method_count).then_some(EntityRef::Method(MethodIdx(func.0)))
    }

    /// [`ConstId`] (a literal shape) → smallest matching [`LiteralArrayIdx`] in `file`.
    pub(crate) fn literal_array_idx(&self, shape: ConstId) -> Option<LiteralArrayIdx> {
        let shape_id = canonicalize_const_shape(self.module, &self.shape_interner, shape)?;
        self.shape_to_min_index.get(&shape_id).copied()
    }

    /// [`ConstId`] (a literal shape) → [`EntityRef::LiteralArray`].
    pub(crate) fn literal_array_ref(&self, shape: ConstId) -> Option<EntityRef> {
        self.literal_array_idx(shape).map(EntityRef::LiteralArray)
    }

    /// Convert [`LoweredTryBlock`]s (`ClassId` catch types) into container
    /// [`TryBlock`]s (`StringId` class descriptors).
    pub(crate) fn resolve_try_blocks(
        &self,
        lowered: &[LoweredTryBlock],
        func_id: FuncId,
    ) -> Result<Vec<TryBlock>, LowerError> {
        let mut out = Vec::with_capacity(lowered.len());
        for tb in lowered {
            let mut catches = Vec::with_capacity(tb.catches.len());
            for c in &tb.catches {
                let type_class = match c.type_class {
                    None => None,
                    Some(cid) => {
                        let cls = self
                            .module
                            .class(cid)
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind: EntityKind::StringId,
                                raw: cid.0,
                            })?;
                        let sid = self.string_id(cls.descriptor).ok_or(
                            LowerError::UntraceableEntity {
                                func: func_id,
                                kind: EntityKind::StringId,
                                raw: cls.descriptor.0,
                            },
                        )?;
                        Some(sid)
                    }
                };
                catches.push(CatchBlock {
                    type_class,
                    handler: c.handler,
                    len: c.len,
                });
            }
            out.push(TryBlock {
                start: tb.start,
                len: tb.len,
                catches,
            });
        }
        Ok(out)
    }
}

/// Wrapper kind when pushing a nested shape child onto the explicit workstack.
#[derive(Clone, Copy)]
enum NestedShapeWrap {
    Array,
    BufferRef { wrapper_cid: ConstId },
}

enum ConstShapeCursor<'m> {
    Array {
        items: &'m [ConstId],
        next: usize,
    },
    Object {
        keys: &'m [ConstId],
        values: &'m [ConstId],
        next: usize,
    },
}

impl<'m> ConstShapeCursor<'m> {
    fn from_const(c: &'m Const) -> Option<(Self, usize)> {
        match c {
            Const::ArrayLiteral(items) => Some((Self::Array { items, next: 0 }, items.len())),
            Const::ObjectLiteral { keys, values } if keys.len() == values.len() => Some((
                Self::Object {
                    keys,
                    values,
                    next: 0,
                },
                keys.len() * 2,
            )),
            _ => None,
        }
    }

    fn next_id(&mut self) -> Option<ConstId> {
        match self {
            Self::Array { items, next } => {
                let id = *items.get(*next)?;
                *next += 1;
                Some(id)
            }
            Self::Object { keys, values, next } => {
                let pair_idx = *next / 2;
                let id = if *next % 2 == 0 {
                    *keys.get(pair_idx)?
                } else {
                    *values.get(pair_idx)?
                };
                *next += 1;
                Some(id)
            }
        }
    }
}

struct ConstShapeFrame<'m> {
    cid: ConstId,
    parent_wrap: Option<NestedShapeWrap>,
    cursor: ConstShapeCursor<'m>,
    items: Vec<FlatLitElem>,
}

fn wrap_flat_elem(wrap: NestedShapeWrap, id: ShapeId) -> FlatLitElem {
    match wrap {
        NestedShapeWrap::Array => FlatLitElem::Array(id),
        NestedShapeWrap::BufferRef { .. } => FlatLitElem::LiteralBufferRef(id),
    }
}

/// Convert a homogeneous [`Const::TypedArrayLiteral`] into its tag-exact
/// [`FlatLitElem::Array*`] payload.
fn const_typed_array_elems(
    module: &Module,
    tag: TypedArrayTag,
    items: &[ConstId],
) -> Option<FlatLitElem> {
    match tag {
        TypedArrayTag::U1 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let b = match module.consts.get(cid)? {
                    Const::Bool(b) => *b,
                    Const::Int8(n) if *n <= 1 => *n != 0,
                    Const::Int32(n) if *n <= 1 => *n != 0,
                    _ => return None,
                };
                out.push(b);
            }
            Some(FlatLitElem::ArrayU1(out))
        }
        TypedArrayTag::U8 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => *n,
                    Const::Int32(n) => u8::try_from(*n).ok()?,
                    Const::UInt64(n) => u8::try_from(*n).ok()?,
                    Const::Int64(n) => u8::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayU8(out))
        }
        TypedArrayTag::I8 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => *n as i8,
                    Const::Int32(n) => i8::try_from(*n as i32).ok()?,
                    Const::Int64(n) => i8::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayI8(out))
        }
        TypedArrayTag::U16 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => u16::from(*n),
                    Const::Int32(n) => u16::try_from(*n).ok()?,
                    Const::UInt64(n) => u16::try_from(*n).ok()?,
                    Const::Int64(n) => u16::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayU16(out))
        }
        TypedArrayTag::I16 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => i16::from(*n as i8),
                    Const::Int32(n) => i16::try_from(*n as i32).ok()?,
                    Const::Int64(n) => i16::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayI16(out))
        }
        TypedArrayTag::U32 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => u32::from(*n),
                    Const::Int32(n) => *n,
                    Const::UInt64(n) => u32::try_from(*n).ok()?,
                    Const::Int64(n) => u32::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayU32(out))
        }
        TypedArrayTag::I32 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int8(n) => i32::from(*n as i8),
                    Const::Int32(n) => *n as i32,
                    Const::Int64(n) => i32::try_from(*n).ok()?,
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayI32(out))
        }
        TypedArrayTag::U64 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::UInt64(n) => *n,
                    Const::Int64(n) => u64::try_from(*n).ok()?,
                    Const::Int32(n) => u64::from(*n),
                    Const::Int8(n) => u64::from(*n),
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayU64(out))
        }
        TypedArrayTag::I64 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let v = match module.consts.get(cid)? {
                    Const::Int64(n) => *n,
                    Const::UInt64(n) => i64::try_from(*n).ok()?,
                    Const::Int32(n) => i64::from(*n as i32),
                    Const::Int8(n) => i64::from(*n as i8),
                    _ => return None,
                };
                out.push(v);
            }
            Some(FlatLitElem::ArrayI64(out))
        }
        TypedArrayTag::F32 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let bits = match module.consts.get(cid)? {
                    Const::Float32(b) => *b,
                    Const::Number(b) => (f64::from_bits(*b) as f32).to_bits(),
                    _ => return None,
                };
                out.push(bits);
            }
            Some(FlatLitElem::ArrayF32(out))
        }
        TypedArrayTag::F64 => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let bits = match module.consts.get(cid)? {
                    Const::Number(b) => *b,
                    Const::Float32(b) => f64::from(f32::from_bits(*b)).to_bits(),
                    _ => return None,
                };
                out.push(bits);
            }
            Some(FlatLitElem::ArrayF64(out))
        }
        TypedArrayTag::String => {
            let mut out = Vec::with_capacity(items.len());
            for &cid in items {
                let Const::String(sym) = module.consts.get(cid)? else {
                    return None;
                };
                out.push(*sym);
            }
            Some(FlatLitElem::ArrayString(out))
        }
    }
}

/// Iteratively dereference a pooled literal shape into its hash-consed
/// [`ShapeId`] inside `interner`, rejecting dangling child [`ConstId`]s,
/// non-shape/unsupported elements, and `ConstId` cycles in `O(1)` call stack.
fn canonicalize_const_shape(
    module: &Module,
    interner: &HashMap<Vec<FlatLitElem>, ShapeId>,
    root: ConstId,
) -> Option<ShapeId> {
    let mut active: HashSet<ConstId> = HashSet::new();
    let mut actual_root = root;
    let root_const = loop {
        if !active.insert(actual_root) {
            return None;
        }
        match module.consts.get(actual_root)? {
            Const::LiteralBufferRef(inner) => actual_root = *inner,
            other => break other,
        }
    };
    if let Const::TypedArrayLiteral { tag, items } = root_const {
        let elem = const_typed_array_elems(module, *tag, items)?;
        return interner.get(&vec![elem]).copied();
    }
    let (root_cursor, root_cap) = ConstShapeCursor::from_const(root_const)?;
    let mut memo: HashMap<ConstId, ShapeId> = HashMap::new();
    let mut stack = vec![ConstShapeFrame {
        cid: actual_root,
        parent_wrap: None,
        cursor: root_cursor,
        items: Vec::with_capacity(root_cap),
    }];

    'outer: while let Some(mut frame) = stack.pop() {
        while let Some(child_cid) = frame.cursor.next_id() {
            let child_const = module.consts.get(child_cid)?;
            if let Const::TypedArrayLiteral { tag, items } = child_const {
                frame
                    .items
                    .push(const_typed_array_elems(module, *tag, items)?);
                continue;
            }
            let nested = match child_const {
                Const::ArrayLiteral(_) | Const::ObjectLiteral { .. } => {
                    Some((child_cid, child_const, NestedShapeWrap::Array))
                }
                Const::LiteralBufferRef(inner_cid) => {
                    if active.contains(&child_cid) {
                        return None;
                    }
                    let inner_const = module.consts.get(*inner_cid)?;
                    if let Const::TypedArrayLiteral { tag, items } = inner_const {
                        let elem = const_typed_array_elems(module, *tag, items)?;
                        let child_id = *interner.get(&vec![elem])?;
                        frame.items.push(FlatLitElem::LiteralBufferRef(child_id));
                        continue;
                    }
                    if !matches!(
                        inner_const,
                        Const::ArrayLiteral(_) | Const::ObjectLiteral { .. }
                    ) {
                        return None;
                    }
                    Some((
                        *inner_cid,
                        inner_const,
                        NestedShapeWrap::BufferRef {
                            wrapper_cid: child_cid,
                        },
                    ))
                }
                _ => None,
            };

            if let Some((target_cid, target_const, wrap)) = nested {
                if active.contains(&target_cid) {
                    return None;
                }
                if let Some(&cached_id) = memo.get(&target_cid) {
                    frame.items.push(wrap_flat_elem(wrap, cached_id));
                    continue;
                }
                let (child_cursor, child_cap) = ConstShapeCursor::from_const(target_const)?;
                if let NestedShapeWrap::BufferRef { wrapper_cid } = wrap {
                    active.insert(wrapper_cid);
                }
                active.insert(target_cid);
                stack.push(frame);
                stack.push(ConstShapeFrame {
                    cid: target_cid,
                    parent_wrap: Some(wrap),
                    cursor: child_cursor,
                    items: Vec::with_capacity(child_cap),
                });
                continue 'outer;
            }

            let scalar = match child_const {
                Const::Bool(b) => FlatLitElem::Bool(*b),
                Const::Int8(n) => FlatLitElem::Int8(*n),
                Const::Int32(n) => FlatLitElem::Int32(*n),
                Const::Float32(bits) => FlatLitElem::Float32(*bits),
                Const::Number(bits) => FlatLitElem::Double(*bits),
                Const::Accessor(n) => FlatLitElem::Accessor(*n),
                Const::MethodAffiliate(n) => FlatLitElem::MethodAffiliate(*n),
                Const::BuiltinTypeIndex(n) => FlatLitElem::BuiltinTypeIndex(*n),
                Const::EtsImplements(s) => FlatLitElem::EtsImplements(*s),
                Const::String(s) => FlatLitElem::String(*s),
                Const::MethodRef { func, kind } => FlatLitElem::MethodRef {
                    func: *func,
                    kind: *kind,
                },
                Const::LitNull(n) => FlatLitElem::LitNull(*n),
                Const::Null => FlatLitElem::LitNull(0),
                Const::Undefined
                | Const::Hole
                | Const::Int64(_)
                | Const::UInt64(_)
                | Const::BigInt(_)
                | Const::ArrayLiteral(_)
                | Const::TypedArrayLiteral { .. }
                | Const::ObjectLiteral { .. }
                | Const::LiteralBufferRef(_) => return None,
            };
            frame.items.push(scalar);
        }

        active.remove(&frame.cid);
        if let Some(NestedShapeWrap::BufferRef { wrapper_cid }) = frame.parent_wrap {
            active.remove(&wrapper_cid);
        }
        let shape_id = *interner.get(&frame.items)?;
        memo.insert(frame.cid, shape_id);
        if let Some(parent) = stack.last_mut() {
            let wrap = frame.parent_wrap.unwrap_or(NestedShapeWrap::Array);
            parent.items.push(wrap_flat_elem(wrap, shape_id));
        } else {
            return Some(shape_id);
        }
    }
    None
}

#[derive(Clone, Copy)]
enum FileNestedWrap {
    Array,
    BufferRef,
}

struct LitArrayFrame {
    idx_usize: usize,
    parent_wrap: Option<FileNestedWrap>,
    next_elem: usize,
    items: Vec<FlatLitElem>,
}

fn wrap_file_elem(wrap: FileNestedWrap, id: ShapeId) -> FlatLitElem {
    match wrap {
        FileNestedWrap::Array => FlatLitElem::Array(id),
        FileNestedWrap::BufferRef => FlatLitElem::LiteralBufferRef(id),
    }
}

/// Convert `file.literal_arrays[table_idx]` into its hash-consed [`ShapeId`]
/// iteratively on an explicit heap stack (`O(1)` call stack, cycle-guarded).
fn intern_file_literal_array(
    module: &Module,
    file: &File,
    method_count: usize,
    state: &mut [u8],
    resolved: &mut [Option<ShapeId>],
    interner: &mut HashMap<Vec<FlatLitElem>, ShapeId>,
    table_idx: u32,
) -> Option<ShapeId> {
    let root_usize = table_idx as usize;
    let root_la = file.literal_arrays.get(root_usize)?;
    match state[root_usize] {
        2 => return resolved[root_usize],
        1 => return None,
        _ => {}
    }
    state[root_usize] = 1;
    let mut stack = vec![LitArrayFrame {
        idx_usize: root_usize,
        parent_wrap: None,
        next_elem: 0,
        items: Vec::with_capacity(root_la.values.len()),
    }];

    'outer: while let Some(mut frame) = stack.pop() {
        while frame.next_elem < file.literal_arrays[frame.idx_usize].values.len() {
            let v = &file.literal_arrays[frame.idx_usize].values[frame.next_elem];
            frame.next_elem += 1;
            let nested = match v {
                LiteralValue::LiteralArray(idx) => Some((idx.0, FileNestedWrap::Array)),
                LiteralValue::LiteralBufferIndex(idx) => Some((idx.0, FileNestedWrap::BufferRef)),
                _ => None,
            };

            if let Some((child_idx, wrap)) = nested {
                let child_usize = child_idx as usize;
                let Some(child_la) = file.literal_arrays.get(child_usize) else {
                    abort_lit_stack(state, resolved, frame, stack);
                    return None;
                };
                match state[child_usize] {
                    2 => {
                        let Some(child_id) = resolved[child_usize] else {
                            abort_lit_stack(state, resolved, frame, stack);
                            return None;
                        };
                        frame.items.push(wrap_file_elem(wrap, child_id));
                    }
                    1 => {
                        abort_lit_stack(state, resolved, frame, stack);
                        return None;
                    }
                    _ => {
                        state[child_usize] = 1;
                        let child_cap = child_la.values.len();
                        stack.push(frame);
                        stack.push(LitArrayFrame {
                            idx_usize: child_usize,
                            parent_wrap: Some(wrap),
                            next_elem: 0,
                            items: Vec::with_capacity(child_cap),
                        });
                        continue 'outer;
                    }
                }
            } else {
                let Some(scalar) = scalar_literal_value_elem(module, file, method_count, v) else {
                    abort_lit_stack(state, resolved, frame, stack);
                    return None;
                };
                frame.items.push(scalar);
            }
        }

        let next_id = ShapeId(interner.len() as u32);
        let shape_id = *interner.entry(frame.items).or_insert(next_id);
        state[frame.idx_usize] = 2;
        resolved[frame.idx_usize] = Some(shape_id);
        if let Some(parent) = stack.last_mut() {
            let wrap = frame.parent_wrap.unwrap_or(FileNestedWrap::Array);
            parent.items.push(wrap_file_elem(wrap, shape_id));
        } else {
            return Some(shape_id);
        }
    }
    None
}

fn abort_lit_stack(
    state: &mut [u8],
    resolved: &mut [Option<ShapeId>],
    cur: LitArrayFrame,
    stack: Vec<LitArrayFrame>,
) {
    state[cur.idx_usize] = 2;
    resolved[cur.idx_usize] = None;
    for f in stack {
        state[f.idx_usize] = 2;
        resolved[f.idx_usize] = None;
    }
}

fn lookup_sym_in_module(module: &Module, file: &File, sid: StringId) -> Option<Sym> {
    if let Some(raw) = file.strings.raw_mutf8(sid) {
        module.sym.get_raw_mutf8(raw)
    } else {
        file.strings.as_str(sid).and_then(|s| module.sym.get(s))
    }
}

fn scalar_literal_value_elem(
    module: &Module,
    file: &File,
    method_count: usize,
    v: &LiteralValue,
) -> Option<FlatLitElem> {
    let method_elem = |midx: MethodIdx, kind: LitMethodKind| -> Option<FlatLitElem> {
        (midx.index() < method_count).then_some(FlatLitElem::MethodRef {
            func: FuncId::new(midx.0),
            kind,
        })
    };
    match v {
        LiteralValue::Bool(vb) => Some(FlatLitElem::Bool(*vb)),
        LiteralValue::Integer8(n) => Some(FlatLitElem::Int8(*n)),
        LiteralValue::Integer(n) => Some(FlatLitElem::Int32(*n)),
        LiteralValue::Float(x) => Some(FlatLitElem::Float32(x.to_bits())),
        LiteralValue::Double(x) => Some(FlatLitElem::Double(x.to_bits())),
        LiteralValue::Accessor(n) => Some(FlatLitElem::Accessor(*n)),
        LiteralValue::MethodAffiliate(n) => Some(FlatLitElem::MethodAffiliate(*n)),
        LiteralValue::BuiltinTypeIndex(n) => Some(FlatLitElem::BuiltinTypeIndex(*n)),
        LiteralValue::String(sid) => {
            lookup_sym_in_module(module, file, *sid).map(FlatLitElem::String)
        }
        LiteralValue::EtsImplements(sid) => {
            lookup_sym_in_module(module, file, *sid).map(FlatLitElem::EtsImplements)
        }
        LiteralValue::Method(midx) => method_elem(*midx, LitMethodKind::Method),
        LiteralValue::GeneratorMethod(midx) => method_elem(*midx, LitMethodKind::GeneratorMethod),
        LiteralValue::AsyncGeneratorMethod(midx) => {
            method_elem(*midx, LitMethodKind::AsyncGeneratorMethod)
        }
        LiteralValue::Getter(midx) => method_elem(*midx, LitMethodKind::Getter),
        LiteralValue::Setter(midx) => method_elem(*midx, LitMethodKind::Setter),
        LiteralValue::NullValue(n) => Some(FlatLitElem::LitNull(*n)),
        LiteralValue::ArrayU1(vals) => Some(FlatLitElem::ArrayU1(vals.clone())),
        LiteralValue::ArrayU8(vals) => Some(FlatLitElem::ArrayU8(vals.clone())),
        LiteralValue::ArrayI8(vals) => Some(FlatLitElem::ArrayI8(vals.clone())),
        LiteralValue::ArrayU16(vals) => Some(FlatLitElem::ArrayU16(vals.clone())),
        LiteralValue::ArrayI16(vals) => Some(FlatLitElem::ArrayI16(vals.clone())),
        LiteralValue::ArrayU32(vals) => Some(FlatLitElem::ArrayU32(vals.clone())),
        LiteralValue::ArrayI32(vals) => Some(FlatLitElem::ArrayI32(vals.clone())),
        LiteralValue::ArrayU64(vals) => Some(FlatLitElem::ArrayU64(vals.clone())),
        LiteralValue::ArrayI64(vals) => Some(FlatLitElem::ArrayI64(vals.clone())),
        LiteralValue::ArrayF32(vals) => Some(FlatLitElem::ArrayF32(
            vals.iter().map(|f| f.to_bits()).collect(),
        )),
        LiteralValue::ArrayF64(vals) => Some(FlatLitElem::ArrayF64(
            vals.iter().map(|f| f.to_bits()).collect(),
        )),
        LiteralValue::ArrayString(sids) => {
            let mut syms = Vec::with_capacity(sids.len());
            for &sid in sids {
                syms.push(lookup_sym_in_module(module, file, sid)?);
            }
            Some(FlatLitElem::ArrayString(syms))
        }
        LiteralValue::LiteralArray(_) | LiteralValue::LiteralBufferIndex(_) => None,
    }
}

/// Method-local `(EntityKind, u16_local_id) → EntityRef` relocation map (`#50`).
pub(crate) type EntityMap = HashMap<(EntityKind, u32), EntityRef>;

/// Resolve every entity operand in `bytecodes` through `resolve` and compact
/// module-global `EntityId(u32)` values into method-local `u16` placeholder
/// indices (`0, 1, 2, …` per [`EntityKind`] in first-appearance order, #32).
pub(crate) fn relocate_and_compact_entities(
    func_id: FuncId,
    bytecodes: &[Bytecode],
    mut resolve: impl FnMut(EntityKind, u32) -> Result<EntityRef, LowerError>,
) -> Result<(Vec<Bytecode>, EntityMap), LowerError> {
    let mut out_bytecodes = bytecodes.to_vec();
    let mut entities: EntityMap = HashMap::new();
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
                let entity_ref = resolve(kind, raw)?;
                let counter = match kind {
                    EntityKind::StringId => &mut next_string,
                    EntityKind::MethodId => &mut next_method,
                    EntityKind::LiteralarrayId => &mut next_literal,
                };
                let assigned = u16::try_from(*counter)
                    .map_err(|_| LowerError::EntityIndexOverflow(func_id))?;
                *counter += 1;
                local_ids.insert((kind, raw), assigned);
                entities.insert((kind, u32::from(assigned)), entity_ref);
                assigned
            };
            *id_mut = EntityId(u32::from(local_id));
            Ok(())
        })?;
        if visited != expected_len || bc.entity_operands().len() != expected_len {
            return Err(LowerError::EntityOperandMismatch {
                func: func_id,
                mnemonic: bc.mnemonic().to_string(),
                expected: expected_len,
                visited,
            });
        }
    }

    Ok((out_bytecodes, entities))
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

        let (compacted, entities) =
            relocate_and_compact_entities(FuncId::new(0), &sample, |kind, raw| {
                Ok(match kind {
                    EntityKind::StringId => EntityRef::string(StringId::new(raw)),
                    EntityKind::MethodId => EntityRef::Method(MethodIdx(raw)),
                    EntityKind::LiteralarrayId => EntityRef::LiteralArray(LiteralArrayIdx(raw)),
                })
            })
            .expect("compaction must succeed");
        for bc in &compacted {
            for (kind, id) in bc.entity_operands() {
                assert!(id.0 <= u32::from(u16::MAX), "uncompacted operand in {bc:?}");
                assert!(entities.contains_key(&(kind, id.0)));
            }
        }
        abcd_isa::encode(&compacted).expect("all compacted entity instructions must encode");
    }

    #[test]
    fn entity_index_overflow_above_65536_distinct_in_one_method_errors_loudly() {
        let bytecodes: Vec<Bytecode> = (0..=u32::from(u16::MAX) + 1)
            .map(|i| Bytecode::LdaStr(EntityId(i)))
            .collect();
        let err = relocate_and_compact_entities(FuncId::new(7), &bytecodes, |_, raw| {
            Ok(EntityRef::string(StringId::new(raw)))
        })
        .expect_err("65537 distinct strings in one method must overflow u16");
        assert!(matches!(err, LowerError::EntityIndexOverflow(f) if f == FuncId::new(7)));
    }
}
