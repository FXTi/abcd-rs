//! Produce an encodable [`abcd_file::MethodBody`] from a lowered function.
//!
//! [`lower_function`](crate::lower_function) emits entity operands whose
//! raw values are v0.2 IR identities (never source-file offsets —
//! design/ir-v0.2.md §6.2):
//!
//! - `StringId` operands carry the raw [`Sym`] arena index;
//! - `MethodId` operands carry the module function-table index
//!   ([`FuncId`]) of the referenced method;
//! - `LiteralarrayId` operands carry the [`ConstId`] of the literal shape.
//!
//! `abcd_file::encode` relocates such operands through
//! `MethodBody.entity_offsets` (raw operand → source-file offset) and
//! `Builder::relocate_code_id` — the same channel the decode → encode and
//! the v0.1 lower paths use. This module derives those relocation entries
//! by resolving the IR entities BACK to source-file offsets through the
//! source file's tables (the exact inverse of `abcd-lift`'s forward
//! resolution in `resolve.rs`):
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
//! [`LowerError::UntraceableEntity`] — nothing is invented and no operand
//! passes through silently.

use std::collections::HashMap;

use abcd_file::{File, LiteralValue, MethodBody};
use abcd_ir::{Const, ConstId, FuncId, Module, Sym};
use abcd_isa::EntityKind;
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

/// Module-scoped reverse entity resolver: v0.2 IR identities → source-file
/// offsets (#29).
///
/// Built once per `(Module, File)` pair and safe to share across threads
/// (`Sync`). All lookups (`string_offset`, `method_offset`,
/// `literal_array_offset`) run in `O(1)` amortized time.
pub struct EntityResolver<'a> {
    module: &'a Module,
    /// MUTF-8 string content → smallest source offset of a string entity
    /// with that content.
    string_offsets: HashMap<String, u32>,
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
    pub fn new(module: &'a Module, file: &'a File) -> Self {
        let mut string_offsets: HashMap<String, u32> =
            HashMap::with_capacity(file.entity_map.len());
        // Smallest offset wins on duplicate content (encode resolves
        // string operands content-addressed, so any valid entry produces
        // identical output; the choice only needs to be deterministic).
        let mut entries: Vec<(u32, abcd_file::StringId)> =
            file.entity_map.iter().map(|(&o, &s)| (o, s)).collect();
        entries.sort_unstable();
        for (offset, sid) in entries {
            if let Some(content) = file.strings.resolve(sid) {
                string_offsets.entry(content.to_string()).or_insert(offset);
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
                build_literal_array_const(module, file, &method_offset_to_index, &mut cache, idx, 0)
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

        let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
        for bc in &result.bytecodes {
            for (kind, id) in bc.entity_operands() {
                let offset = match kind {
                    EntityKind::StringId => {
                        self.string_offset(Sym::new(id.0))
                            .ok_or(LowerError::UntraceableEntity {
                                func: func_id,
                                kind,
                                raw: id.0,
                            })?
                    }
                    EntityKind::MethodId => self.method_offset(FuncId::new(id.0)).ok_or(
                        LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        },
                    )?,
                    EntityKind::LiteralarrayId => self
                        .literal_array_offset(ConstId::new(id.0))
                        .ok_or(LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        })?,
                };
                entity_offsets.insert((kind, id.0), offset);
            }
        }

        Ok(MethodBody {
            num_vregs: u32::from(result.num_regs),
            num_args: param_count as u32,
            bytecodes: result.bytecodes.clone(),
            entity_offsets,
            try_blocks: result.try_blocks.clone(),
            ic_size: Some(result.ic_size),
        })
    }

    /// [`Sym`] → source offset of an equal-content string entity.
    fn string_offset(&self, sym: Sym) -> Option<u32> {
        let content = self.module.sym.resolve(sym)?;
        self.string_offsets.get(content).copied()
    }

    /// [`FuncId`] → source offset of the method at that function-table
    /// position.
    fn method_offset(&self, func: FuncId) -> Option<u32> {
        self.method_offsets.get(func.index()).copied()
    }

    /// [`ConstId`] (a literal shape) → source offset of the smallest
    /// literal-array table entry whose content matches the shape.
    fn literal_array_offset(&self, shape: ConstId) -> Option<u32> {
        let tree = self.module.consts.get(shape)?;
        let &index = self.shape_to_min_index.get(tree)?;
        self.literal_index_to_offset.get(&index).copied()
    }
}

/// Convert `file.literal_arrays[table_idx]` into its canonical [`Const`]
/// shape (the exact inverse of `abcd-lift`'s `const_for_literal_array`),
/// returning `None` if any element uses an uninterned string, unknown
/// method offset, non-shape literal tag, or nesting depth > 64.
fn build_literal_array_const(
    module: &Module,
    file: &File,
    method_offset_to_index: &HashMap<u32, u32>,
    cache: &mut [Option<Option<Const>>],
    table_idx: u32,
    depth: u32,
) -> Option<Const> {
    if depth > 64 {
        return None;
    }
    let idx_usize = table_idx as usize;
    let la = file.literal_arrays.get(idx_usize)?;
    // Memoize depth-valid conversions (`None` inside `Some(None)` marks
    // either an active cycle or a permanently non-representable array).
    if let Some(cached) = &cache[idx_usize] {
        return cached.clone();
    }
    // Install `Some(None)` before recursing as a cycle guard.
    cache[idx_usize] = Some(None);
    let mut items = Vec::with_capacity(la.values.len());
    for v in &la.values {
        let c = build_literal_value_const(module, file, method_offset_to_index, cache, v, depth)?;
        items.push(c);
    }
    let out = Const::ArrayLiteral(items);
    cache[idx_usize] = Some(Some(out.clone()));
    Some(out)
}

fn build_literal_value_const(
    module: &Module,
    file: &File,
    method_offset_to_index: &HashMap<u32, u32>,
    cache: &mut [Option<Option<Const>>],
    v: &LiteralValue,
    depth: u32,
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
            let s = file.strings.resolve(*sid)?;
            module.sym.get(s).map(Const::String)
        }
        LiteralValue::Method(off)
        | LiteralValue::GeneratorMethod(off)
        | LiteralValue::AsyncGeneratorMethod(off)
        | LiteralValue::Getter(off)
        | LiteralValue::Setter(off) => method_offset_to_index
            .get(off)
            .map(|&idx| Const::MethodRef(FuncId::new(idx))),
        LiteralValue::NullValue(_) => Some(Const::Null),
        LiteralValue::LiteralArray(idx) => build_literal_array_const(
            module,
            file,
            method_offset_to_index,
            cache,
            idx.0,
            depth + 1,
        ),
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
        | LiteralValue::ArrayString(raw) => {
            let idx = typed_array_table_index(file, raw.0)?;
            build_literal_array_const(module, file, method_offset_to_index, cache, idx, depth + 1)
        }
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
