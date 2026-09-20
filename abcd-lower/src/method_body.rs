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
use abcd_ir2::{Const, ConstId, FuncId, Module, Sym};
use abcd_isa::EntityKind;

use crate::LowerError;
use crate::layout::LayoutResult;

/// Build an encodable [`MethodBody`] for a lowered function.
///
/// `file` is the source file the module was lifted from: it provides the
/// string table, the method table, and the literal-array table the IR
/// entities must resolve against.
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
    let param_count = module
        .func(func_id)
        .map(|f| f.params.len())
        .unwrap_or_default();

    let resolver = EntityResolver::new(module, file);

    let mut entity_offsets: HashMap<(EntityKind, u32), u32> = HashMap::new();
    for bc in &result.bytecodes {
        for (kind, id) in bc.entity_operands() {
            let offset =
                match kind {
                    EntityKind::StringId => resolver.string_offset(Sym::new(id.0)).ok_or(
                        LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        },
                    )?,
                    EntityKind::MethodId => resolver.method_offset(FuncId::new(id.0)).ok_or(
                        LowerError::UntraceableEntity {
                            func: func_id,
                            kind,
                            raw: id.0,
                        },
                    )?,
                    EntityKind::LiteralarrayId => resolver
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
        num_args: param_count as u32,
        bytecodes: result.bytecodes.clone(),
        entity_offsets,
        try_blocks: result.try_blocks.clone(),
    })
}

/// Reverse entity resolver: v0.2 IR identities → source-file offsets.
struct EntityResolver<'a> {
    module: &'a Module,
    file: &'a File,
    /// MUTF-8 string content → smallest source offset of a string entity
    /// with that content.
    string_offsets: HashMap<String, u32>,
    /// Function-table position → method source offset (`all_methods()`
    /// order = the lift's reservation order).
    method_offsets: Vec<u32>,
    /// Literal-array table index → source offset (inverted
    /// `literal_array_offsets`).
    literal_index_to_offset: HashMap<u32, u32>,
}

impl<'a> EntityResolver<'a> {
    fn new(module: &'a Module, file: &'a File) -> Self {
        let mut string_offsets: HashMap<String, u32> = HashMap::new();
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
        let method_offsets = file.all_methods().map(|(_, m)| m.offset).collect();
        let literal_index_to_offset = file
            .literal_array_offsets
            .iter()
            .map(|(&offset, &index)| (index, offset))
            .collect();
        Self {
            module,
            file,
            string_offsets,
            method_offsets,
            literal_index_to_offset,
        }
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
        let index = (0..self.file.literal_arrays.len() as u32)
            .find(|&idx| self.const_matches_literal_array(tree, idx, 0))?;
        self.literal_index_to_offset.get(&index).copied()
    }

    /// Structural content equality between a shape const tree and the
    /// literal array at `table_idx` — the exact inverse of `abcd-lift`'s
    /// `const_for_literal_array`/`const_for_literal_value` (every
    /// resolution that lift performs forward is inverted here, including
    /// nested arrays and the raw-offset typed-array payloads).
    fn const_matches_literal_array(&self, tree: &Const, table_idx: u32, depth: u32) -> bool {
        if depth > 64 {
            return false;
        }
        let Const::ArrayLiteral(items) = tree else {
            return false;
        };
        let Some(la) = self.file.literal_arrays.get(table_idx as usize) else {
            return false;
        };
        items.len() == la.values.len()
            && items
                .iter()
                .zip(la.values.iter())
                .all(|(c, v)| self.const_matches_literal_value(c, v, depth))
    }

    /// One const ↔ one literal value (the inverse of
    /// `const_for_literal_value`).
    fn const_matches_literal_value(&self, c: &Const, v: &LiteralValue, depth: u32) -> bool {
        match (c, v) {
            (Const::Bool(b), LiteralValue::Bool(vb)) => b == vb,
            (Const::Number(bits), LiteralValue::Integer8(n)) => *bits == (*n as f64).to_bits(),
            (Const::Number(bits), LiteralValue::Integer(n)) => *bits == (*n as f64).to_bits(),
            (Const::Number(bits), LiteralValue::Float(x)) => *bits == (*x as f64).to_bits(),
            (Const::Number(bits), LiteralValue::Double(x)) => *bits == x.to_bits(),
            (Const::Number(bits), LiteralValue::Accessor(n)) => *bits == f64::from(*n).to_bits(),
            (Const::Number(bits), LiteralValue::MethodAffiliate(n)) => {
                *bits == f64::from(*n).to_bits()
            }
            (Const::Number(bits), LiteralValue::BuiltinTypeIndex(n)) => {
                *bits == f64::from(*n).to_bits()
            }
            (Const::String(sym), LiteralValue::String(sid))
            | (Const::String(sym), LiteralValue::EtsImplements(sid)) => {
                self.module.sym.resolve(*sym).is_some()
                    && self.file.strings.resolve(*sid) == self.module.sym.resolve(*sym)
            }
            (Const::MethodRef(fid), LiteralValue::Method(off))
            | (Const::MethodRef(fid), LiteralValue::GeneratorMethod(off))
            | (Const::MethodRef(fid), LiteralValue::AsyncGeneratorMethod(off))
            | (Const::MethodRef(fid), LiteralValue::Getter(off))
            | (Const::MethodRef(fid), LiteralValue::Setter(off)) => {
                self.method_index_of(*off) == Some(fid.index() as u32)
            }
            (Const::Null, LiteralValue::NullValue(_)) => true,
            (Const::ArrayLiteral(_), LiteralValue::LiteralArray(idx)) => {
                self.const_matches_literal_array(c, idx.0, depth + 1)
            }
            (Const::ArrayLiteral(_), LiteralValue::LiteralBufferIndex(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayU1(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayU8(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayI8(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayU16(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayI16(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayU32(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayI32(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayU64(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayI64(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayF32(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayF64(raw))
            | (Const::ArrayLiteral(_), LiteralValue::ArrayString(raw)) => {
                // The lift's N52 rule: raw file offset → table index via
                // the offset map, with a direct-index fallback for
                // hand-built models.
                match self.typed_array_table_index(raw.0) {
                    Some(idx) => self.const_matches_literal_array(c, idx, depth + 1),
                    None => false,
                }
            }
            _ => false,
        }
    }

    /// Raw file offset → literal-array table index (the lift's
    /// `typed_array_table_index`): offset map first, direct index as a
    /// fallback for hand-built models.
    fn typed_array_table_index(&self, raw: u32) -> Option<u32> {
        if let Some(&idx) = self.file.literal_array_offsets.get(&raw) {
            return Some(idx);
        }
        if (raw as usize) < self.file.literal_arrays.len() {
            return Some(raw);
        }
        None
    }

    /// The method offset's position in `all_methods()` order (the
    /// function-table reservation order).
    fn method_index_of(&self, offset: u32) -> Option<u32> {
        self.method_offsets
            .iter()
            .position(|&o| o == offset)
            .map(|i| i as u32)
    }
}
