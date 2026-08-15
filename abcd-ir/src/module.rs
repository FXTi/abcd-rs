//! Module: top-level IR container holding all arenas and metadata.

use abcd_file::{AccessFlags, AnnotationValue, FileType, FunctionKind, SourceLang, Version};
use abcd_file::{ColumnEntry, LineEntry, LocalVarInfo, ParamInfo};
use abcd_file::{FieldValue, LiteralArray, ModuleData};

use crate::entity::{Block, ClassId, FuncId, Inst, StringId, Value};
use crate::inst::InstData;
use crate::types::IrType;

// ─── String pool ─────────────────────────────────────────────────────────────

use string_interner::{DefaultStringInterner, DefaultSymbol, Symbol};

/// Deduplicating string pool backed by `string-interner`.
#[derive(Clone, Debug, Default)]
pub struct StringPool {
    inner: DefaultStringInterner,
}

impl StringPool {
    pub fn new() -> Self {
        Self::default()
    }

    /// Intern a string, returning its [`StringId`].
    /// If the string already exists, the existing id is returned.
    pub fn intern(&mut self, s: &str) -> StringId {
        let sym = self.inner.get_or_intern(s);
        StringId(sym.to_usize() as u32)
    }

    /// Look up a string by id.
    pub fn get(&self, id: StringId) -> &str {
        let sym = DefaultSymbol::try_from_usize(id.index()).expect("invalid StringId");
        self.inner.resolve(sym).expect("dangling StringId")
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
}

// ─── Annotations ─────────────────────────────────────────────────────────────

/// Complete annotations preserving all four retention categories.
#[derive(Clone, Debug, Default)]
pub struct IrAnnotations {
    pub compile_time: Vec<IrAnnotation>,
    pub runtime: Vec<IrAnnotation>,
    pub compile_time_type: Vec<IrAnnotation>,
    pub runtime_type: Vec<IrAnnotation>,
}

/// A single annotation with interned strings.
#[derive(Clone, Debug)]
pub struct IrAnnotation {
    pub class_descriptor: StringId,
    pub elements: Vec<(StringId, AnnotationValue)>,
}

// ─── Debug info ──────────────────────────────────────────────────────────────

/// Per-function debug information (source mapping, locals, params).
#[derive(Clone, Debug)]
pub struct FuncDebugInfo {
    pub source_file: Option<StringId>,
    pub source_code: Option<StringId>,
    pub line_table: Vec<LineEntry>,
    pub column_table: Vec<ColumnEntry>,
    pub local_vars: Vec<LocalVarInfo>,
    pub params: Vec<ParamInfo>,
}

// ─── Value / Instruction nodes ───────────────────────────────────────────────

/// How an SSA value is defined.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValueDef {
    /// Result of an instruction (including phi nodes).
    Inst(Inst),
    /// Function parameter (by index).
    FuncParam(u16),
}

/// Per-value metadata stored in the arena.
#[derive(Clone, Debug)]
pub struct ValueData {
    pub def: ValueDef,
    pub ty: IrType,
}

/// Per-instruction metadata stored in the arena.
#[derive(Clone, Debug)]
pub struct InstNode {
    pub data: InstData,
    pub result: Option<Value>,
    pub result_type: IrType,
    pub block: Block,
    /// Source bytecode offset (for debug mapping).
    pub loc: Option<u32>,
}

// ─── Basic block ─────────────────────────────────────────────────────────────

/// A basic block: a sequence of phi nodes followed by instructions,
/// ending with a terminator.
#[derive(Clone, Debug)]
pub struct BasicBlockData {
    /// Phi instructions (must precede all other instructions).
    pub phis: Vec<Inst>,
    /// Non-phi instructions; the last must be a terminator.
    pub insts: Vec<Inst>,
    /// Predecessor blocks.
    pub preds: Vec<Block>,
}

impl BasicBlockData {
    pub fn new() -> Self {
        Self {
            phis: Vec::new(),
            insts: Vec::new(),
            preds: Vec::new(),
        }
    }
}

impl Default for BasicBlockData {
    fn default() -> Self {
        Self::new()
    }
}

// ─── Function ────────────────────────────────────────────────────────────────

/// IR representation of a single function/method.
#[derive(Clone, Debug)]
pub struct FunctionData {
    pub name: StringId,
    pub kind: FunctionKind,
    pub access_flags: AccessFlags,
    pub source_lang: SourceLang,
    pub is_external: bool,
    pub param_count: u16,
    pub return_type: Option<IrType>,
    pub param_types: Vec<IrType>,
    pub entry_block: Block,
    /// All blocks owned by this function (entry_block is always blocks[0]).
    pub blocks: Vec<Block>,
    pub annotations: IrAnnotations,
    pub debug: Option<FuncDebugInfo>,
    /// Try/catch scope info preserved from lifting for reconstruction during lowering.
    pub try_regions: Vec<TryRegion>,
}

/// A try/catch region in the IR, mapping protected blocks to catch handlers.
#[derive(Clone, Debug)]
pub struct TryRegion {
    /// Blocks covered by this try region.
    pub try_blocks: Vec<Block>,
    /// Catch handlers: (type_idx, handler_block).
    /// `type_idx == u32::MAX` means catch-all.
    pub catches: Vec<CatchHandler>,
}

/// A catch handler entry.
#[derive(Clone, Debug)]
pub struct CatchHandler {
    /// Exception type index (u32::MAX for catch-all).
    pub type_idx: u32,
    /// The block where the catch handler starts.
    pub handler_block: Block,
}

// ─── Class ───────────────────────────────────────────────────────────────────

/// Class structure metadata, lifted from `abcd_file::Class`.
#[derive(Clone, Debug)]
pub struct ClassData {
    pub descriptor: StringId,
    pub name: StringId,
    pub access_flags: AccessFlags,
    pub source_lang: SourceLang,
    pub source_file: Option<StringId>,
    pub is_external: bool,
    pub super_class: Option<StringId>,
    pub interfaces: Vec<StringId>,
    pub fields: Vec<FieldData>,
    /// References into `Module::functions`.
    pub methods: Vec<FuncId>,
    pub annotations: IrAnnotations,
}

/// Field metadata.
#[derive(Clone, Debug)]
pub struct FieldData {
    pub name: StringId,
    pub field_type: IrType,
    pub access_flags: AccessFlags,
    pub is_external: bool,
    pub initial_value: Option<FieldValue>,
    pub annotations: IrAnnotations,
}

// ─── Module (top-level container) ────────────────────────────────────────────

/// Top-level IR module owning all arenas and metadata.
///
/// Designed for complete round-trip: `abcd_file::File` → `Module` → `abcd_file::File`.
#[derive(Clone, Debug)]
pub struct Module {
    // ── File-level metadata ──
    pub version: Version,
    pub file_type: FileType,

    // ── Module-level data ──
    pub classes: Vec<ClassData>,
    pub literal_arrays: Vec<LiteralArray>,
    pub module_data: Vec<ModuleData>,

    // ── Function body IR ──
    pub functions: Vec<FunctionData>,
    pub insts: Vec<InstNode>,
    pub blocks: Vec<BasicBlockData>,
    pub values: Vec<ValueData>,

    // ── Shared resources ──
    pub strings: StringPool,
}

impl Module {
    pub fn new(version: Version, file_type: FileType) -> Self {
        Self {
            version,
            file_type,
            classes: Vec::new(),
            literal_arrays: Vec::new(),
            module_data: Vec::new(),
            functions: Vec::new(),
            insts: Vec::new(),
            blocks: Vec::new(),
            values: Vec::new(),
            strings: StringPool::new(),
        }
    }

    pub fn func(&self, id: FuncId) -> &FunctionData {
        &self.functions[id.index()]
    }

    pub fn func_mut(&mut self, id: FuncId) -> &mut FunctionData {
        &mut self.functions[id.index()]
    }

    pub fn block(&self, id: Block) -> &BasicBlockData {
        &self.blocks[id.index()]
    }

    pub fn block_mut(&mut self, id: Block) -> &mut BasicBlockData {
        &mut self.blocks[id.index()]
    }

    pub fn inst(&self, id: Inst) -> &InstNode {
        &self.insts[id.index()]
    }

    pub fn inst_mut(&mut self, id: Inst) -> &mut InstNode {
        &mut self.insts[id.index()]
    }

    pub fn value(&self, id: Value) -> &ValueData {
        &self.values[id.index()]
    }

    pub fn class(&self, id: ClassId) -> &ClassData {
        &self.classes[id.index()]
    }
}
