//! # abcd-lift — lift converter: `abcd_file::File` → `abcd_ir::Module`
//!
//! Format-aware lifting layer (`design/ir.md` §3, `design/decisions.md`)
//! that translates decoded `.abc` containers ([`abcd_file::File`]) into the
//! format-independent SSA IR ([`abcd_ir::Module`]). Alongside `abcd-lower`,
//! this crate is the boundary between the `.abc`/ISA container layer and the
//! semantic IR:
//!
//! - **Dialect & class metadata (`D3`)** — [`abcd_file::Dialect`] maps
//!   directly onto [`abcd_ir::Module::dialect`], and every [`abcd_ir::ClassData`]
//!   header (including `es_module`, `scope_names`, `annotations`, and `fields`)
//!   plus standalone module records are published before lifting method bodies.
//! - **Entity resolution → [`abcd_ir::SymbolTable`] + [`FuncId`]** — strings
//!   intern losslessly as content-keyed [`Sym`]s (UTF-8 or raw MUTF-8 bytes);
//!   method references resolve via dense [`abcd_file::MethodIdx`] slots into
//!   [`FuncId`] indices (never name-keyed, never raw offsets).
//! - **Literal arrays → [`abcd_ir::ConstPool`]** — lossless typed [`Const`]
//!   trees (including nested arrays, literal-buffer refs, and inline typed
//!   primitive/string arrays), with method references lifted to
//!   [`Const::MethodRef`].
//! - **Module records → [`abcd_ir::EsModule`] / [`abcd_ir::ImportDecl`] / [`abcd_ir::ExportDecl`]** —
//!   standalone `_ESModuleRecord` and `--merge-abc` `moduleRecordIdx`
//!   field blobs (`FieldValue::ModuleData`) parse into declarations with
//!   `module_request_idx` resolved to specifier [`Sym`]s;
//!   `moduleRequestPhaseIdx` blobs pair per-record into
//!   [`abcd_ir::ModuleRequest`]`{specifier, lazy}`;
//!   `_ESScopeNamesRecord` and `--merge-abc` `scopeNames` fields populate
//!   [`abcd_ir::ClassData::scope_names`] and
//!   [`DebugData::scope_names`](abcd_ir::DebugData).
//! - **Annotations** — the four container retention buckets merge into one
//!   ordered list per attach site (`compile_time`, `runtime`,
//!   `compile_time_type`, `runtime_type`).
//! - **Debug** — line/column tables attach to lifted [`InstId`]s (and
//!   `Inst.loc`), local variable names carry instruction-extent scopes, and
//!   parameter names and source text lift into [`DebugData`](abcd_ir::DebugData).
//! - **CFG + Braun SSA** — `u32`→`u16` checked parameter counts, entry
//!   parameter seeding, explicit frame-initial constants recorded on
//!   [`FunctionData::frame_init_consts`] ([`Const::Undefined`](abcd_ir::Const)
//!   for uninitialized vregs, [`Const::Hole`](abcd_ir::Const) for
//!   accumulator-read-before-write), catch-handler
//!   [`ExceptionParam`](abcd_ir::ValueDef) values, and predecessor-complete
//!   Braun SSA construction with iterative union-find + user-cascade
//!   trivial-phi elimination.
//! - **Try regions** — structured [`TryRegion`]s with materialized
//!   [`EdgeKind::Exceptional`](abcd_ir::EdgeKind) edges in `Block.preds` for
//!   every `(protected block → handler)` pair, followed by unreachable-block
//!   pruning over [`abcd_ir::cfg::ExceptionHandlerMap`] exception-augmented
//!   reachability.
//! - **Opcode coverage** — every modern (`9.0.0.0`..`24.0.0.0`) and legacy
//!   (`0.0.0.2`) bytecode opcode maps into the 94-op IR taxonomy (see
//!   `translate.rs` for the full opcode mapping).
//!
//! Library rule: no panics on data; every malformed or unsupported input
//! returns a typed [`LiftError`].

#![forbid(unsafe_code)]
#![deny(missing_docs)]
#![cfg_attr(not(test), deny(clippy::unwrap_used))]

mod cfg;
mod metadata;
mod parallel;
mod resolve;
mod ssa;
mod translate;

use std::collections::{BTreeSet, HashMap};
use std::sync::{Arc, OnceLock};

use abcd_file::{File, Method, MethodBody};
use abcd_ir::{
    Block, BlockId, Catch, ClassId, Const, ConstId, Edge, EdgeKind, FieldId, FuncId, FunctionData,
    Inst, InstId, Module, Sym, TryRegion, Ty, Value, ValueDef, ValueId,
};

use cfg::{RawCfg, build_cfg};
use ssa::RegOrAcc;

pub use translate::{SuperKeyForm, super_key};

const PARALLEL_MIN_METHODS: usize = 32;
const PARALLEL_MIN_BYTECODES: usize = 1_024;

/// Configuration options for [`lift_file_with_options`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiftOptions {
    /// Retain arena tail capacity instead of calling `shrink_to_fit()` at the
    /// end of lifting (`true` avoids `~600 MiB` arena reallocation when the
    /// caller immediately appends an OpenHarmony lifecycle harness, `#71`).
    pub retain_tail_capacity: bool,
    /// Lift method bodies in parallel across Rayon workers while merging into
    /// a 100% structurally identical [`Module`] (`#84`).
    pub parallel: bool,
}

impl Default for LiftOptions {
    fn default() -> Self {
        Self {
            retain_tail_capacity: false,
            parallel: true,
        }
    }
}

/// Errors that can occur during lifting (no panics on untrusted data;
/// `Unsupported*` variants are restricted to constructs with zero upstream VM
/// semantics per `design/decisions.md` ADR-07).
#[derive(Debug, thiserror::Error)]
pub enum LiftError {
    /// An entity operand could not be resolved through the owning
    /// method's typed index mapping (string/method/literal-array).
    #[error("unresolved entity id {0}")]
    UnresolvedEntity(u32),
    /// A non-external method has no body.
    #[error("method has no body")]
    NoBody,
    /// A method body has no bytecodes.
    #[error("empty bytecode")]
    EmptyBytecode,
    /// The code-header argument count exceeds the u16 parameter limit.
    #[error("method declares num_args {0}, which exceeds the u16 parameter-count limit")]
    ParamCountOverflow(u32),
    /// The code-header frame exceeds the u16 register limit.
    #[error(
        "method frame num_vregs {num_vregs} + num_args {num_args} exceeds the u16 register limit"
    )]
    FrameTooLarge {
        /// Declared virtual-register count.
        num_vregs: u32,
        /// Declared argument count.
        num_args: u32,
    },
    /// Super-property access by constant index: `isa.yaml` has NO
    /// super-by-index opcode, so this can never be produced from real
    /// bytecode — preserved as a hard error (v0.1 lower's
    /// `UnsupportedInstruction` ruling), never silently invented.
    #[error(
        "super-property access by constant index has no ArkCompiler opcode (isa.yaml has no super-by-index form)"
    )]
    UnsupportedSuperByIndex,
    /// The fused compare-and-branch family — the acc-branch forms
    /// (`jstricteqz` / `jnstricteqz`, `jeqnull` / `jnenull`,
    /// `jstricteqnull` / `jnstricteqnull`, `jequndefined` /
    /// `jneundefined`, `jstrictequndefined` / `jnstrictequndefined`)
    /// and the fused compare-branch forms (`jeq` / `jne` /
    /// `jstricteq` / `jnstricteq`)
    /// (abcd-isa-sys/arkcompiler_runtime_core/isa/isa.yaml:1700-1796):
    /// isa.yaml documents only `pc += imm` for the family — NO
    /// comparison semantics. The C++ interpreter FATALs all 24
    /// variants (interpreter-inl.cpp:6853-6964), the assembly
    /// interpreter NOP-skips them (interpreter_stub.cpp:5412-5516),
    /// the baseline JIT/AOT ignore them, es2abc never emits them
    /// (pandagen.cpp:1139-1170 lowers unfused:
    /// `ldundefined;eq;jnez` / `ldundefined;stricteq;jnez`), and
    /// abckit marks the null/undefined/zero forms deprecated and the
    /// compare forms replaced. Corpus coverage is zero (0/5517
    /// reference .pa + 156 wild packages), so there is NO upstream
    /// behavior to lift — a hard error (maintainer ruling 2026-10-04,
    /// N51 pattern), never silently invented.
    #[error(
        "unsupported fused compare-and-branch opcode `{0}` (ruling 2026-10-04): isa.yaml documents no comparison semantics (pc += imm only), the vendor interpreters FATAL/NOP-skip the family, and no producer emits it — please report this file to the abcd-rs maintainers"
    )]
    UnsupportedFusedCompareBranch(&'static str),
    /// `throw.ifsupernotcorrectcall` carries a check-kind immediate the
    /// vendor does not define (0 = TDZ guard, 1 = re-bind guard).
    #[error(
        "throw.ifsupernotcorrectcall kind {0} is not a vendor-defined check kind (0=NotCalled, 1=Rebind)"
    )]
    InvalidSuperCheckKind(u16),
    /// A literal-array table index is out of range.
    #[error("literal array index {0} out of range")]
    LiteralArrayOutOfRange(u32),
    /// Literal arrays form a reference cycle (or nest pathologically).
    #[error("literal array cycle detected at table index {0}")]
    LiteralArrayCycle(u32),
    /// A module record references a module-request index outside the
    /// record's request list.
    #[error("module record references module_request_idx {idx} but only {count} requests exist")]
    MalformedModuleData {
        /// The offending request index.
        idx: u32,
        /// The record's request count.
        count: usize,
    },
    /// A bytecode operand references a register outside `num_vregs + num_args`.
    #[error("register v{reg} exceeds method frame limit {frame_limit}")]
    InvalidRegister {
        /// Offending register index.
        reg: u16,
        /// Total frame register count (`num_vregs + num_args`).
        frame_limit: u16,
    },
    /// A register-range operand overflows `u16` or carries a negative count.
    #[error("register range start v{start} + count {count} overflows u16")]
    RegisterRangeOverflow {
        /// Window start register.
        start: u16,
        /// Encoded register count.
        count: i64,
    },
    /// A jump target points outside the method's bytecode stream.
    #[error("jump at instruction {pc} targets out-of-bounds instruction {target} (len {len})")]
    JumpTargetOutOfBounds {
        /// Instruction index of the jump.
        pc: usize,
        /// Target instruction index.
        target: usize,
        /// Total instruction count.
        len: usize,
    },
    /// Control falls through past the end of the method's bytecode stream.
    #[error("instruction {pc} falls through past end of bytecode stream (len {len})")]
    FallthroughOutOfBounds {
        /// Instruction index of the falling-through instruction.
        pc: usize,
        /// Total instruction count.
        len: usize,
    },
    /// A `TryBlock` covers an empty or out-of-bounds instruction range.
    #[error("try block [{start}..{start}+{len}) exceeds bytecode length {bytecode_len}")]
    TryRangeOutOfBounds {
        /// Start instruction index.
        start: u32,
        /// Protected instruction count.
        len: u32,
        /// Total instruction count.
        bytecode_len: usize,
    },
    /// A `CatchBlock` handler or length points outside the method's bytecode stream.
    #[error("catch handler [{handler}..{handler}+{len}) exceeds bytecode length {bytecode_len}")]
    CatchRangeOutOfBounds {
        /// Handler entry instruction index.
        handler: u32,
        /// Handler instruction count.
        len: u32,
        /// Total instruction count.
        bytecode_len: usize,
    },
}

/// Backing arena storage (`blocks`, `insts`, `values`) for SSA construction and
/// instruction emission (`Module` in sequential lifting; `LocalArenas` on
/// parallel workers).
pub(crate) trait IrArenas {
    fn blocks(&self) -> &[Block];
    fn blocks_mut(&mut self) -> &mut Vec<Block>;
    fn insts(&self) -> &[Inst];
    fn insts_mut(&mut self) -> &mut Vec<Inst>;
    fn values(&self) -> &[Value];
    fn values_mut(&mut self) -> &mut Vec<Value>;
    fn blocks_and_insts_mut(&mut self) -> (&mut Vec<Block>, &mut Vec<Inst>);
}

impl IrArenas for Module {
    #[inline]
    fn blocks(&self) -> &[Block] {
        &self.blocks
    }

    #[inline]
    fn blocks_mut(&mut self) -> &mut Vec<Block> {
        &mut self.blocks
    }

    #[inline]
    fn insts(&self) -> &[Inst] {
        &self.insts
    }

    #[inline]
    fn insts_mut(&mut self) -> &mut Vec<Inst> {
        &mut self.insts
    }

    #[inline]
    fn values(&self) -> &[Value] {
        &self.values
    }

    #[inline]
    fn values_mut(&mut self) -> &mut Vec<Value> {
        &mut self.values
    }

    #[inline]
    fn blocks_and_insts_mut(&mut self) -> (&mut Vec<Block>, &mut Vec<Inst>) {
        (&mut self.blocks, &mut self.insts)
    }
}

/// Shared interface over sequential [`Lifter`] and worker-local
/// [`parallel::MethodLiftCtx`] so [`lift_method_with`], [`metadata`],
/// [`resolve`], and [`translate`] execute one unified code path (`#84`).
pub(crate) trait LiftBackend<'f> {
    type Arenas: IrArenas;

    fn file(&self) -> &'f File;
    fn arenas(&self) -> &Self::Arenas;
    fn arenas_mut(&mut self) -> &mut Self::Arenas;
    fn backend_method_count(&self) -> usize;
    fn backend_method_name(&self, idx: abcd_file::MethodIdx) -> Option<Sym>;
    fn backend_field_id(&self, idx: abcd_file::FieldIdx) -> Option<(ClassId, FieldId)>;
    fn backend_field_name(&self, cid: ClassId, fid: FieldId) -> Option<Sym>;

    fn backend_sym_of_file_sid(&mut self, sid: abcd_file::StringId) -> Option<Sym>;
    fn backend_sym(&mut self, s: &'static str) -> Sym;
    fn backend_class_of_descriptor(&mut self, sid: abcd_file::StringId) -> Option<ClassId>;
    fn backend_const_scalar(&mut self, c: Const) -> ConstId;
    fn backend_const_shape(&mut self, c: Const) -> ConstId;

    fn empty_object_shape(&mut self) -> ConstId {
        self.backend_const_shape(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        })
    }

    fn backend_resolve_lit_array(
        &mut self,
        table_idx: u32,
        wrap: resolve::LitWrap,
    ) -> Result<ConstId, LiftError>;

    fn backend_try_lit_array_or_null(&mut self, table_idx: u32, wrap: resolve::LitWrap) -> ConstId;

    fn backend_this_param_index(&self, fd: &FunctionData) -> Option<usize>;
    fn backend_is_const_bool(&self, cid: ConstId) -> bool;

    fn backend_legacy_module_slots(
        &self,
        class_id: ClassId,
    ) -> Option<&metadata::LegacyModuleSlotIndex>;

    fn backend_record_legacy_modvar_fallback(&mut self, inst_id: InstId, sym: Sym);
    fn backend_lookup_scope_names(
        &self,
        class_id: ClassId,
        source_file: Option<Sym>,
    ) -> Option<ConstId>;
    fn backend_resolve_source_code(&mut self, sid: abcd_file::StringId) -> Option<Arc<str>>;
}

/// The module-level conversion state: the v0.2 module under
/// construction plus the identity tables built in pass 1.
pub(crate) struct Lifter<'f> {
    /// The file being lifted.
    pub file: &'f File,
    /// The v0.2 module under construction.
    pub module: Module,
    /// Dense `StringId -> Sym.raw()` memo (`u32::MAX` when uncached, `#72`).
    pub(crate) sid_to_sym: Vec<u32>,
    /// Dense method index (`MethodIdx`) → interned method name [`Sym`] (`#50`).
    pub(crate) method_names: Vec<Sym>,
    /// Class descriptor (file string id) → class-table index. Grows at
    /// lift time for foreign annotation / catch-type classes (stub entries,
    /// see [`Lifter::class_of_descriptor`]).
    pub(crate) class_to_id: HashMap<abcd_file::StringId, ClassId>,
    /// Dense field index (`FieldIdx`) → `(owning ClassId, FieldId)` (`#50`).
    pub(crate) field_ids: Vec<(ClassId, FieldId)>,
    /// `(literal_array_idx, wrapper_kind)` → pooled [`ConstId`] (memoized).
    pub(crate) lit_cache: HashMap<(u32, resolve::LitWrap), ConstId>,
    /// Cycle guard for nested literal arrays.
    pub(crate) lit_active: BTreeSet<u32>,
    /// Deduplicated `Arc<str>` debug source-code payloads keyed by `StringId` (`#58` `R3-A6`).
    pub(crate) source_code_cache: HashMap<abcd_file::StringId, Arc<str>>,
    /// `_ESModuleRecord` blobs, in class/field iteration order.
    pub(crate) module_datas: Vec<&'f abcd_file::ModuleData>,
    /// `moduleRequestPhaseIdx` blobs, in class/field iteration order.
    pub(crate) module_phases: Vec<&'f abcd_file::ModuleRequestPhase>,
    /// `_ESScopeNamesRecord` fields: `source_file -> scope_names` (first-wins, `#103`).
    pub(crate) scope_name_fields: HashMap<Sym, ConstId>,
    /// Per-class `O(1)` legacy `0.0.0.2` module-var slot index (`#103`).
    pub(crate) class_module_slots: Vec<OnceLock<Box<metadata::LegacyModuleSlotIndex>>>,
    /// Standalone `_ESModuleRecord` `O(1)` legacy `0.0.0.2` slot index (`#103`).
    pub(crate) standalone_module_slots: OnceLock<Box<metadata::LegacyModuleSlotIndex>>,
}

impl<'f> Lifter<'f> {
    fn new(file: &'f File) -> Self {
        let dialect = match file.dialect() {
            Some(abcd_file::Dialect::Static) => abcd_ir::Dialect::StaticArkTS,
            Some(abcd_file::Dialect::DynamicModern | abcd_file::Dialect::DynamicLegacy) | None => {
                abcd_ir::Dialect::DynamicEcma
            }
        };
        Self {
            file,
            module: Module::with_dialect(dialect),
            sid_to_sym: vec![u32::MAX; file.strings.len()],
            method_names: Vec::new(),
            class_to_id: HashMap::new(),
            field_ids: Vec::new(),
            lit_cache: HashMap::new(),
            lit_active: BTreeSet::new(),
            source_code_cache: HashMap::new(),
            module_datas: Vec::new(),
            module_phases: Vec::new(),
            scope_name_fields: HashMap::new(),
            class_module_slots: Vec::new(),
            standalone_module_slots: OnceLock::new(),
        }
    }

    /// Intern a file-level string as a symbol in `O(1)` when cached, preserving
    /// lone-surrogate MUTF-8 bytes losslessly (`#30`, `#72`).
    pub(crate) fn sym_of_file_sid(&mut self, sid: abcd_file::StringId) -> Option<Sym> {
        let idx = sid.index();
        if let Some(&cached) = self.sid_to_sym.get(idx)
            && cached != u32::MAX
        {
            return Some(Sym::new(cached));
        }
        let sym = if let Some(raw) = self.file.strings.raw_mutf8(sid) {
            let lossy = self.file.strings.resolve(sid)?;
            self.module.sym.intern_lossy_raw(lossy, raw)
        } else {
            let s = self.file.strings.as_str(sid)?;
            self.module.sym.intern(s)
        };
        if let Some(slot) = self.sid_to_sym.get_mut(idx) {
            *slot = sym.raw();
        }
        Some(sym)
    }

    /// Intern a string literal as a symbol.
    pub(crate) fn sym(&mut self, s: &str) -> Sym {
        self.module.sym.intern(s)
    }

    /// The class-table index of a file descriptor, appending a minimal
    /// stub entry for descriptors the file never declared (annotation
    /// classes are commonly foreign; documented policy — the class
    /// exists in the module's table so `Annotation.class` /
    /// `AnnValue::Class` / `StaticTy::Reference` stay table-local).
    pub(crate) fn class_of_descriptor(&mut self, sid: abcd_file::StringId) -> Option<ClassId> {
        if let Some(&cid) = self.class_to_id.get(&sid) {
            return Some(cid);
        }
        let descriptor = self.sym_of_file_sid(sid)?;
        let cid = ClassId::new(self.module.classes.len() as u32);
        self.module
            .classes
            .push(abcd_ir::ClassData::new(descriptor, descriptor));
        self.class_module_slots.push(OnceLock::new());
        self.class_to_id.insert(sid, cid);
        Some(cid)
    }

    /// Pool a scalar constant (deduplicated via [`abcd_ir::ConstPool::intern`]).
    pub(crate) fn const_scalar(&mut self, c: Const) -> ConstId {
        self.module.consts.intern(c)
    }

    /// Pool a shape constant (array/object/method-ref; structural dedup via
    /// [`abcd_ir::ConstPool::intern`]).
    pub(crate) fn const_shape(&mut self, c: Const) -> ConstId {
        self.module.consts.intern(c)
    }
}

impl<'f> LiftBackend<'f> for Lifter<'f> {
    type Arenas = Module;

    #[inline]
    fn file(&self) -> &'f File {
        self.file
    }

    #[inline]
    fn arenas(&self) -> &Self::Arenas {
        &self.module
    }

    #[inline]
    fn arenas_mut(&mut self) -> &mut Self::Arenas {
        &mut self.module
    }

    #[inline]
    fn backend_method_count(&self) -> usize {
        self.method_names.len()
    }

    #[inline]
    fn backend_method_name(&self, idx: abcd_file::MethodIdx) -> Option<Sym> {
        self.method_names.get(idx.index()).copied()
    }

    #[inline]
    fn backend_field_id(&self, idx: abcd_file::FieldIdx) -> Option<(ClassId, FieldId)> {
        self.field_ids.get(idx.index()).copied()
    }

    #[inline]
    fn backend_field_name(&self, cid: ClassId, fid: FieldId) -> Option<Sym> {
        self.module
            .classes
            .get(cid.index())
            .and_then(|c| c.fields.get(fid.index()))
            .map(|f| f.name)
    }

    #[inline]
    fn backend_sym_of_file_sid(&mut self, sid: abcd_file::StringId) -> Option<Sym> {
        self.sym_of_file_sid(sid)
    }

    #[inline]
    fn backend_sym(&mut self, s: &'static str) -> Sym {
        self.sym(s)
    }

    #[inline]
    fn backend_class_of_descriptor(&mut self, sid: abcd_file::StringId) -> Option<ClassId> {
        self.class_of_descriptor(sid)
    }

    #[inline]
    fn backend_const_scalar(&mut self, c: Const) -> ConstId {
        self.const_scalar(c)
    }

    #[inline]
    fn backend_const_shape(&mut self, c: Const) -> ConstId {
        self.const_shape(c)
    }

    #[inline]
    fn backend_resolve_lit_array(
        &mut self,
        table_idx: u32,
        wrap: resolve::LitWrap,
    ) -> Result<ConstId, LiftError> {
        resolve::const_for_literal_array_with_wrap(self, table_idx, wrap)
    }

    #[inline]
    fn backend_try_lit_array_or_null(&mut self, table_idx: u32, wrap: resolve::LitWrap) -> ConstId {
        resolve::const_for_literal_array_with_wrap(self, table_idx, wrap)
            .unwrap_or_else(|_| self.const_scalar(Const::Null))
    }

    #[inline]
    fn backend_this_param_index(&self, fd: &FunctionData) -> Option<usize> {
        abcd_ir::frame::this_param_index(&self.module, fd)
    }

    #[inline]
    fn backend_is_const_bool(&self, cid: ConstId) -> bool {
        matches!(self.module.consts.get(cid), Some(Const::Bool(_)))
    }

    #[inline]
    fn backend_legacy_module_slots(
        &self,
        class_id: ClassId,
    ) -> Option<&metadata::LegacyModuleSlotIndex> {
        metadata::resolve_legacy_module_slots(
            class_id,
            &self.module.classes,
            &self.class_module_slots,
            &self.module.imports,
            &self.module.exports,
            &self.module.module_requests,
            &self.standalone_module_slots,
        )
    }

    #[inline]
    fn backend_record_legacy_modvar_fallback(&mut self, _inst_id: InstId, _sym: Sym) {}

    fn backend_lookup_scope_names(
        &self,
        class_id: ClassId,
        source_file: Option<Sym>,
    ) -> Option<ConstId> {
        self.module
            .classes
            .get(class_id.index())
            .and_then(|c| c.scope_names)
            .or_else(|| source_file.and_then(|sf| self.scope_name_fields.get(&sf).copied()))
    }

    fn backend_resolve_source_code(&mut self, sid: abcd_file::StringId) -> Option<Arc<str>> {
        if let Some(arc) = self.source_code_cache.get(&sid) {
            return Some(Arc::clone(arc));
        }
        let s = self.file.strings.resolve(sid)?;
        let arc: Arc<str> = Arc::from(s);
        self.source_code_cache.insert(sid, Arc::clone(&arc));
        Some(arc)
    }
}

/// Lift an entire ABC file into an [`abcd_ir::Module`] using [`LiftOptions::default`].
pub fn lift_file(file: &File) -> Result<Module, LiftError> {
    lift_file_with_options(file, &LiftOptions::default())
}

/// Lift an entire ABC file into an [`abcd_ir::Module`] with explicit [`LiftOptions`].
pub fn lift_file_with_options(file: &File, options: &LiftOptions) -> Result<Module, LiftError> {
    lift_file_impl(file, options, false)
}

/// Force-enable parallel method lifting regardless of file size (used by unit tests).
#[cfg(test)]
pub(crate) fn lift_file_forced_parallel(
    file: &File,
    retain_tail_capacity: bool,
) -> Result<Module, LiftError> {
    lift_file_impl(
        file,
        &LiftOptions {
            retain_tail_capacity,
            parallel: true,
        },
        true,
    )
}

fn lift_file_impl(
    file: &File,
    options: &LiftOptions,
    force_parallel: bool,
) -> Result<Module, LiftError> {
    let mut lf = Lifter::new(file);

    let total_classes = file.classes.len();
    let total_methods: usize = file.classes.values().map(|c| c.methods.len()).sum();
    let total_fields: usize = file.classes.values().map(|c| c.fields.len()).sum();
    let total_bytecodes: usize = file
        .all_methods()
        .filter_map(|(_, m)| m.body.as_ref())
        .map(MethodBody::insn_count)
        .sum();
    let use_parallel = force_parallel
        || (options.parallel
            && total_methods >= PARALLEL_MIN_METHODS
            && total_bytecodes >= PARALLEL_MIN_BYTECODES);
    if options.retain_tail_capacity {
        lf.module
            .classes
            .reserve(total_classes.saturating_add((total_classes >> 4).max(16)));
        lf.module
            .functions
            .reserve(total_methods.saturating_add((total_methods >> 4).max(64)));
    } else {
        lf.module.classes.reserve(total_classes);
        lf.module.functions.reserve_exact(total_methods);
    }
    lf.method_names.reserve_exact(total_methods);
    lf.class_to_id.reserve(total_classes);
    lf.class_module_slots.reserve(total_classes);
    lf.field_ids.reserve_exact(total_fields);
    if !use_parallel {
        let est_blocks = total_methods.saturating_mul(5);
        if options.retain_tail_capacity {
            let bc_extra = (total_bytecodes >> 4).max(64);
            let blk_extra = (est_blocks >> 4).max(64);
            lf.module
                .insts
                .reserve(total_bytecodes.saturating_add(bc_extra));
            lf.module
                .values
                .reserve(total_bytecodes.saturating_add(bc_extra));
            lf.module
                .blocks
                .reserve(est_blocks.saturating_add(blk_extra));
        } else {
            lf.module.insts.reserve_exact(total_bytecodes);
            lf.module.values.reserve_exact(total_bytecodes);
            lf.module.blocks.reserve_exact(est_blocks);
        }
    }

    // Pass 1 — dense identity tables (`#50`): pre-fill the class-table and
    // function-table slots in `file.classes` × declaration order (`== MethodIdx`
    // and `FieldIdx` order) so every forward reference resolves in O(1) and
    // pass 2 ASSIGNS by reserved index (stub-append of foreign descriptors can
    // never disturb the reservation).
    for (class_sid, class) in &file.classes {
        let cid = ClassId::new(lf.module.classes.len() as u32);
        lf.class_to_id.insert(*class_sid, cid);
        let descriptor = lf
            .sym_of_file_sid(class.descriptor)
            .unwrap_or_else(|| lf.sym("<unnamed-class>"));
        lf.module
            .classes
            .push(abcd_ir::ClassData::new(descriptor, descriptor));
        lf.class_module_slots.push(OnceLock::new());
        for method in &class.methods {
            let name = lf
                .sym_of_file_sid(method.name)
                .unwrap_or_else(|| lf.sym("<unnamed>"));
            lf.method_names.push(name);
            let kind = metadata::function_kind(method);
            lf.module.functions.push(FunctionData::new(cid, name, kind));
        }
        for (fi, _field) in class.fields.iter().enumerate() {
            lf.field_ids.push((cid, FieldId::new(fi as u32)));
        }
    }

    // Pass 2a — lift all class headers (`ClassData` with `es_module`,
    // `scope_names`, `annotations`, `fields`, and `methods`) plus standalone
    // `_ESModuleRecord` / `_ModuleRequestPhaseRecord` / `_ESScopeNamesRecord`
    // tables BEFORE lifting any method body (`D3`). This ensures enclosing
    // `ClassData` (`source_lang` for `FrameSlots`, `es_module` slot tables for
    // legacy `0.0.0.2` module-var opcodes, and `scope_names`) is populated
    // immediately when translating methods.
    let mut func_base = 0u32;
    let mut class_schedule: Vec<(ClassId, &abcd_file::Class, u32)> =
        Vec::with_capacity(total_classes);
    for (&class_sid, class) in &file.classes {
        let class_id = metadata::lift_class_header(&mut lf, class_sid, class, func_base)?;
        class_schedule.push((class_id, class, func_base));
        func_base += class.methods.len() as u32;
    }
    metadata::emit_module_records(&mut lf)?;

    // Pass 2b — lift method bodies either in parallel (with deterministic
    // Pass-2c event-stream replay, `#84`) or sequentially.
    if use_parallel {
        parallel::lift_methods_parallel(
            &mut lf,
            &class_schedule,
            total_methods,
            options.retain_tail_capacity,
        )?;
    } else {
        for (class_id, class, base) in class_schedule {
            for (mi, method) in class.methods.iter().enumerate() {
                let func_id = FuncId::new(base + mi as u32);
                let fd = lift_method_with(&mut lf, class_id, method, func_id)?;
                lf.module.functions[func_id.index()] = fd;
            }
        }
    }

    if !options.retain_tail_capacity {
        for cls in &mut lf.module.classes {
            cls.interfaces.shrink_to_fit();
            cls.fields.shrink_to_fit();
            cls.methods.shrink_to_fit();
            cls.annotations.shrink_to_fit();
            if let Some(es) = &mut cls.es_module {
                es.imports.shrink_to_fit();
                es.exports.shrink_to_fit();
                es.module_requests.shrink_to_fit();
            }
        }
        lf.module.classes.shrink_to_fit();
        lf.module.functions.shrink_to_fit();
        lf.module.blocks.shrink_to_fit();
        lf.module.insts.shrink_to_fit();
        lf.module.values.shrink_to_fit();
        lf.module.imports.shrink_to_fit();
        lf.module.exports.shrink_to_fit();
        lf.module.module_requests.shrink_to_fit();
    }

    Ok(lf.module)
}

/// Lift a single method body against `lf` (sequential [`Lifter`] or worker-local
/// [`parallel::MethodLiftCtx`]), returning the completed [`FunctionData`].
pub(crate) fn lift_method_with<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    class_id: ClassId,
    method: &'f Method,
    _func_id: FuncId,
) -> Result<FunctionData, LiftError> {
    let name = lf
        .backend_sym_of_file_sid(method.name)
        .unwrap_or_else(|| lf.backend_sym("<unnamed>"));
    let kind = metadata::function_kind(method);
    let mut fd = FunctionData::new(class_id, name, kind);
    fd.sig = metadata::signature(lf, method);
    fd.modifiers = metadata::modifiers(method.access_flags);
    fd.is_external = method.is_external;
    fd.annotations = metadata::lift_annotations(lf, &method.annotations);

    let Some(body) = method.body.as_ref() else {
        // v0.1 hard-errors on any body-less method. v0.2 keeps the hard
        // error for NON-external methods (parity) but lifts external
        // (native/foreign) declarations into bodyless external
        // functions — the verifier's MissingBody rule allows exactly
        // that shape (documented divergence: strictly more permissive,
        // zero corpus impact).
        if !method.is_external {
            return Err(LiftError::NoBody);
        }
        fd.params = metadata::external_params(lf, method);
        fd.params.shrink_to_fit();
        fd.annotations.shrink_to_fit();
        return Ok(fd);
    };

    // Borrow `Decoded` in O(1) or transiently decode `MethodSpan` ONCE for this
    // method (`#49`), dropping any temporary `Vec<Bytecode>` when returning.
    let bytecodes_cow = body.bytecodes();
    let bytecodes: &[abcd_isa::Bytecode] = &bytecodes_cow;
    if bytecodes.is_empty() {
        return Err(LiftError::EmptyBytecode);
    }

    // Arity and arg-slot base come from the decoded code header (B5).
    // The u32 → u16 conversions are checked: overflow is a hard error,
    // never a truncation.
    let param_count =
        u16::try_from(body.num_args).map_err(|_| LiftError::ParamCountOverflow(body.num_args))?;
    let arg_base = u16::try_from(body.num_vregs).map_err(|_| LiftError::FrameTooLarge {
        num_vregs: body.num_vregs,
        num_args: body.num_args,
    })?;
    let frame_limit = arg_base
        .checked_add(param_count)
        .ok_or(LiftError::FrameTooLarge {
            num_vregs: body.num_vregs,
            num_args: body.num_args,
        })?;

    let raw_cfg = build_cfg(bytecodes, &body.try_blocks)?;

    // #32: If raw block 0 (bytecode offset 0) has any incoming edge — a
    // loop back-edge (`jmp 0` / `jnez 0`), a single-block self-loop at 0,
    // or an exception handler targeting offset 0 — synthesize a pure,
    // zero-predecessor pre-entry trampoline at `fd.blocks[0]` that
    // unconditionally branches to `header0` (`block_map[0]`, `fd.blocks[1]`).
    // When raw block 0 has no incoming edges, `entry_block` IS `block_map[0]`
    // so block/inst/value numbering stays 100% unchanged.
    let needs_pre_entry = raw_cfg
        .blocks
        .iter()
        .any(|rb| rb.succs.contains(&0) || rb.catch_succs.contains(&0))
        || body
            .try_blocks
            .iter()
            .flat_map(|tb| &tb.catches)
            .any(|c| c.handler == 0);

    // Create the function's blocks: optional synthetic pre-entry first,
    // then dense raw block index → IR BlockId in leader order (`R3-A4`).
    let mut block_map: Vec<BlockId> = Vec::with_capacity(raw_cfg.blocks.len());
    let (entry_block, block_base) = {
        let blocks = lf.arenas_mut().blocks_mut();
        let entry = BlockId::new(blocks.len() as u32);
        let base = entry.index();
        blocks.push(Block::default());
        fd.blocks.push(entry);
        if needs_pre_entry {
            for _ in 0..raw_cfg.blocks.len() {
                let bb = BlockId::new(blocks.len() as u32);
                blocks.push(Block::default());
                fd.blocks.push(bb);
                block_map.push(bb);
            }
        } else {
            block_map.push(entry);
            for _ in 1..raw_cfg.blocks.len() {
                let bb = BlockId::new(blocks.len() as u32);
                blocks.push(Block::default());
                fd.blocks.push(bb);
                block_map.push(bb);
            }
        }
        (entry, base)
    };
    let num_fn_blocks = fd.blocks.len();

    // Predecessor edges (both kinds, materialized before SSA — the
    // empty-phi-free construction). Normal edges from terminator
    // successors (plus `pre_entry -> header0` when synthesized);
    // Exceptional edges for every (protected block → handler) pair (the
    // verifier's MissingExceptionalPred rule).
    {
        let blocks = lf.arenas_mut().blocks_mut();
        if needs_pre_entry {
            let header0 = block_map[0];
            blocks[header0.index()].preds.push(Edge {
                from: entry_block,
                kind: EdgeKind::Normal,
            });
        }
        for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
            let ir_block = block_map[bi];
            for &succ_bi in &raw_block.succs {
                let succ_bb = block_map[succ_bi];
                let edge = Edge {
                    from: ir_block,
                    kind: EdgeKind::Normal,
                };
                if !blocks[succ_bb.index()].preds.contains(&edge) {
                    blocks[succ_bb.index()].preds.push(edge);
                }
            }
            for &catch_bi in &raw_block.catch_succs {
                let catch_bb = block_map[catch_bi];
                let edge = Edge {
                    from: ir_block,
                    kind: EdgeKind::Exceptional,
                };
                if !blocks[catch_bb.index()].preds.contains(&edge) {
                    blocks[catch_bb.index()].preds.push(edge);
                }
            }
        }
    }

    // Try regions (protected ranges + handler blocks) from the original
    // try_blocks.
    fd.try_regions = build_try_regions(lf, body, &raw_cfg, &block_map)?;

    // SSA construction context.
    let mut fx = translate::FnLift::new(
        lf,
        method,
        body,
        class_id,
        bytecodes.len(),
        frame_limit,
        block_base,
        num_fn_blocks,
        block_map,
        raw_cfg,
    );

    // N13 handler seeding: exception dispatch physically delivers the
    // thrown object in the ACCUMULATOR at handler entry (vendor
    // `SET_ACC(exception)`, interpreter_assembly.cpp:7860-7863). Seed
    // every catch handler's acc location with a fresh ExceptionParam
    // value BEFORE any block is translated; the value is recorded on
    // the region's Catch (v0.2's first-class form of v0.1's
    // exception_values).
    {
        let mut handlers: Vec<BlockId> = fd
            .try_regions
            .iter()
            .flat_map(|region| region.catches.iter().map(|c| c.handler))
            .collect();
        handlers.sort_unstable();
        handlers.dedup();
        for handler in handlers {
            let val = fx.new_value(ValueDef::ExceptionParam(handler), Ty::Any);
            fx.ssa.write_variable(RegOrAcc::Acc, handler, val);
            for region in &mut fd.try_regions {
                for catch in &mut region.catches {
                    if catch.handler == handler {
                        catch.exception = val;
                    }
                }
            }
        }
    }

    // Entry seeding (B5 + the ABI top-slot convention): arguments arrive
    // in `Reg(num_vregs + i)`; bind each to a fresh Param value.
    // Frame-slot model (T4/§5.3, canonical — abcd_ir::frame): the
    // leading params are the vendored implicit frame slots
    // `[func][new.target][this]` (per the callee's
    // `L_ESCallTypeAnnotation;` callType bits; absent → the `0xF`
    // default, the es2abc shape), then the source formals.
    for i in 0..param_count {
        let ty = method
            .arg_types
            .get(i as usize)
            .map(|t| metadata::ty_of(fx.lf, t))
            .unwrap_or(Ty::Any);
        let val = fx.new_value(ValueDef::Param(i), ty);
        fx.ssa
            .write_variable(RegOrAcc::Reg(arg_base + i), entry_block, val);
        fd.params.push(val);
    }

    // N67: `ldthis` reads the frame's thisObj (vendor
    // `EcmaInterpreter::GetThis`, interpreter-inl.cpp:7907-7912), bound
    // from the this-role frame slot — `params[2]` under the `0xF`
    // default, annotation-aware via abcd_ir::frame::this_param_index;
    // `None` (→ undefined) for shapes the model can't cover
    // (documented conservative fallback). NOT `params[0]` — the FUNC
    // slot under `0xF` (the superseded convention, N66).
    fx.this_param = fx.lf.backend_this_param_index(&fd).map(|i| fd.params[i]);

    // The entry block has no predecessors: seal it immediately. When a
    // synthetic pre-entry trampoline was inserted (#32), emit its single
    // unconditional Branch into `header0` (`pc: None` so debug line/scope
    // extents attach exclusively to real bytecode instructions).
    fx.ssa.seal_block(entry_block, fx.lf.arenas_mut());
    if needs_pre_entry {
        let header0 = fx.block_map[0];
        fx.emit_void(entry_block, abcd_ir::Op::Branch { dest: header0 }, None);
    }

    // Translate bytecodes block by block.
    for bi in 0..fx.raw_cfg.blocks.len() {
        let ir_block = fx.block_map[bi];
        let (start, end) = {
            let raw = &fx.raw_cfg.blocks[bi];
            (raw.start, raw.end)
        };
        for (off, bc) in bytecodes[start..end].iter().enumerate() {
            translate::translate_bytecode(&mut fx, bc, start + off, bi, ir_block)?;
        }

        // Every block must end in an explicit terminator; bytecode
        // instructions such as lda/sta may disappear during SSA
        // lifting, so inspect the emitted IR rather than the last
        // source instruction.
        let terminated = fx.lf.arenas().blocks()[ir_block.index()]
            .insts
            .last()
            .and_then(|&iid| fx.lf.arenas().insts().get(iid.index()))
            .is_some_and(|inst| inst.op.is_terminator());
        if !terminated {
            let succs = fx.raw_cfg.blocks[bi].succs.clone();
            match succs.as_slice() {
                [succ_bi] => {
                    let dest = fx.block_map[*succ_bi];
                    fx.emit_void(ir_block, abcd_ir::Op::Branch { dest }, None);
                }
                [] => {
                    fx.emit_void(ir_block, abcd_ir::Op::Unreachable, None);
                }
                _ => {
                    fx.emit_void(ir_block, abcd_ir::Op::Unreachable, None);
                }
            }
        }

        // Seal successors whose predecessors have all been processed
        // (`entry_block` and `block_map[0..=bi]` have monotonically increasing
        // `BlockId`s <= `ir_block`, giving an O(1) predecessor check).
        let (succs, catch_succs) = {
            let raw = &fx.raw_cfg.blocks[bi];
            (raw.succs.clone(), raw.catch_succs.clone())
        };
        for &succ_bi in succs.iter().chain(catch_succs.iter()) {
            let succ_bb = fx.block_map[succ_bi];
            if !fx.ssa.is_sealed(succ_bb) {
                let all_preds_done = fx.lf.arenas().blocks()[succ_bb.index()]
                    .preds
                    .iter()
                    .all(|edge| edge.from.index() <= ir_block.index());
                if all_preds_done {
                    fx.ssa.seal_block(succ_bb, fx.lf.arenas_mut());
                }
            }
        }
    }

    // Seal any remaining unsealed blocks in raw-block order (`N20`).
    for bi in 0..fx.raw_cfg.blocks.len() {
        let bb = fx.block_map[bi];
        if !fx.ssa.is_sealed(bb) {
            fx.ssa.seal_block(bb, fx.lf.arenas_mut());
        }
    }

    // Record the function's frame-initial constant ValueIds (#30).
    fd.frame_init_consts = fx.ssa.frame_init_consts.clone();

    // N18 dead-island sweep (exception-augmented reachability).
    sweep_dead_blocks(&mut fd, fx.lf.arenas_mut(), block_base);

    // Finalize iterative trivial-phi cascade (including any phis reduced to a
    // single live predecessor by `sweep_dead_blocks`) and rewrite all surviving
    // instruction operands (`Op::for_each_operand_mut`) and debug references.
    fx.ssa.finalize_function_data(fx.lf.arenas_mut(), &mut fd);

    // Debug data (line/column tables keyed by the lifted InstIds,
    // locals with scope extents, param names, source file/code).
    metadata::finish_debug(&mut fx, &mut fd);

    fd.params.shrink_to_fit();
    fd.frame_init_consts.shrink_to_fit();
    fd.blocks.shrink_to_fit();
    for region in &mut fd.try_regions {
        region.protected.shrink_to_fit();
        region.catches.shrink_to_fit();
    }
    fd.try_regions.shrink_to_fit();
    fd.annotations.shrink_to_fit();
    if let Some(dbg) = &mut fd.debug {
        dbg.line_table.shrink_to_fit();
        dbg.column_table.shrink_to_fit();
        dbg.local_names.shrink_to_fit();
        dbg.param_names.shrink_to_fit();
    }
    {
        let blocks = fx.lf.arenas_mut().blocks_mut();
        for &bid in &fd.blocks {
            let blk = &mut blocks[bid.index()];
            blk.insts.shrink_to_fit();
            blk.preds.shrink_to_fit();
        }
    }

    Ok(fd)
}

/// Build structured try regions from the original bytecode `try_blocks`.
/// Catch exception values start as a placeholder and are filled by the
/// N13 handler seeding in [`lift_method_with`].
fn build_try_regions<'f, B: LiftBackend<'f>>(
    lf: &mut B,
    body: &MethodBody,
    raw_cfg: &RawCfg,
    block_map: &[BlockId],
) -> Result<Vec<TryRegion>, LiftError> {
    let mut regions = Vec::with_capacity(body.try_blocks.len());

    for try_block in &body.try_blocks {
        let try_start = try_block.start as usize;
        let try_end = try_start.saturating_add(try_block.len as usize);

        // All IR blocks overlapping `[try_start, try_end)` are protected (`O(log B + |protected|)`).
        let first_bi = raw_cfg.blocks.partition_point(|b| b.end <= try_start);
        let end_bi = raw_cfg.blocks.partition_point(|b| b.start < try_end);
        let protected = if first_bi < end_bi {
            block_map
                .get(first_bi..end_bi)
                .map(<[BlockId]>::to_vec)
                .unwrap_or_else(|| {
                    (first_bi..end_bi)
                        .filter_map(|bi| block_map.get(bi).copied())
                        .collect()
                })
        } else {
            Vec::new()
        };

        let mut catches = Vec::with_capacity(try_block.catches.len());
        for c in &try_block.catches {
            let Some(&handler_bi) = raw_cfg.leader_to_block.get(&(c.handler as usize)) else {
                continue;
            };
            let Some(&handler) = block_map.get(handler_bi) else {
                continue;
            };
            let type_class = match c.type_class {
                Some(sid) => Some(
                    lf.backend_class_of_descriptor(sid)
                        .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?,
                ),
                None => None,
            };
            catches.push(Catch {
                handler,
                // Filled by the N13 handler seeding (the placeholder is never
                // observed: every handler block is seeded before translation,
                // and the sweep prunes dead catches afterwards).
                exception: ValueId::new(u32::MAX),
                type_class,
            });
        }

        regions.push(TryRegion { protected, catches });
    }

    Ok(regions)
}

/// N18 dead-island sweep: remove blocks unreachable over the exception-augmented
/// successor relation (`abcd_ir::normal_succs_inline` + `TryRegion` handlers)
/// and repair preds, phi entries, and try regions of the survivors.
fn sweep_dead_blocks<A: IrArenas>(fd: &mut FunctionData, arenas: &mut A, block_base: usize) {
    use std::collections::VecDeque;

    let num_blocks = fd.blocks.len();
    let Some(&entry) = fd.blocks.first() else {
        return;
    };
    let rel_of = |bb: BlockId| -> Option<usize> {
        bb.index()
            .checked_sub(block_base)
            .filter(|&rel| rel < num_blocks)
    };

    let mut exc_succs: Vec<Vec<BlockId>> = vec![Vec::new(); num_blocks];
    for region in &fd.try_regions {
        for &prot in &region.protected {
            let Some(pi) = rel_of(prot) else {
                continue;
            };
            for catch in &region.catches {
                if rel_of(catch.handler).is_some() && !exc_succs[pi].contains(&catch.handler) {
                    exc_succs[pi].push(catch.handler);
                }
            }
        }
    }

    let mut reachable = vec![false; num_blocks];
    let mut reachable_count = 0usize;
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    if let Some(ei) = rel_of(entry) {
        reachable[ei] = true;
        reachable_count = 1;
        queue.push_back(entry);
    }

    while let Some(bb) = queue.pop_front() {
        let normal = arenas.blocks()[bb.index()]
            .insts
            .last()
            .and_then(|&iid| arenas.insts().get(iid.index()))
            .map(|inst| abcd_ir::normal_succs_inline(&inst.op))
            .unwrap_or(([BlockId::new(0); 2], 0));
        for &succ in &normal.0[..normal.1] {
            if let Some(si) = rel_of(succ)
                && !reachable[si]
            {
                reachable[si] = true;
                reachable_count += 1;
                queue.push_back(succ);
            }
        }
        if let Some(bi) = rel_of(bb) {
            for &handler in &exc_succs[bi] {
                if let Some(hi) = rel_of(handler)
                    && !reachable[hi]
                {
                    reachable[hi] = true;
                    reachable_count += 1;
                    queue.push_back(handler);
                }
            }
        }
    }

    if reachable_count == num_blocks {
        return;
    }

    let is_dead = |bb: BlockId| -> bool { rel_of(bb).is_none_or(|ri| !reachable[ri]) };

    {
        let (blocks, insts) = arenas.blocks_and_insts_mut();
        for &bb in &fd.blocks {
            if is_dead(bb) {
                blocks[bb.index()].insts.shrink_to_fit();
                blocks[bb.index()].preds.shrink_to_fit();
                continue;
            }
            blocks[bb.index()].preds.retain(|e| !is_dead(e.from));
            for &iid in &blocks[bb.index()].insts {
                let Some(inst) = insts.get_mut(iid.index()) else {
                    continue;
                };
                if let abcd_ir::Op::Phi { entries } = &mut inst.op {
                    entries.retain(|(e, _)| !is_dead(e.from));
                } else {
                    break;
                }
            }
        }
    }

    fd.blocks.retain(|&bb| !is_dead(bb));
    for region in &mut fd.try_regions {
        region.protected.retain(|&bb| !is_dead(bb));
        region.catches.retain(|c| !is_dead(c.handler));
    }
    fd.try_regions
        .retain(|r| !r.protected.is_empty() && !r.catches.is_empty());
}

/// Emit an IR instruction in `block` (helper used across modules).
pub(crate) fn emit_inst<A: IrArenas>(
    arenas: &mut A,
    block: BlockId,
    op: abcd_ir::Op,
    loc: Option<abcd_ir::Loc>,
) -> (InstId, Option<ValueId>) {
    let has_result = op.has_result();
    let is_phi = op.is_phi();
    let inst_id = InstId::new(arenas.insts().len() as u32);
    let result = if has_result {
        let values = arenas.values_mut();
        let val = ValueId::new(values.len() as u32);
        values.push(Value {
            def: ValueDef::Inst(inst_id),
            ty: Ty::Any,
        });
        Some(val)
    } else {
        None
    };
    arenas.insts_mut().push(Inst {
        op,
        result,
        block,
        loc,
    });
    let (blocks, insts) = arenas.blocks_and_insts_mut();
    let bb = &mut blocks[block.index()];
    if is_phi {
        // Phis form the block's leading prefix: insert after the
        // existing phi run (a Braun phi can materialize for a block
        // whose translation already started elsewhere).
        let phi_len = bb
            .insts
            .iter()
            .take_while(|&&iid| insts.get(iid.index()).is_some_and(|i| i.op.is_phi()))
            .count();
        bb.insts.insert(phi_len, inst_id);
    } else {
        bb.insts.push(inst_id);
    }
    (inst_id, result)
}

#[cfg(test)]
mod tests;
