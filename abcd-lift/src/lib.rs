//! # abcd-lift — lift converter: `abcd_file::File` → `abcd_ir::Module`
//!
//! IR v0.2 migration plan P1 (design/ir-v0.2.md §8, design/ir.md §7):
//! the format-aware conversion layer that decodes v0.1's container model
//! into the format-independent v0.2 IR. This crate is the ONLY component
//! that imports both sides (`abcd-file` + `abcd-isa` on the container
//! end, `abcd-ir` on the semantic end).
//!
//! The conversion ports v0.1 `abcd_ir::lift`'s battle-proven semantics
//! (VM oracle 1149/1149 on both pipelines) into v0.2's types:
//!
//! - **Entity resolution → [`SymbolTable`] + [`FuncId`]** — strings are
//!   content-keyed symbols; a method reference is a [`FuncId`] into the
//!   module's function table (the S1/N2 lesson: the file's method table
//!   is built FIRST, then bytecode/literal offsets resolve to indices —
//!   never name-keyed, never raw offsets).
//! - **Literal arrays → [`ConstPool`]** — typed [`Const`] trees
//!   (nested arrays included; typed arrays resolved to real trees, N52:
//!   no raw offsets); method references inside literal arrays become
//!   [`Const::MethodRef`]`(FuncId)`.
//! - **Module records → [`ImportDecl`]/[`ExportDecl`]** — the N7 model:
//!   `_ESModuleRecord` field blobs (`FieldValue::ModuleData`) parsed into
//!   declarations with `module_request_idx` resolved to specifier syms;
//!   `moduleRequestPhaseIdx` blobs become
//!   [`ModuleRequest`](abcd_ir::ModuleRequest)`{specifier, lazy}`;
//!   `_ESScopeNamesRecord` fields land on
//!   [`DebugData::scope_names`](abcd_ir::DebugData) of the functions
//!   whose source file matches the field name.
//! - **Annotations** — the four file buckets merge into ONE list per
//!   attach site, in the documented order: `compile_time`, `runtime`,
//!   `compile_time_type`, `runtime_type`.
//! - **Debug** — the LNP dual stream becomes
//!   [`DebugData`](abcd_ir::DebugData): line/column keyed by the lifted
//!   [`InstId`](abcd_ir::InstId)s (also on `Inst.loc`), local names with
//!   their #5 scope extents mapped onto lifted instructions, param
//!   names, source file/code.
//! - **CFG + Braun SSA** — v0.1's exact semantics: param seeding from
//!   the code-header `num_args` (u32→u16 checked, B5), entry param
//!   seeding, frame-initial values as CONSTANTS
//!   ([`Const::Undefined`](abcd_ir::Const) for vregs,
//!   [`Const::Hole`](abcd_ir::Const) for acc-read-before-write — P3-T7,
//!   represented as `ValueDef::Const`, no seeding instructions), handler
//!   [`ExceptionParam`](abcd_ir::ValueDef) seeding (N13), Braun
//!   construction with preds known before SSA (empty-phi-free).
//! - **Try regions** — structured [`TryRegion`](abcd_ir::TryRegion)s
//!   plus materialized [`EdgeKind::Exceptional`](abcd_ir::EdgeKind)
//!   edges in `Block.preds` for EVERY (protected block → handler) pair
//!   (the verifier's `MissingExceptionalPred` rule), and the N18
//!   dead-island sweep over augmented reachability.
//! - **Opcode coverage** — every opcode v0.1's lift handles, mapped to
//!   v0.2 ops per the (v2-P0.5-grown) taxonomy; deprecated opcodes fold
//!   to the modern ops (v0.1 convention). The full mapping table lives
//!   in `translate.rs`'s header docs; the machine-checked version is
//!   `compare.rs`'s canonicalization.
//!
//! Library rule (mirroring abcd-ir): no panics on data; every fallible
//! finding is a [`LiftError`].

#![deny(missing_docs)]

mod cfg;
mod metadata;
mod resolve;
mod ssa;
mod translate;

use std::collections::{BTreeSet, HashMap};

use abcd_file::{File, Method, MethodBody};
use abcd_ir::{
    Block, BlockId, Catch, ClassId, Const, ConstId, Edge, EdgeKind, FuncId, FunctionData, Inst,
    InstId, Module, Sym, TryRegion, Ty, Value, ValueDef, ValueId,
};

use cfg::{RawCfg, build_cfg};
use ssa::RegOrAcc;

pub use translate::{SuperKeyForm, super_key};

/// Errors that can occur during lifting (v0.1 `LiftError` mirrored
/// where sensible; no panics on data).
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
    /// `ldthisbyname` / `stthisbyname` / `ldthisbyvalue` /
    /// `stthisbyvalue` (abcd-isa-sys/vendor/isa/isa.yaml:1627-1642):
    /// IC-fused `this` property access that es2panda NEVER emits (N51 —
    /// upstream source grep zero hits; the 36-compile matrix shows
    /// `this[k] = v` always compiles to `ldthis` + `stobjbyvalue`).
    /// Corpus coverage is zero, so there is no VM evidence for the IC
    /// semantics — a hard error (maintainer ruling 2026-09-20), never
    /// silently invented.
    #[error(
        "unsupported this-by-* opcode `{0}` (N51): es2panda never emits this IC-fused family and its IC semantics are unsupported — please report this file to the abcd-rs maintainers"
    )]
    UnsupportedThisByAccess(&'static str),
    /// `deprecated.defineclasswithbuffer method_id, imm1:u16, imm2:u16,
    /// v1:in:top, v2:in:top` (abcd-isa-sys/vendor/isa/isa.yaml:1239-1244):
    /// the vendor runtime reads v1 as the LEXENV and v2 as the PROTO
    /// (arkcompiler_ets_runtime-master/ecmascript/interpreter/
    /// interpreter_assembly.cpp:4622-4648,
    /// `HandleDeprecatedDefineclasswithbufferPrefId16Imm16Imm16V8V8`),
    /// but both lifters historically took v1 as the base (proto) and
    /// DROPPED v2 — double role corruption (N54). Corpus coverage is
    /// zero (reference.pa grep: none), so there is no evidence path
    /// for a corrected lift — a hard error (maintainer ruling N8/N51:
    /// hard error, never a warning, never silent), mirroring v0.1.
    #[error(
        "unsupported opcode `deprecated.defineclasswithbuffer` (N54): the vendor runtime reads v1=lexenv, v2=proto (interpreter_assembly.cpp:4622-4648) and zero corpus coverage makes the corrected roles unverifiable — please report this file to the abcd-rs maintainers"
    )]
    UnsupportedDeprecatedDefineClassWithBuffer,
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
}

/// The module-level conversion state: the v0.2 module under
/// construction plus the identity tables built in pass 1.
pub(crate) struct Lifter<'f> {
    /// The file being lifted.
    pub file: &'f File,
    /// The v0.2 module under construction.
    pub module: Module,
    /// Method source-file offset → function-table index (S1/N2: method
    /// identity is the offset; references resolve offset → [`FuncId`]).
    /// First-wins on duplicate offsets (hand-built files use offset 0).
    method_to_func: HashMap<u32, FuncId>,
    /// Class descriptor (file string id) → class-table index. Grows at
    /// lift time for annotation-only classes (stub entries, see
    /// [`Lifter::class_of_descriptor`]).
    pub(crate) class_to_id: HashMap<abcd_file::StringId, ClassId>,
    /// Field source-file offset → (owning class, field index) — for
    /// enum-valued annotation elements (`AnnValue::Field`).
    pub(crate) field_to_id: HashMap<u32, (ClassId, u32)>,
    /// Class descriptor (file string id) → its first method's reserved
    /// [`FuncId`] (method i of the class is `base + i` — exact even for
    /// hand-built files with duplicate method offsets).
    pub(crate) func_bases: HashMap<abcd_file::StringId, u32>,
    /// Scalar-constant dedup (a lift-layer policy; the pool itself is
    /// append-only).
    scalar_consts: HashMap<ScalarKey, ConstId>,
    /// Shape-constant (array/object trees) dedup — linear scan over
    /// structural equality (few shapes per file).
    shape_consts: Vec<(Const, ConstId)>,
    /// Literal-array table index → converted shape tree (memoized).
    pub(crate) lit_cache: HashMap<u32, Const>,
    /// Cycle guard for nested literal arrays.
    pub(crate) lit_active: BTreeSet<u32>,
    /// `_ESModuleRecord` blobs, in class/field iteration order.
    pub(crate) module_datas: Vec<&'f abcd_file::ModuleData>,
    /// `moduleRequestPhaseIdx` blobs, in class/field iteration order.
    pub(crate) module_phases: Vec<&'f abcd_file::ModuleRequestPhase>,
    /// `_ESScopeNamesRecord` fields: (source-file name, scope-names
    /// constant), in class/field iteration order.
    pub(crate) scope_name_fields: Vec<(Sym, ConstId)>,
}

/// Content key for scalar-constant dedup.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ScalarKey {
    Undefined,
    Hole,
    Null,
    Bool(bool),
    Number(u64),
    String(Sym),
    BigInt(Sym),
}

impl<'f> Lifter<'f> {
    fn new(file: &'f File) -> Self {
        Self {
            file,
            module: Module::new(),
            method_to_func: HashMap::new(),
            class_to_id: HashMap::new(),
            field_to_id: HashMap::new(),
            func_bases: HashMap::new(),
            scalar_consts: HashMap::new(),
            shape_consts: Vec::new(),
            lit_cache: HashMap::new(),
            lit_active: BTreeSet::new(),
            module_datas: Vec::new(),
            module_phases: Vec::new(),
            scope_name_fields: Vec::new(),
        }
    }

    /// Intern a file-level string as a symbol.
    pub(crate) fn sym_of_file_sid(&mut self, sid: abcd_file::StringId) -> Option<Sym> {
        let s = self.file.strings.resolve(sid)?;
        Some(self.module.sym.intern(s))
    }

    /// Intern a string literal as a symbol.
    pub(crate) fn sym(&mut self, s: &str) -> Sym {
        self.module.sym.intern(s)
    }

    /// The function-table index of a method offset (pass-1 table).
    pub(crate) fn func_of_method_offset(&self, offset: u32) -> Option<FuncId> {
        self.method_to_func.get(&offset).copied()
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
        self.module.classes.push(abcd_ir::ClassData {
            descriptor,
            name: descriptor,
            modifiers: abcd_ir::Modifiers::NONE,
            source_lang: abcd_ir::SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
        self.class_to_id.insert(sid, cid);
        Some(cid)
    }

    /// Pool a scalar constant (deduplicated).
    pub(crate) fn const_scalar(&mut self, c: Const) -> ConstId {
        let key = match &c {
            Const::Undefined => ScalarKey::Undefined,
            Const::Hole => ScalarKey::Hole,
            Const::Null => ScalarKey::Null,
            Const::Bool(b) => ScalarKey::Bool(*b),
            Const::Number(bits) => ScalarKey::Number(*bits),
            Const::String(s) => ScalarKey::String(*s),
            Const::BigInt(s) => ScalarKey::BigInt(*s),
            other => return self.const_shape(other.clone()),
        };
        if let Some(&id) = self.scalar_consts.get(&key) {
            return id;
        }
        let id = self.module.consts.push(c);
        self.scalar_consts.insert(key, id);
        id
    }

    /// Pool a shape constant (array/object/method-ref tree; structural
    /// dedup).
    pub(crate) fn const_shape(&mut self, c: Const) -> ConstId {
        for (existing, id) in &self.shape_consts {
            if *existing == c {
                return *id;
            }
        }
        let id = self.module.consts.push(c.clone());
        self.shape_consts.push((c, id));
        id
    }

    /// The shared empty object shape (for `createemptyobject`).
    pub(crate) fn empty_object_shape(&mut self) -> ConstId {
        self.const_shape(Const::ObjectLiteral {
            keys: Vec::new(),
            values: Vec::new(),
        })
    }
}

/// Lift an entire ABC file into an IR v0.2 [`Module`].
pub fn lift_file(file: &File) -> Result<Module, LiftError> {
    let mut lf = Lifter::new(file);

    // Pass 1 — identity tables: pre-fill the class-table and
    // function-table slots so every forward reference (DefineFunc,
    // Const::MethodRef, super_class, Type::Reference) resolves to a
    // stable index, and pass 2 ASSIGNS by reserved index (stub-append
    // of foreign descriptors can then never disturb the reservation).
    // Iteration order is the reservation order: classes in file order,
    // methods/fields in declaration order.
    for (class_sid, class) in &file.classes {
        let cid = ClassId::new(lf.module.classes.len() as u32);
        lf.class_to_id.insert(*class_sid, cid);
        lf.func_bases
            .insert(*class_sid, lf.module.functions.len() as u32);
        let descriptor = lf
            .sym_of_file_sid(class.descriptor)
            .unwrap_or_else(|| lf.sym("<unnamed-class>"));
        lf.module.classes.push(abcd_ir::ClassData {
            descriptor,
            name: descriptor,
            modifiers: abcd_ir::Modifiers::NONE,
            source_lang: abcd_ir::SourceLang::EcmaScript,
            super_class: None,
            interfaces: Vec::new(),
            fields: Vec::new(),
            methods: Vec::new(),
            annotations: Vec::new(),
            source_file: None,
        });
        for method in &class.methods {
            let fid = FuncId::new(lf.module.functions.len() as u32);
            lf.method_to_func.entry(method.offset).or_insert(fid);
            let name = lf
                .sym_of_file_sid(method.name)
                .unwrap_or_else(|| lf.sym("<unnamed>"));
            let kind = metadata::function_kind(method);
            lf.module.functions.push(FunctionData::new(cid, name, kind));
        }
        for (fi, field) in class.fields.iter().enumerate() {
            lf.field_to_id
                .entry(field.offset)
                .or_insert((cid, fi as u32));
        }
    }

    // Pass 2 — lift classes (same order as pass 1).
    for class in file.classes.values() {
        metadata::lift_class(&mut lf, class)?;
    }

    // Module records → imports/exports/module-requests.
    metadata::emit_module_records(&mut lf)?;

    Ok(lf.module)
}

/// Lift a single method body into its reserved function-table slot.
pub(crate) fn lift_method<'f>(
    lf: &mut Lifter<'f>,
    class_id: ClassId,
    method: &'f Method,
    func_id: FuncId,
) -> Result<(), LiftError> {
    let name = lf
        .sym_of_file_sid(method.name)
        .unwrap_or_else(|| lf.sym("<unnamed>"));
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
        lf.module.functions[func_id.index()] = fd;
        return Ok(());
    };
    if body.bytecodes.is_empty() {
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
    if arg_base.checked_add(param_count).is_none() {
        return Err(LiftError::FrameTooLarge {
            num_vregs: body.num_vregs,
            num_args: body.num_args,
        });
    }

    let raw_cfg = build_cfg(body).ok_or(LiftError::EmptyBytecode)?;

    // Create the function's blocks: raw block index → IR BlockId.
    let entry_block = BlockId::new(lf.module.blocks.len() as u32);
    lf.module.blocks.push(Block::default());
    fd.blocks.push(entry_block);
    let mut block_map: HashMap<usize, BlockId> = HashMap::new();
    block_map.insert(0, entry_block);
    for bi in 1..raw_cfg.blocks.len() {
        let bb = BlockId::new(lf.module.blocks.len() as u32);
        lf.module.blocks.push(Block::default());
        fd.blocks.push(bb);
        block_map.insert(bi, bb);
    }

    // Predecessor edges (both kinds, materialized before SSA — the
    // empty-phi-free construction). Normal edges from terminator
    // successors; Exceptional edges for every (protected block →
    // handler) pair (the verifier's MissingExceptionalPred rule).
    for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
        let ir_block = block_map[&bi];
        for &succ_bi in &raw_block.succs {
            let succ_bb = block_map[&succ_bi];
            let edge = Edge {
                from: ir_block,
                kind: EdgeKind::Normal,
            };
            if !lf.module.blocks[succ_bb.index()].preds.contains(&edge) {
                lf.module.blocks[succ_bb.index()].preds.push(edge);
            }
        }
        for &catch_bi in &raw_block.catch_succs {
            let catch_bb = block_map[&catch_bi];
            let edge = Edge {
                from: ir_block,
                kind: EdgeKind::Exceptional,
            };
            if !lf.module.blocks[catch_bb.index()].preds.contains(&edge) {
                lf.module.blocks[catch_bb.index()].preds.push(edge);
            }
        }
    }

    // Try regions (protected ranges + handler blocks) from the original
    // try_blocks.
    let try_regions = build_try_regions(body, &raw_cfg, &block_map);
    fd.try_regions = try_regions;

    // SSA construction context.
    let mut fx = translate::FnLift::new(lf, method, body, func_id, block_map, raw_cfg);

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
    fx.this_param = abcd_ir::frame::this_param_index(&fx.lf.module, &fd).map(|i| fd.params[i]);

    // The entry block has no predecessors: seal it immediately.
    fx.ssa.seal_block(entry_block, &mut fx.lf.module);

    // Translate bytecodes block by block.
    let bytecodes = &body.bytecodes;
    for bi in 0..fx.raw_cfg.blocks.len() {
        let ir_block = fx.block_map[&bi];
        let (start, end) = {
            let raw = &fx.raw_cfg.blocks[bi];
            (raw.start, raw.end)
        };
        for idx in start..end {
            let bc = &bytecodes[idx];
            translate::translate_bytecode(&mut fx, bc, idx, ir_block)?;
        }

        // Every block must end in an explicit terminator; bytecode
        // instructions such as lda/sta may disappear during SSA
        // lifting, so inspect the emitted IR rather than the last
        // source instruction.
        let terminated = fx.lf.module.blocks[ir_block.index()]
            .insts
            .last()
            .and_then(|&iid| fx.lf.module.insts.get(iid.index()))
            .is_some_and(|inst| inst.op.is_terminator());
        if !terminated {
            let succs = fx.raw_cfg.blocks[bi].succs.clone();
            match succs.as_slice() {
                [succ_bi] => {
                    let dest = fx.block_map[succ_bi];
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
        // (raw-block-order heuristic, v0.1 parity).
        let (succs, catch_succs) = {
            let raw = &fx.raw_cfg.blocks[bi];
            (raw.succs.clone(), raw.catch_succs.clone())
        };
        for succ_bi in succs.iter().chain(catch_succs.iter()) {
            let succ_bb = fx.block_map[succ_bi];
            if !fx.ssa.is_sealed(succ_bb) {
                let all_preds_done =
                    fx.lf.module.blocks[succ_bb.index()]
                        .preds
                        .iter()
                        .all(|edge| {
                            fx.block_map
                                .iter()
                                .any(|(&rbi, &bb)| bb == edge.from && rbi <= bi)
                        });
                if all_preds_done {
                    fx.ssa.seal_block(succ_bb, &mut fx.lf.module);
                }
            }
        }
    }

    // Seal any remaining unsealed blocks (N20: raw-block order, not
    // HashMap order — deterministic value/inst numbering).
    let mut remaining: Vec<BlockId> = (0..fx.raw_cfg.blocks.len())
        .map(|bi| fx.block_map[&bi])
        .filter(|bb| !fx.ssa.is_sealed(*bb))
        .collect();
    remaining.sort_unstable();
    for bb in remaining {
        fx.ssa.seal_block(bb, &mut fx.lf.module);
    }

    // Publish the translated body into the reserved function-table
    // slot (pass 1 pre-filled a shell).
    fx.lf.module.functions[func_id.index()] = fd;

    // N18 dead-island sweep (augmented reachability).
    sweep_dead_blocks(&mut fx);

    // Debug data (line/column tables keyed by the lifted InstIds,
    // locals with scope extents, param names, source file/code).
    metadata::finish_debug(&mut fx);

    Ok(())
}

/// Build structured try regions from the original bytecode try_blocks.
/// Catch exception values start as a placeholder and are filled by the
/// N13 handler seeding in [`lift_method`].
fn build_try_regions(
    body: &MethodBody,
    raw_cfg: &RawCfg,
    block_map: &HashMap<usize, BlockId>,
) -> Vec<TryRegion> {
    let mut regions = Vec::new();

    for try_block in &body.try_blocks {
        let try_start = try_block.start as usize;
        let try_end = (try_block.start + try_block.len) as usize;

        // All IR blocks overlapping the try region are protected.
        let mut protected = Vec::new();
        for (bi, raw_block) in raw_cfg.blocks.iter().enumerate() {
            if raw_block.start < try_end && raw_block.end > try_start {
                if let Some(&ir_block) = block_map.get(&bi) {
                    protected.push(ir_block);
                }
            }
        }

        let catches = try_block
            .catches
            .iter()
            .filter_map(|c| {
                let handler_bi = raw_cfg.leader_to_block.get(&(c.handler as usize))?;
                let &handler = block_map.get(handler_bi)?;
                Some(Catch {
                    handler,
                    // Filled by the N13 handler seeding (the placeholder
                    // is never observed: every handler block is seeded
                    // before translation, and the sweep prunes dead
                    // catches afterwards).
                    exception: ValueId::new(u32::MAX),
                    // u32::MAX is the file's catch-all sentinel.
                    type_idx: (c.type_idx != u32::MAX).then_some(c.type_idx),
                })
            })
            .collect();

        regions.push(TryRegion { protected, catches });
    }

    regions
}

/// N18 dead-island sweep: remove blocks unreachable over the AUGMENTED
/// successor relation (terminator edges + try→handler exception edges)
/// and repair preds/phi entries/try regions of the survivors.
fn sweep_dead_blocks(fx: &mut translate::FnLift) {
    use std::collections::{HashSet, VecDeque};

    let func_id = fx.func_id;
    let module = &mut fx.lf.module;
    let entry = module.functions[func_id.index()].blocks[0];
    let func_blocks: HashSet<BlockId> = module.functions[func_id.index()]
        .blocks
        .iter()
        .copied()
        .collect();

    let augmented_succs = |module: &Module, func_id: FuncId, bb: BlockId| -> Vec<BlockId> {
        let mut out = Vec::new();
        if let Some(block) = module.blocks.get(bb.index()) {
            if let Some(&last) = block.insts.last() {
                if let Some(inst) = module.insts.get(last.index()) {
                    match &inst.op {
                        abcd_ir::Op::Branch { dest } => out.push(*dest),
                        abcd_ir::Op::CondBranch {
                            true_dest,
                            false_dest,
                            ..
                        } => {
                            out.push(*true_dest);
                            out.push(*false_dest);
                        }
                        _ => {}
                    }
                }
            }
        }
        for region in &module.functions[func_id.index()].try_regions {
            if region.protected.contains(&bb) {
                out.extend(region.catches.iter().map(|c| c.handler));
            }
        }
        out
    };

    let mut reachable: HashSet<BlockId> = HashSet::new();
    let mut queue: VecDeque<BlockId> = VecDeque::new();
    reachable.insert(entry);
    queue.push_back(entry);
    while let Some(bb) = queue.pop_front() {
        for succ in augmented_succs(module, func_id, bb) {
            if func_blocks.contains(&succ) && reachable.insert(succ) {
                queue.push_back(succ);
            }
        }
    }
    let dead: HashSet<BlockId> = func_blocks
        .into_iter()
        .filter(|bb| !reachable.contains(bb))
        .collect();
    if dead.is_empty() {
        return;
    }

    // Kept blocks: drop dead predecessors and the phi entries keyed by
    // them (verify requires phi entry count == predecessor count).
    let kept: Vec<BlockId> = module.functions[func_id.index()]
        .blocks
        .iter()
        .filter(|bb| !dead.contains(bb))
        .copied()
        .collect();
    for bb in kept {
        module.blocks[bb.index()]
            .preds
            .retain(|e| !dead.contains(&e.from));
        let phi_ids: Vec<InstId> = module.blocks[bb.index()]
            .insts
            .iter()
            .copied()
            .filter(|&iid| module.insts.get(iid.index()).is_some_and(|i| i.op.is_phi()))
            .collect();
        for phi_id in phi_ids {
            if let abcd_ir::Op::Phi { entries } = &mut module.insts[phi_id.index()].op {
                entries.retain(|(e, _)| !dead.contains(&e.from));
            }
        }
    }

    // Remove the dead blocks and prune dependent metadata: try-region
    // coverage/handler references.
    let func = &mut module.functions[func_id.index()];
    func.blocks.retain(|bb| !dead.contains(bb));
    for region in &mut func.try_regions {
        region.protected.retain(|bb| !dead.contains(bb));
        region.catches.retain(|c| !dead.contains(&c.handler));
    }
    // A region with no surviving protected blocks or no surviving
    // handler can never dispatch; drop it.
    func.try_regions
        .retain(|r| !r.protected.is_empty() && !r.catches.is_empty());
}

/// Emit an IR instruction in `block` (helper used across modules).
pub(crate) fn emit_inst(
    module: &mut Module,
    block: BlockId,
    op: abcd_ir::Op,
    loc: Option<abcd_ir::Loc>,
) -> (InstId, Option<ValueId>) {
    let has_result = op.has_result();
    let is_phi = op.is_phi();
    let inst_id = InstId::new(module.insts.len() as u32);
    let result = if has_result {
        let val = ValueId::new(module.values.len() as u32);
        module.values.push(Value {
            def: ValueDef::Inst(inst_id),
            ty: Ty::Any,
        });
        Some(val)
    } else {
        None
    };
    module.insts.push(Inst {
        op,
        result,
        block,
        loc,
    });
    let bb = &mut module.blocks[block.index()];
    if is_phi {
        // Phis form the block's leading prefix: insert after the
        // existing phi run (a Braun phi can materialize for a block
        // whose translation already started elsewhere).
        let phi_len = bb
            .insts
            .iter()
            .take_while(|&&iid| module.insts.get(iid.index()).is_some_and(|i| i.op.is_phi()))
            .count();
        bb.insts.insert(phi_len, inst_id);
    } else {
        bb.insts.push(inst_id);
    }
    (inst_id, result)
}
