//! Class-event-stream parallel method-body lifting (`#84` Part 2b).
//!
//! Pass 1 (dense `ClassId` / `FuncId` / `FieldId` reservation) and Pass 2a
//! (`ClassData` headers + standalone ES module records) execute sequentially on
//! [`Lifter`]. Pass 2b then decodes lazy [`abcd_file::MethodSpan`]s, builds
//! CFGs, translates bytecodes, runs Braun SSA + dead-island sweeping + trivial
//! phi cascade, and maps debug tables **in parallel** across Rayon workers into
//! isolated [`MethodFragment`]s.
//!
//! Every side effect a method performs on [`Lifter`]'s module-global tables
//! (`sym_of_file_sid`, `sym`, foreign `class_of_descriptor`, `ConstPool::intern`,
//! and `resolve_literal_array`) that cannot already be satisfied in `O(1)` from
//! the immutable Pass-2a snapshot is recorded in exact encounter order in
//! [`MethodFragment::events`]. Sequential Pass 2c replays each fragment's
//! events against `&mut Lifter` in `(class_schedule, mi)` order and remaps
//! local IDs in place via [`abcd_ir::IdRemapper`], producing a [`abcd_ir::Module`]
//! that is 100% bit-for-bit structurally identical to sequential lifting.

use std::collections::{BTreeSet, HashMap};
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};

use rayon::prelude::*;

use abcd_file::{Class, File, Method};
use abcd_ir::{
    Block, BlockId, ClassData, ClassId, Const, ConstId, Dialect, ExportDecl, FieldId, FuncId,
    FunctionData, IdRemapper, ImportDecl, Inst, InstId, ModuleRequest, Sym, SymbolTable, Value,
    ValueId,
};

use crate::metadata::{self, LegacyModuleSlotIndex};
use crate::resolve::{self, LitWrap};
use crate::{IrArenas, LiftBackend, LiftError, Lifter, lift_method_with};

/// Isolated per-function IR arenas populated on a Rayon worker (`0`-based local IDs).
#[derive(Default)]
pub(crate) struct LocalArenas {
    pub(crate) blocks: Vec<Block>,
    pub(crate) insts: Vec<Inst>,
    pub(crate) values: Vec<Value>,
}

impl IrArenas for LocalArenas {
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

/// Exact encounter-ordered table mutation recorded while lifting one method in parallel.
pub(crate) enum MethodEvent {
    /// Intern a file `StringId` (`Lifter::sym_of_file_sid`) -> next local [`Sym`].
    SymFile(abcd_file::StringId),
    /// Intern a static string (`Lifter::sym`) -> next local [`Sym`].
    SymStr(&'static str),
    /// Append/lookup a foreign class descriptor (`Lifter::class_of_descriptor`) -> next local [`ClassId`].
    ForeignClass(abcd_file::StringId),
    /// Intern a direct [`Const`] (after remapping child local `Sym`/`ConstId`s) -> next local [`ConstId`].
    ConstIntern(Const),
    /// Resolve `(idx, wrap)` through `Lifter::lit_cache` / `file.literal_arrays` -> next local [`ConstId`].
    LitArray { idx: u32, wrap: LitWrap },
    /// Resolve `(idx, wrap)` inside an annotation literal-array element, degrading `Err` to `Const::Null`.
    TryLitArrayOrNull { idx: u32, wrap: LitWrap },
}

/// Completed per-method IR fragment produced by a Rayon worker.
pub(crate) struct MethodFragment {
    pub(crate) fd: FunctionData,
    pub(crate) arenas: LocalArenas,
    pub(crate) events: Vec<MethodEvent>,
    pub(crate) legacy_modvar_patches: Vec<(InstId, Sym)>,
    pub(crate) debug_source_code_sid: Option<abcd_file::StringId>,
}

/// Read-only Pass-2a module snapshot shared across all Rayon workers.
pub(crate) struct SharedLiftState<'a, 'f> {
    pub(crate) file: &'f File,
    pub(crate) dialect: Dialect,
    pub(crate) base_sym: &'a SymbolTable,
    pub(crate) base_consts: &'a abcd_ir::ConstPool,
    pub(crate) base_classes: &'a [ClassData],
    pub(crate) base_class_to_id: &'a HashMap<abcd_file::StringId, ClassId>,
    pub(crate) method_names: &'a [Sym],
    pub(crate) field_ids: &'a [(ClassId, FieldId)],
    pub(crate) base_sid_to_sym: &'a [u32],
    pub(crate) base_lit_cache: &'a HashMap<(u32, LitWrap), ConstId>,
    pub(crate) base_imports: &'a [ImportDecl],
    pub(crate) base_exports: &'a [ExportDecl],
    pub(crate) base_module_requests: &'a [ModuleRequest],
    pub(crate) class_module_slots: &'a [OnceLock<Box<LegacyModuleSlotIndex>>],
    pub(crate) standalone_module_slots: &'a OnceLock<Box<LegacyModuleSlotIndex>>,
    pub(crate) scope_name_fields: &'a HashMap<Sym, ConstId>,
    /// Lock-free `0 = unchecked`, `1 = validated acyclic` cache per `file.literal_arrays` slot.
    pub(crate) lit_valid_cache: Vec<AtomicU8>,
    /// Lowest method index that returned `Err(LiftError)` (`usize::MAX` while error-free).
    pub(crate) min_err_idx: AtomicUsize,
}

/// Worker-local [`LiftBackend`] recording global table requests into [`MethodEvent`]s.
pub(crate) struct MethodLiftCtx<'a, 'f> {
    shared: &'a SharedLiftState<'a, 'f>,
    arenas: LocalArenas,
    events: Vec<MethodEvent>,
    local_syms: Vec<LocalSymKind>,
    local_sid_to_sym: HashMap<abcd_file::StringId, Sym>,
    local_str_to_sym: HashMap<&'static str, Sym>,
    local_classes: Vec<abcd_file::StringId>,
    local_class_to_id: HashMap<abcd_file::StringId, ClassId>,
    /// Maps `local_const_rel -> index in self.events`.
    local_const_events: Vec<u32>,
    local_scalar_consts: HashMap<Const, ConstId>,
    local_lit_cache: HashMap<(u32, LitWrap), ConstId>,
    cached_undefined: Option<ConstId>,
    cached_hole: Option<ConstId>,
    cached_null: Option<ConstId>,
    cached_false: Option<ConstId>,
    cached_true: Option<ConstId>,
    cached_empty_obj: Option<ConstId>,
    legacy_modvar_patches: Vec<(InstId, Sym)>,
    debug_source_code_sid: Option<abcd_file::StringId>,
}

#[derive(Clone, Copy)]
enum LocalSymKind {
    FileSid(abcd_file::StringId),
    StaticStr(&'static str),
}

impl<'a, 'f> MethodLiftCtx<'a, 'f> {
    fn new(shared: &'a SharedLiftState<'a, 'f>, insn_hint: usize) -> Self {
        Self {
            shared,
            arenas: LocalArenas {
                blocks: Vec::with_capacity(if insn_hint > 0 { 4 } else { 0 }),
                insts: Vec::with_capacity(insn_hint),
                values: Vec::with_capacity(insn_hint),
            },
            events: Vec::new(),
            local_syms: Vec::new(),
            local_sid_to_sym: HashMap::new(),
            local_str_to_sym: HashMap::new(),
            local_classes: Vec::new(),
            local_class_to_id: HashMap::new(),
            local_const_events: Vec::new(),
            local_scalar_consts: HashMap::new(),
            local_lit_cache: HashMap::new(),
            cached_undefined: None,
            cached_hole: None,
            cached_null: None,
            cached_false: None,
            cached_true: None,
            cached_empty_obj: None,
            legacy_modvar_patches: Vec::new(),
            debug_source_code_sid: None,
        }
    }

    #[inline]
    fn base_sym_len(&self) -> usize {
        self.shared.base_sym.len()
    }

    #[inline]
    fn base_class_len(&self) -> usize {
        self.shared.base_classes.len()
    }

    #[inline]
    fn base_const_len(&self) -> usize {
        self.shared.base_consts.len()
    }

    fn alloc_local_sym(&mut self, kind: LocalSymKind, ev: MethodEvent) -> Sym {
        let id = Sym::new((self.base_sym_len() + self.local_syms.len()) as u32);
        self.local_syms.push(kind);
        self.events.push(ev);
        id
    }

    fn alloc_local_class(&mut self, sid: abcd_file::StringId) -> ClassId {
        let id = ClassId::new((self.base_class_len() + self.local_classes.len()) as u32);
        self.local_classes.push(sid);
        self.events.push(MethodEvent::ForeignClass(sid));
        id
    }

    fn alloc_local_const(&mut self, ev: MethodEvent) -> ConstId {
        let id = ConstId::new((self.base_const_len() + self.local_const_events.len()) as u32);
        let ev_idx = self.events.len() as u32;
        self.events.push(ev);
        self.local_const_events.push(ev_idx);
        id
    }

    fn const_uses_only_base_ids(&self, c: &Const) -> bool {
        let base_sym = self.base_sym_len();
        let base_const = self.base_const_len();
        let mut all_base = true;
        c.for_each_sym(|s| {
            if s.index() >= base_sym {
                all_base = false;
            }
        });
        if all_base {
            c.for_each_const_id(|cid| {
                if cid.index() >= base_const {
                    all_base = false;
                }
            });
        }
        all_base
    }

    fn intern_const(&mut self, c: Const) -> ConstId {
        match &c {
            Const::Undefined => {
                if let Some(id) = self.cached_undefined {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&Const::Undefined)
                    .unwrap_or_else(|| {
                        self.alloc_local_const(MethodEvent::ConstIntern(Const::Undefined))
                    });
                self.cached_undefined = Some(id);
                return id;
            }
            Const::Hole => {
                if let Some(id) = self.cached_hole {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&Const::Hole)
                    .unwrap_or_else(|| {
                        self.alloc_local_const(MethodEvent::ConstIntern(Const::Hole))
                    });
                self.cached_hole = Some(id);
                return id;
            }
            Const::Null => {
                if let Some(id) = self.cached_null {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&Const::Null)
                    .unwrap_or_else(|| {
                        self.alloc_local_const(MethodEvent::ConstIntern(Const::Null))
                    });
                self.cached_null = Some(id);
                return id;
            }
            Const::Bool(false) => {
                if let Some(id) = self.cached_false {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&Const::Bool(false))
                    .unwrap_or_else(|| {
                        self.alloc_local_const(MethodEvent::ConstIntern(Const::Bool(false)))
                    });
                self.cached_false = Some(id);
                return id;
            }
            Const::Bool(true) => {
                if let Some(id) = self.cached_true {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&Const::Bool(true))
                    .unwrap_or_else(|| {
                        self.alloc_local_const(MethodEvent::ConstIntern(Const::Bool(true)))
                    });
                self.cached_true = Some(id);
                return id;
            }
            Const::ObjectLiteral { keys, values } if keys.is_empty() && values.is_empty() => {
                if let Some(id) = self.cached_empty_obj {
                    return id;
                }
                let id = self
                    .shared
                    .base_consts
                    .lookup(&c)
                    .unwrap_or_else(|| self.alloc_local_const(MethodEvent::ConstIntern(c)));
                self.cached_empty_obj = Some(id);
                return id;
            }
            _ => {}
        }

        if self.const_uses_only_base_ids(&c)
            && let Some(global_cid) = self.shared.base_consts.lookup(&c)
        {
            return global_cid;
        }

        let is_cheap_clone = !matches!(
            c,
            Const::ArrayLiteral(_) | Const::TypedArrayLiteral { .. } | Const::ObjectLiteral { .. }
        );
        if is_cheap_clone {
            if let Some(&existing) = self.local_scalar_consts.get(&c) {
                return existing;
            }
            let key = c.clone();
            let id = self.alloc_local_const(MethodEvent::ConstIntern(c));
            self.local_scalar_consts.insert(key, id);
            id
        } else {
            self.alloc_local_const(MethodEvent::ConstIntern(c))
        }
    }

    fn resolve_sym_str(&self, sym: Sym) -> Option<&str> {
        if let Some(rel) = sym.index().checked_sub(self.base_sym_len()) {
            match *self.local_syms.get(rel)? {
                LocalSymKind::FileSid(sid) => self.shared.file.strings.resolve(sid),
                LocalSymKind::StaticStr(s) => Some(s),
            }
        } else {
            self.shared.base_sym.resolve(sym)
        }
    }

    fn resolve_class_descriptor_str(&self, cid: ClassId) -> Option<&str> {
        if let Some(rel) = cid.index().checked_sub(self.base_class_len()) {
            let sid = *self.local_classes.get(rel)?;
            self.shared.file.strings.resolve(sid)
        } else {
            let desc_sym = self.shared.base_classes.get(cid.index())?.descriptor;
            self.shared.base_sym.resolve(desc_sym)
        }
    }

    fn get_const(&self, cid: ConstId) -> Option<&Const> {
        if let Some(rel) = cid.index().checked_sub(self.base_const_len()) {
            let ev_idx = *self.local_const_events.get(rel)? as usize;
            match self.events.get(ev_idx)? {
                MethodEvent::ConstIntern(c) => Some(c),
                _ => None,
            }
        } else {
            self.shared.base_consts.get(cid)
        }
    }

    fn call_type_frame_slots(&self, fd: &FunctionData) -> Option<abcd_ir::FrameSlots> {
        for ann in &fd.annotations {
            if self.resolve_class_descriptor_str(ann.class) != Some("L_ESCallTypeAnnotation;") {
                continue;
            }
            for (name, value) in &ann.elements {
                if self.resolve_sym_str(*name) != Some("callType") {
                    continue;
                }
                let abcd_ir::AnnValue::Const(cid) = value else {
                    continue;
                };
                let Some(konst) = self.get_const(*cid) else {
                    continue;
                };
                let bits = match konst {
                    Const::Int8(v) => u32::from(*v),
                    Const::Int32(v) => *v,
                    Const::Int64(v) => *v as u32,
                    Const::UInt64(v) => *v as u32,
                    Const::Float32(raw) => {
                        let f = f32::from_bits(*raw);
                        if !f.is_finite() {
                            continue;
                        }
                        (f as i64) as u32
                    }
                    Const::Number(raw) => {
                        let f = f64::from_bits(*raw);
                        if !f.is_finite() {
                            continue;
                        }
                        (f as i64) as u32
                    }
                    _ => continue,
                };
                return Some(abcd_ir::FrameSlots {
                    func: bits & 0b1000 != 0,
                    new_target: bits & 0b0010 != 0,
                    this: bits & 0b0001 != 0,
                });
            }
        }
        None
    }
}

impl<'f> LiftBackend<'f> for MethodLiftCtx<'_, 'f> {
    type Arenas = LocalArenas;

    #[inline]
    fn file(&self) -> &'f File {
        self.shared.file
    }

    #[inline]
    fn arenas(&self) -> &Self::Arenas {
        &self.arenas
    }

    #[inline]
    fn arenas_mut(&mut self) -> &mut Self::Arenas {
        &mut self.arenas
    }

    #[inline]
    fn backend_method_count(&self) -> usize {
        self.shared.method_names.len()
    }

    #[inline]
    fn backend_method_name(&self, idx: abcd_file::MethodIdx) -> Option<Sym> {
        self.shared.method_names.get(idx.index()).copied()
    }

    #[inline]
    fn backend_field_id(&self, idx: abcd_file::FieldIdx) -> Option<(ClassId, FieldId)> {
        self.shared.field_ids.get(idx.index()).copied()
    }

    #[inline]
    fn backend_field_name(&self, cid: ClassId, fid: FieldId) -> Option<Sym> {
        self.shared
            .base_classes
            .get(cid.index())
            .and_then(|c| c.fields.get(fid.index()))
            .map(|f| f.name)
    }

    fn backend_sym_of_file_sid(&mut self, sid: abcd_file::StringId) -> Option<Sym> {
        let idx = sid.index();
        if let Some(&cached) = self.shared.base_sid_to_sym.get(idx)
            && cached != u32::MAX
        {
            return Some(Sym::new(cached));
        }
        if let Some(&local) = self.local_sid_to_sym.get(&sid) {
            return Some(local);
        }
        if let Some(raw) = self.shared.file.strings.raw_mutf8(sid) {
            self.shared.file.strings.resolve(sid)?;
            if let Some(existing) = self.shared.base_sym.get_raw_mutf8(raw) {
                return Some(existing);
            }
        } else {
            let s = self.shared.file.strings.as_str(sid)?;
            if let Some(existing) = self.shared.base_sym.get(s) {
                return Some(existing);
            }
        }
        let sym = self.alloc_local_sym(LocalSymKind::FileSid(sid), MethodEvent::SymFile(sid));
        self.local_sid_to_sym.insert(sid, sym);
        Some(sym)
    }

    fn backend_sym(&mut self, s: &'static str) -> Sym {
        if let Some(existing) = self.shared.base_sym.get(s) {
            return existing;
        }
        if let Some(&local) = self.local_str_to_sym.get(s) {
            return local;
        }
        let sym = self.alloc_local_sym(LocalSymKind::StaticStr(s), MethodEvent::SymStr(s));
        self.local_str_to_sym.insert(s, sym);
        sym
    }

    fn backend_class_of_descriptor(&mut self, sid: abcd_file::StringId) -> Option<ClassId> {
        if let Some(&cid) = self.shared.base_class_to_id.get(&sid) {
            return Some(cid);
        }
        if let Some(&local_cid) = self.local_class_to_id.get(&sid) {
            return Some(local_cid);
        }
        self.shared.file.strings.resolve(sid)?;
        let cid = self.alloc_local_class(sid);
        self.local_class_to_id.insert(sid, cid);
        Some(cid)
    }

    #[inline]
    fn backend_const_scalar(&mut self, c: Const) -> ConstId {
        self.intern_const(c)
    }

    #[inline]
    fn backend_const_shape(&mut self, c: Const) -> ConstId {
        self.intern_const(c)
    }

    fn backend_resolve_lit_array(
        &mut self,
        table_idx: u32,
        wrap: LitWrap,
    ) -> Result<ConstId, LiftError> {
        if let Some(&cid) = self.shared.base_lit_cache.get(&(table_idx, wrap)) {
            return Ok(cid);
        }
        if let Some(&local_cid) = self.local_lit_cache.get(&(table_idx, wrap)) {
            return Ok(local_cid);
        }
        if !(matches!(wrap, LitWrap::BufferRef)
            && self
                .shared
                .base_lit_cache
                .contains_key(&(table_idx, LitWrap::PlainArray)))
        {
            validate_literal_array(
                self.shared.file,
                self.shared.method_names.len(),
                &self.shared.lit_valid_cache,
                table_idx,
            )?;
        }
        let cid = self.alloc_local_const(MethodEvent::LitArray {
            idx: table_idx,
            wrap,
        });
        self.local_lit_cache.insert((table_idx, wrap), cid);
        Ok(cid)
    }

    fn backend_try_lit_array_or_null(&mut self, table_idx: u32, wrap: LitWrap) -> ConstId {
        if let Some(&cid) = self.shared.base_lit_cache.get(&(table_idx, wrap)) {
            return cid;
        }
        self.alloc_local_const(MethodEvent::TryLitArrayOrNull {
            idx: table_idx,
            wrap,
        })
    }

    fn backend_this_param_index(&self, fd: &FunctionData) -> Option<usize> {
        let slots = self
            .call_type_frame_slots(fd)
            .unwrap_or_else(|| match self.shared.dialect {
                Dialect::DynamicEcma => abcd_ir::FrameSlots::DEFAULT,
                Dialect::StaticArkTS => abcd_ir::FrameSlots::for_static_arkts(
                    fd.modifiers.contains(abcd_ir::Modifiers::STATIC),
                ),
            });
        let idx = slots.this_index()?;
        if fd.params.len() < slots.implicit_count() {
            return None;
        }
        Some(idx)
    }

    fn backend_is_const_bool(&self, cid: ConstId) -> bool {
        matches!(self.get_const(cid), Some(Const::Bool(_)))
    }

    #[inline]
    fn backend_legacy_module_slots(&self, class_id: ClassId) -> Option<&LegacyModuleSlotIndex> {
        metadata::resolve_legacy_module_slots(
            class_id,
            self.shared.base_classes,
            self.shared.class_module_slots,
            self.shared.base_imports,
            self.shared.base_exports,
            self.shared.base_module_requests,
            self.shared.standalone_module_slots,
        )
    }

    fn backend_record_legacy_modvar_fallback(&mut self, inst_id: InstId, sym: Sym) {
        if sym.index() >= self.base_sym_len() {
            self.legacy_modvar_patches.push((inst_id, sym));
        }
    }

    fn backend_lookup_scope_names(
        &self,
        class_id: ClassId,
        source_file: Option<Sym>,
    ) -> Option<ConstId> {
        self.shared
            .base_classes
            .get(class_id.index())
            .and_then(|c| c.scope_names)
            .or_else(|| source_file.and_then(|sf| self.shared.scope_name_fields.get(&sf).copied()))
    }

    fn backend_resolve_source_code(&mut self, sid: abcd_file::StringId) -> Option<Arc<str>> {
        self.shared.file.strings.resolve(sid)?;
        self.debug_source_code_sid = Some(sid);
        None
    }
}

struct ValLitFrame<'f> {
    table_idx: u32,
    values: &'f [abcd_file::LiteralValue],
    next_elem: usize,
}

/// Validate a literal-array subgraph iteratively in exact `resolve.rs` DFS
/// pre-order (`O(1)` native stack, lock-free `AtomicU8` memoization for valid
/// subtrees).
fn validate_literal_array(
    file: &File,
    method_count: usize,
    lit_valid_cache: &[AtomicU8],
    root_idx: u32,
) -> Result<(), LiftError> {
    if lit_valid_cache
        .get(root_idx as usize)
        .is_some_and(|flag| flag.load(Ordering::Relaxed) == 1)
    {
        return Ok(());
    }
    let Some(root_arr) = file.literal_arrays.get(root_idx as usize) else {
        return Err(LiftError::LiteralArrayOutOfRange(root_idx));
    };

    let str_len = file.strings.len();
    let mut active = BTreeSet::new();
    active.insert(root_idx);
    let mut stack = vec![ValLitFrame {
        table_idx: root_idx,
        values: &root_arr.values,
        next_elem: 0,
    }];

    while let Some(next_elem) = stack.last().map(|f| f.next_elem) {
        let top = stack.len() - 1;
        let values = stack[top].values;
        if next_elem < values.len() {
            let v = &values[next_elem];
            stack[top].next_elem += 1;
            match v {
                abcd_file::LiteralValue::String(sid)
                | abcd_file::LiteralValue::EtsImplements(sid) => {
                    if sid.index() >= str_len {
                        return Err(LiftError::UnresolvedEntity(sid.index() as u32));
                    }
                }
                abcd_file::LiteralValue::Method(midx)
                | abcd_file::LiteralValue::GeneratorMethod(midx)
                | abcd_file::LiteralValue::AsyncGeneratorMethod(midx)
                | abcd_file::LiteralValue::Getter(midx)
                | abcd_file::LiteralValue::Setter(midx) => {
                    if midx.index() >= method_count {
                        return Err(LiftError::UnresolvedEntity(midx.0));
                    }
                }
                abcd_file::LiteralValue::ArrayString(sids) => {
                    for &sid in sids {
                        if sid.index() >= str_len {
                            return Err(LiftError::UnresolvedEntity(sid.index() as u32));
                        }
                    }
                }
                abcd_file::LiteralValue::LiteralArray(child)
                | abcd_file::LiteralValue::LiteralBufferIndex(child) => {
                    let child_idx = child.0;
                    if lit_valid_cache
                        .get(child_idx as usize)
                        .is_some_and(|flag| flag.load(Ordering::Relaxed) == 1)
                    {
                        continue;
                    }
                    let Some(child_arr) = file.literal_arrays.get(child_idx as usize) else {
                        return Err(LiftError::LiteralArrayOutOfRange(child_idx));
                    };
                    if !active.insert(child_idx) {
                        return Err(LiftError::LiteralArrayCycle(child_idx));
                    }
                    stack.push(ValLitFrame {
                        table_idx: child_idx,
                        values: &child_arr.values,
                        next_elem: 0,
                    });
                }
                abcd_file::LiteralValue::Bool(_)
                | abcd_file::LiteralValue::Integer8(_)
                | abcd_file::LiteralValue::Integer(_)
                | abcd_file::LiteralValue::Float(_)
                | abcd_file::LiteralValue::Double(_)
                | abcd_file::LiteralValue::Accessor(_)
                | abcd_file::LiteralValue::MethodAffiliate(_)
                | abcd_file::LiteralValue::BuiltinTypeIndex(_)
                | abcd_file::LiteralValue::NullValue(_)
                | abcd_file::LiteralValue::ArrayU1(_)
                | abcd_file::LiteralValue::ArrayU8(_)
                | abcd_file::LiteralValue::ArrayI8(_)
                | abcd_file::LiteralValue::ArrayU16(_)
                | abcd_file::LiteralValue::ArrayI16(_)
                | abcd_file::LiteralValue::ArrayU32(_)
                | abcd_file::LiteralValue::ArrayI32(_)
                | abcd_file::LiteralValue::ArrayU64(_)
                | abcd_file::LiteralValue::ArrayI64(_)
                | abcd_file::LiteralValue::ArrayF32(_)
                | abcd_file::LiteralValue::ArrayF64(_) => {}
            }
        } else {
            let Some(finished) = stack.pop() else {
                break;
            };
            active.remove(&finished.table_idx);
            if let Some(slot) = lit_valid_cache.get(finished.table_idx as usize) {
                slot.store(1, Ordering::Relaxed);
            }
        }
    }
    Ok(())
}

/// Zero-allocation slice + arena-offset [`IdRemapper`] translating a
/// [`MethodFragment`]'s local IDs (`>= base_*_len` and `0`-based arenas) into
/// module-global IDs during Pass 2c.
struct MergeRemapper<'a> {
    base_sym_len: usize,
    sym_map: &'a [Sym],
    base_const_len: usize,
    const_map: &'a [ConstId],
    base_class_len: usize,
    class_map: &'a [ClassId],
    block_offset: u32,
    inst_offset: u32,
    value_offset: u32,
}

impl IdRemapper for MergeRemapper<'_> {
    #[inline]
    fn remap_sym(&mut self, id: Sym) -> Sym {
        id.index()
            .checked_sub(self.base_sym_len)
            .and_then(|rel| self.sym_map.get(rel).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_const(&mut self, id: ConstId) -> ConstId {
        id.index()
            .checked_sub(self.base_const_len)
            .and_then(|rel| self.const_map.get(rel).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_class(&mut self, id: ClassId) -> ClassId {
        id.index()
            .checked_sub(self.base_class_len)
            .and_then(|rel| self.class_map.get(rel).copied())
            .unwrap_or(id)
    }

    #[inline]
    fn remap_block(&mut self, id: BlockId) -> BlockId {
        BlockId::new(id.raw().wrapping_add(self.block_offset))
    }

    #[inline]
    fn remap_inst(&mut self, id: InstId) -> InstId {
        InstId::new(id.raw().wrapping_add(self.inst_offset))
    }

    #[inline]
    fn remap_value(&mut self, id: ValueId) -> ValueId {
        ValueId::new(id.raw().wrapping_add(self.value_offset))
    }
}

/// Lift all methods in `class_schedule` in parallel across Rayon workers and
/// deterministically merge their fragments into `lf` in exact `(class, method)`
/// declaration order (`#84` Part 2b).
pub(crate) fn lift_methods_parallel<'f>(
    lf: &mut Lifter<'f>,
    class_schedule: &[(ClassId, &'f Class, u32)],
    total_methods: usize,
    retain_tail_capacity: bool,
) -> Result<(), LiftError> {
    if total_methods == 0 {
        return Ok(());
    }

    let mut jobs: Vec<(usize, ClassId, &'f Method, FuncId)> = Vec::with_capacity(total_methods);
    for &(class_id, class, base) in class_schedule {
        for (mi, method) in class.methods.iter().enumerate() {
            let func_idx = base as usize + mi;
            jobs.push((func_idx, class_id, method, FuncId::new(func_idx as u32)));
        }
    }

    let base_sym_len = lf.module.sym.len();
    let base_const_len = lf.module.consts.len();
    let base_class_len = lf.module.classes.len();

    let results: Vec<Option<Result<MethodFragment, LiftError>>> = {
        let lit_valid_cache: Vec<AtomicU8> = (0..lf.file.literal_arrays.len())
            .map(|_| AtomicU8::new(0))
            .collect();
        let shared = SharedLiftState {
            file: lf.file,
            dialect: lf.module.dialect,
            base_sym: &lf.module.sym,
            base_consts: &lf.module.consts,
            base_classes: &lf.module.classes,
            base_class_to_id: &lf.class_to_id,
            method_names: &lf.method_names,
            field_ids: &lf.field_ids,
            base_sid_to_sym: &lf.sid_to_sym,
            base_lit_cache: &lf.lit_cache,
            base_imports: &lf.module.imports,
            base_exports: &lf.module.exports,
            base_module_requests: &lf.module.module_requests,
            class_module_slots: &lf.class_module_slots,
            standalone_module_slots: &lf.standalone_module_slots,
            scope_name_fields: &lf.scope_name_fields,
            lit_valid_cache,
            min_err_idx: AtomicUsize::new(usize::MAX),
        };

        jobs.into_par_iter()
            .map(|(job_idx, class_id, method, func_id)| {
                if job_idx > shared.min_err_idx.load(Ordering::Relaxed) {
                    return None;
                }
                let insn_hint = method.body.as_ref().map_or(0, |b| b.insn_count());
                let mut ctx = MethodLiftCtx::new(&shared, insn_hint);
                match lift_method_with(&mut ctx, class_id, method, func_id) {
                    Ok(fd) => Some(Ok(MethodFragment {
                        fd,
                        arenas: ctx.arenas,
                        events: ctx.events,
                        legacy_modvar_patches: ctx.legacy_modvar_patches,
                        debug_source_code_sid: ctx.debug_source_code_sid,
                    })),
                    Err(err) => {
                        shared.min_err_idx.fetch_min(job_idx, Ordering::Relaxed);
                        Some(Err(err))
                    }
                }
            })
            .collect()
    };

    // Pass 2c — check for the lowest-index error first, reserve output arenas
    // once (keeping peak RSS low during Pass 2b), then replay `events` in
    // deterministic method order (`0..total_methods`) and remap each fragment.
    let mut sum_blocks = 0usize;
    let mut sum_insts = 0usize;
    let mut sum_values = 0usize;
    let mut has_err = false;
    for item in &results {
        match item {
            Some(Ok(frag)) => {
                sum_blocks += frag.arenas.blocks.len();
                sum_insts += frag.arenas.insts.len();
                sum_values += frag.arenas.values.len();
            }
            Some(Err(_)) => {
                has_err = true;
                break;
            }
            None => break,
        }
    }
    if has_err {
        for item in results.into_iter().flatten() {
            let _ = item?;
        }
        unreachable!("has_err implies at least one Err in results");
    }
    if retain_tail_capacity {
        lf.module
            .blocks
            .reserve(sum_blocks.saturating_add((sum_blocks >> 4).max(64)));
        lf.module
            .insts
            .reserve(sum_insts.saturating_add((sum_insts >> 4).max(64)));
        lf.module
            .values
            .reserve(sum_values.saturating_add((sum_values >> 4).max(64)));
    } else {
        lf.module.blocks.reserve_exact(sum_blocks);
        lf.module.insts.reserve_exact(sum_insts);
        lf.module.values.reserve_exact(sum_values);
    }

    let mut sym_map: Vec<Sym> = Vec::new();
    let mut const_map: Vec<ConstId> = Vec::new();
    let mut class_map: Vec<ClassId> = Vec::new();

    for (func_idx, item) in results.into_iter().enumerate() {
        let Some(res) = item else {
            unreachable!("no job before min_err_idx can be skipped");
        };
        let mut frag = res?;

        sym_map.clear();
        const_map.clear();
        class_map.clear();

        for ev in frag.events {
            match ev {
                MethodEvent::SymFile(sid) => {
                    let sym = lf
                        .sym_of_file_sid(sid)
                        .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?;
                    sym_map.push(sym);
                }
                MethodEvent::SymStr(s) => {
                    sym_map.push(lf.sym(s));
                }
                MethodEvent::ForeignClass(sid) => {
                    let cid = lf
                        .class_of_descriptor(sid)
                        .ok_or(LiftError::UnresolvedEntity(sid.index() as u32))?;
                    class_map.push(cid);
                }
                MethodEvent::ConstIntern(mut c) => {
                    let mut const_remapper = MergeRemapper {
                        base_sym_len,
                        sym_map: &sym_map,
                        base_const_len,
                        const_map: &const_map,
                        base_class_len,
                        class_map: &class_map,
                        block_offset: 0,
                        inst_offset: 0,
                        value_offset: 0,
                    };
                    c.remap_ids(&mut const_remapper);
                    const_map.push(lf.module.consts.intern(c));
                }
                MethodEvent::LitArray { idx, wrap } => {
                    let cid = resolve::const_for_literal_array_with_wrap(lf, idx, wrap)?;
                    const_map.push(cid);
                }
                MethodEvent::TryLitArrayOrNull { idx, wrap } => {
                    let cid = resolve::const_for_literal_array_with_wrap(lf, idx, wrap)
                        .unwrap_or_else(|_| lf.const_scalar(Const::Null));
                    const_map.push(cid);
                }
            }
        }

        let block_offset = lf.module.blocks.len() as u32;
        let inst_offset = lf.module.insts.len() as u32;
        let value_offset = lf.module.values.len() as u32;

        let mut remapper = MergeRemapper {
            base_sym_len,
            sym_map: &sym_map,
            base_const_len,
            const_map: &const_map,
            base_class_len,
            class_map: &class_map,
            block_offset,
            inst_offset,
            value_offset,
        };

        for (local_iid, local_sym) in frag.legacy_modvar_patches {
            let global_raw = remapper.remap_sym(local_sym).raw();
            if let Some(inst) = frag.arenas.insts.get_mut(local_iid.index()) {
                match &mut inst.op {
                    abcd_ir::Op::LoadModuleVar { index, .. }
                    | abcd_ir::Op::StoreModuleVar { index, .. }
                    | abcd_ir::Op::GetModuleNamespace { index } => *index = global_raw,
                    _ => {}
                }
            }
        }

        frag.fd.remap_ids(&mut remapper);
        for blk in &mut frag.arenas.blocks {
            blk.remap_ids(&mut remapper);
        }
        for inst in &mut frag.arenas.insts {
            inst.remap_ids(&mut remapper);
        }
        for val in &mut frag.arenas.values {
            val.remap_ids(&mut remapper);
        }

        if let Some(sid) = frag.debug_source_code_sid
            && let Some(dbg) = &mut frag.fd.debug
        {
            dbg.source_code = lf.backend_resolve_source_code(sid);
        }

        lf.module.blocks.append(&mut frag.arenas.blocks);
        lf.module.insts.append(&mut frag.arenas.insts);
        lf.module.values.append(&mut frag.arenas.values);
        lf.module.functions[func_idx] = frag.fd;
    }

    Ok(())
}
