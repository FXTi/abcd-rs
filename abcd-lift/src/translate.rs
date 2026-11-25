//! Bytecode → v0.2 IR translation (the full v0.1 `translate.rs` arm
//! list, ported). v0.1's proven operand-role semantics are preserved
//! EXACTLY: every `read_reg`/`read_acc`/`write_reg`/`write_acc` happens
//! in v0.1's order per arm — reads drive Braun phi materialization, so
//! the SSA structure matches v0.1's one-for-one (the comparison
//! harness in `compare.rs` machine-checks this).
//!
//! # The opcode → op mapping table
//!
//! 1:1 mappings (canonical-equal in the harness): lda/sta/mov (SSA
//! aliases), all literals → `LoadConst` (Undefined/Null/Bool/Number/
//! String/BigInt/Hole/NaN/Infinity), arithmetic `*2` → `BinaryOp`,
//! comparisons (eq/noteq/less*/greater*/strict*/isin/instanceof) →
//! `Compare`, unary → `UnaryOp` (`not` is BITWISE, N39), istrue/isfalse
//! → `UnaryOp::{IsTrue,IsFalse}`, createemptyobject → `AllocObject`
//! (empty shape), createemptyarray → `AllocArray{shape: None}`,
//! createobjectwithbuffer → `AllocObject{shape}`,
//! createarraywithbuffer → `AllocArray{shape: Some(shape)}` (the
//! literal array as a pooled shape; the object/array tag is
//! OPCODE-carried — never recoverable from the flat literal-buffer
//! content, N59), createregexpwithliteral → `AllocRegExp`
//! (flags as u32 — v0.1's decimal-string flags canonicalize to it),
//! createobjectwithexcludedkeys → `CreateObjectWithExcludedKeys`,
//! ld/stobjbyname → `LoadProp`/`StoreProp`, ld/stobjbyvalue →
//! `LoadPropDyn`/`StorePropDyn`, ld/stobjbyindex → `LoadPropIdx`/
//! `StorePropIdx` (the constant index MATERIALIZED as a `LoadConst` —
//! §9 resolution 3), the OWN-STORE family is IR-explicit (N60; v0.1
//! `InstData::StoreOwnProperty` — define-own-property semantics, no
//! setters, no prototype-chain walk): stownbyname(+withnameset)/
//! definefieldbyname/definepropertybyname → `StoreOwnPropName`,
//! stownbyvalue(+withnameset)/callruntime.definefieldbyvalue →
//! `StoreOwnPropDyn`, stownbyindex(+wide)/callruntime.
//! definefieldbyindex → `StoreOwnPropIdx`, ld/stthisby* →
//! hard [`LiftError::UnsupportedThisByAccess`] (N51: es2panda never
//! emits the IC-fused this-by-* family — never silently invented),
//! ld/stsuperbyname →
//! `LoadSuper`/`StoreSuper` (Name), ld/stsuperbyvalue → (Dynamic),
//! delobjprop → `DeleteProp`, private-property family →
//! `LoadPrivate`/`StorePrivate`/`DefinePrivate`/`TestPrivate`/
//! `CreatePrivateNames{count, names}`, ldglobalvar →
//! `TryGetGlobal{name, default: None}` (the THROWING form: `None` =
//! no fallback), tryldglobalbyname → `TryGetGlobal{name, default:
//! Some(undefined)}` (the tolerant form), stglobalvar → `StoreGlobal`
//! (the global-OBJECT property store, throwing form),
//! stto/stconsttoglobalrecord (+ the deprecated
//! stlet-/stclass-/stconstto-globalrecord trio) → `StoreGlobalRecord`
//! (the global LEXICAL record declaration — N72-C4: never folds to
//! `StoreGlobal`; vendor `RuntimeStGlobalRecord(name, value, isConst)`),
//! trystglobalbyname → `TryStoreGlobal` (the tolerant form — no
//! ReferenceError when the global is absent, N61; v0.1
//! `InstData::TryStoreGlobalByName`), ld/stlexvar → `GetLexVar`/
//! `PutLexVar`, newlexenv → `NewLexEnv{num_vars}`, newlexenvwithname →
//! `NewLexEnvWithName{num_vars, scope_names}`, poplexenv → `PopLexEnv`,
//! module-var family → `LoadModuleVar`/`StoreModuleVar` (local vs
//! external folds — documented) /`GetModuleNamespace`, dynamicimport →
//! `DynamicImport`, definefunc → `DefineFunc{body, captures: [],
//! length}` + `AllocClosure` (the closure allocation is explicit in
//! v0.2 — captures are analysis-layer, deferred empty), definemethod →
//! `DefineFunc` + `AllocClosure` + `DefineMethod{object, name, func,
//! length}`, defineclasswithbuffer → `DefineClass{ctor, heritage,
//! members, count}` (N15's count modeled),
//! callruntime.definesendableclass → `DefineSendableClass{ctor,
//! heritage, members, count}` (N53 — the sendable distinction is
//! modeled, NOT folded into `DefineClass`: the vendor runtime uses
//! SlowRuntimeStub::CreateSharedClass, a different stub from the
//! contemporary form's CreateClassWithBuffer), definegettersetterbyvalue → `DefineGetterSetterByValue`,
//! iterators → `GetIterator`/`GetAsyncIterator`/`GetPropIterator`/
//! `IteratorReturn` (closeiterator) /`NextPropName`, generator family →
//! `CreateGenerator` (async folds — documented) /`SuspendGenerator`/
//! `ResumeGenerator`/`GetResumeMode`, async family →
//! `AsyncFunctionEnter`/`AwaitUncaught` (incl. the deprecated form)/
//! `AsyncResolve`/`AsyncReject`/`CreateIterResultObj`
//! (asyncgeneratorresolve folds, v0.1 parity), gettemplateobject →
//! `GetTemplateObject` (acc inout), setobjectwithproto →
//! `SetObjectWithProto` (NEVER a property copy), starrayspread →
//! `ArraySpread` (result = the new index), copydataproperties →
//! `CopyDataProps` (acc := dst after, v0.1 parity), copyrestargs →
//! `CopyRestArgs{start_index}`, getunmappedargs → `GetUnmappedArgs`,
//! ldnewtarget → `LoadNewTarget`, ldglobal → `LoadGlobalObject`,
//! ldfunction (+deprecated.ldlexenv/ldhomeobject) → `LoadFunction`,
//! ldthis → the `this` VALUE (the this-role frame slot — N67, the
//! vendored frame-slot model, [`abcd_ir::frame`]: `params[2]` under
//! the `0xF` default, annotation-aware; `LoadConst(Undefined)` for
//! shapes the model can't cover — documented),
//! throw → `Throw`, throw.constassignment → `ThrowConstAssignment`
//! (runtime name value), throw.undefinedifhole →
//! `ThrowUndefinedIfHole` (two-reg), throw.undefinedifholewithname →
//! `ThrowUndefinedIfHoleWithName` (compile-time name), throw.ifnotobject
//! → `ThrowIfNotObject`, throw.ifsupernotcorrectcall →
//! `ThrowIfSuperNotCalled{kind}` (0 → NotCalled, 1 → Rebind, anything
//! else → hard [`LiftError::InvalidSuperCheckKind`]), throw.notexists/
//! patternnoncoercible/deletesuperproperty → the dedicated ops,
//! debugger → `Debugger`, jumps → `Branch`/`CondBranch` (jeqz/jnez
//! via `UnaryOp::{IsTrue,IsFalse}`; the fused compare-and-branch
//! family — jeq/jne/jstricteq/jnstricteq and the
//! null/undefined/strict-zero acc-branch forms — is a hard
//! [`LiftError::UnsupportedFusedCompareBranch`]: isa.yaml documents
//! no comparison semantics, the vendor interpreters FATAL/NOP-skip
//! the family, and no producer emits it — ruling 2026-10-04, N51
//! pattern), return
//! family → `Return`, setgeneratorstate/nop/callruntime.
//! notifyconcurrentresult/callruntime.topropertykey → no-ops (v0.1
//! parity).
//!
//! Calls: the whole call family folds into one `Call{callee, this,
//! args, kind}` — callarg*/callrange → `Dynamic{this: None}`,
//! callthis* (+withname, callruntime.callinit) → `Dynamic{this:
//! Some(args[0]), args: args[1..]}`, supercallthis/arrowrange →
//! `Super{this: None}` (arrow distinction folds), supercallspread →
//! `SuperSpread{args: [array]}` (the spread role is IR-explicit —
//! v0.1's `CallKind::SuperCallSpread`, N58), apply (+deprecated.
//! callspread) → `Apply{this: Some(this), args: [array]}` (the spread
//! role is IR-explicit — v0.1's `CallKind::Apply`, N57), newobjrange → `New{callee: window[0], args:
//! window[1..]}` (argc counts the ctor; argc=0 keeps v0.1's acc
//! fallback), newobjapply → `New{callee: ctor, args: [array]}` (v0.1's
//! swapped NewObjApply roles NORMALIZED to callee=ctor — documented),
//! callruntime.supercallforwardallargs →
//! `SuperForwardAllArgs{args: [this]}` (the forward-all kind stays
//! distinct from `Super`, N58; v0.1's SuperCall approximation — args
//! [this], lowering to supercallthisrange argc=1 — kept verbatim).
//!
//! Deprecated opcodes fold to the modern ops (v0.1 convention), with
//! v0.1's exact operand reads preserved (including its DISCARDED reads
//! — they drive phi materialization): deprecated.ld/stmodulevar and
//! deprecated.getmodulenamespace keep v0.1's raw-symbol-index payload
//! hack (documented), deprecated.createarray/objectwithbuffer and
//! deprecated.createobjecthavingmethod resolve the RAW table index
//! (v0.1 parity — and v0.1 lifts BOTH deprecated buffer forms to
//! CreateArrayWithBuffer, so both fold to `AllocArray{shape:
//! Some(shape)}` here, N59), and
//! `deprecated.defineclasswithbuffer` lifts to `DefineClass{ctor,
//! heritage: Some(base), members, member_attrs, count}` with the
//! vendor-grounded operand roles `v1 = lexenv`, `v2 = proto`
//! (`interpreter_assembly.cpp:4624-4648`, `design/decisions.md`
//! ADR-08, `#38` overturning `N54`).
//!
//! Super-property access by constant INDEX: the ISA has no such opcode
//! — [`LiftError::UnsupportedSuperByIndex`], a hard error, never
//! invented semantics (see [`super_key`]).

use std::collections::HashMap;

use abcd_file::{Method, MethodBody};
use abcd_ir::{
    BinOp, BlockId, CallKind, CmpOp, Const, ConstId, DynPrim, FuncId, InstId, LexEnvKind, Loc, Op,
    OwnStoreKind, StaticTy, SuperCheck, SuperKey, Sym, Ty, UnOp, ValueDef, ValueId,
};
use abcd_isa::{Bytecode, EntityId, EntityKind, Reg};

use crate::cfg::RawCfg;
use crate::resolve;
use crate::ssa::{RegOrAcc, SsaBuilder};
use crate::{LiftError, Lifter, emit_inst};

/// A super-property key in the three conceivable forms; the ISA
/// provides name/dynamic producers only.
pub enum SuperKeyForm {
    /// A statically known property name (`ld/stsuperbyname`).
    Name(Sym),
    /// A computed key (`ld/stsuperbyvalue`).
    Dynamic(ValueId),
    /// A constant index — NO ArkCompiler opcode exists.
    Index(u32),
}

/// Convert a super-property key form to the IR key. The constant-index
/// form is a hard error: `isa.yaml` has no super-by-index opcode, so
/// the form is unconstructible from real bytecode and no semantics may
/// be invented for it (v0.1 lower's `UnsupportedInstruction` ruling).
pub fn super_key(form: SuperKeyForm) -> Result<SuperKey, LiftError> {
    match form {
        SuperKeyForm::Name(n) => Ok(SuperKey::Name(n)),
        SuperKeyForm::Dynamic(k) => Ok(SuperKey::Dynamic(k)),
        SuperKeyForm::Index(_) => Err(LiftError::UnsupportedSuperByIndex),
    }
}

/// Per-function translation context.
pub struct FnLift<'l, 'f> {
    /// The module-level conversion state.
    pub lf: &'l mut Lifter<'f>,
    /// The method being lifted.
    pub method: &'f Method,
    /// Its body.
    pub body: &'f MethodBody,
    /// The reserved function-table slot.
    pub func_id: FuncId,
    /// Total valid register count (`num_vregs + num_args`, `R3-M3`).
    pub frame_limit: u16,
    /// Dense raw block index → IR block (`R3-A4`).
    pub block_map: Vec<BlockId>,
    /// The raw CFG.
    pub raw_cfg: RawCfg,
    /// The Braun construction state.
    pub ssa: SsaBuilder,
    /// Decoded line table, sorted by instruction index — SPARSE
    /// (line-change entries; the running line applies to every pc
    /// at-or-after the entry).
    pub line_table: Vec<(u32, u32)>,
    /// Decoded column table, sorted by instruction index (same sparse
    /// running-value semantics).
    pub col_table: Vec<(u32, u32)>,
    /// Emitted inst → its source bytecode index (derived insts share
    /// their parent bytecode's position; phis have none).
    pub inst_pc: HashMap<InstId, u32>,
    /// The this-role frame slot's value (N67 — the vendored frame-slot
    /// model, [`abcd_ir::frame`]): `params[2]` under the `0xF` default,
    /// annotation-aware via the callee's `L_ESCallTypeAnnotation;`;
    /// `None` when the model covers no this slot (set after entry
    /// seeding). NOT `params[0]` — that is the FUNC slot under `0xF`.
    pub this_param: Option<ValueId>,
}

impl<'l, 'f> FnLift<'l, 'f> {
    /// Build the translation context.
    #[expect(
        clippy::too_many_arguments,
        reason = "lifts all per-function frame/CFG/SSA state into FnLift in one call"
    )]
    pub fn new(
        lf: &'l mut Lifter<'f>,
        method: &'f Method,
        body: &'f MethodBody,
        func_id: FuncId,
        frame_limit: u16,
        block_base: usize,
        num_fn_blocks: usize,
        block_map: Vec<BlockId>,
        raw_cfg: RawCfg,
    ) -> Self {
        let undefined_const = lf.const_scalar(Const::Undefined);
        let hole_const = lf.const_scalar(Const::Hole);
        let mut line_table = Vec::new();
        let mut col_table = Vec::new();
        if let Some(debug) = &method.debug {
            for e in &debug.line_table {
                line_table.push((e.index, e.line));
            }
            for e in &debug.column_table {
                col_table.push((e.index, e.column));
            }
        }
        line_table.sort_unstable();
        col_table.sort_unstable();
        Self {
            lf,
            method,
            body,
            func_id,
            frame_limit,
            block_map,
            raw_cfg,
            ssa: SsaBuilder::with_blocks(undefined_const, hole_const, block_base, num_fn_blocks),
            line_table,
            col_table,
            inst_pc: HashMap::new(),
            this_param: None,
        }
    }

    /// Push a fresh SSA value into the arena.
    pub fn new_value(&mut self, def: ValueDef, ty: Ty) -> ValueId {
        let val = ValueId::new(self.lf.module.values.len() as u32);
        self.lf.module.values.push(abcd_ir::Value { def, ty });
        val
    }

    /// The running value of a sparse (index → value) debug table at
    /// `pc`: the last entry at-or-before `pc`.
    fn table_lookup(table: &[(u32, u32)], pc: u32) -> Option<u32> {
        match table.partition_point(|&(idx, _)| idx <= pc) {
            0 => None,
            n => Some(table[n - 1].1),
        }
    }

    /// The source line of a bytecode index (running line of the LNP
    /// stream).
    pub fn line_of(&self, pc: u32) -> Option<u32> {
        Self::table_lookup(&self.line_table, pc)
    }

    /// The source column of a bytecode index.
    pub fn column_of(&self, pc: u32) -> Option<u32> {
        Self::table_lookup(&self.col_table, pc)
    }

    /// Source location of a bytecode index (from the LNP tables).
    fn loc_of(&self, pc: u32) -> Option<Loc> {
        self.line_of(pc).map(|line| Loc {
            line,
            column: self.column_of(pc),
        })
    }

    /// Emit an instruction (recording its source position).
    pub fn emit(&mut self, block: BlockId, op: Op, pc: Option<u32>) -> (InstId, Option<ValueId>) {
        let loc = pc.and_then(|pc| self.loc_of(pc));
        let (iid, res) = emit_inst(&mut self.lf.module, block, op, loc);
        if let Some(pc) = pc {
            self.inst_pc.insert(iid, pc);
        }
        (iid, res)
    }

    /// Emit and return the result value.
    pub fn emit_val(&mut self, block: BlockId, op: Op, pc: Option<u32>) -> ValueId {
        self.emit(block, op, pc)
            .1
            .expect("instruction has no result")
    }

    /// Emit, assign an explicit [`Ty`] to the result value, and return it.
    pub fn emit_val_typed(&mut self, block: BlockId, op: Op, ty: Ty, pc: Option<u32>) -> ValueId {
        let val = self.emit_val(block, op, pc);
        self.lf.module.values[val.index()].ty = ty;
        val
    }

    /// Emit a void instruction (no result).
    pub fn emit_void(&mut self, block: BlockId, op: Op, pc: Option<u32>) {
        self.emit(block, op, pc);
    }

    /// Read the accumulator SSA value.
    pub fn read_acc(&mut self, block: BlockId) -> ValueId {
        self.ssa
            .read_variable(RegOrAcc::Acc, block, &mut self.lf.module)
    }

    /// Write the accumulator SSA value.
    pub fn write_acc(&mut self, block: BlockId, val: ValueId) {
        self.ssa.write_variable(RegOrAcc::Acc, block, val);
    }

    /// Validate that `reg` lies within `[0, frame_limit)` (`R3-M3`).
    #[inline]
    fn check_reg(&self, reg: u16) -> Result<(), LiftError> {
        if reg >= self.frame_limit {
            return Err(LiftError::InvalidRegister {
                reg,
                frame_limit: self.frame_limit,
            });
        }
        Ok(())
    }

    /// Read a register SSA value (`R3-M3` frame-checked).
    pub fn read_reg(&mut self, reg: Reg, block: BlockId) -> Result<ValueId, LiftError> {
        self.check_reg(reg.0)?;
        Ok(self
            .ssa
            .read_variable(RegOrAcc::Reg(reg.0), block, &mut self.lf.module))
    }

    /// Write a register SSA value (`R3-M3` frame-checked).
    pub fn write_reg(&mut self, reg: Reg, block: BlockId, val: ValueId) -> Result<(), LiftError> {
        self.check_reg(reg.0)?;
        self.ssa.write_variable(RegOrAcc::Reg(reg.0), block, val);
        Ok(())
    }

    /// Read a range of consecutive registers (`R3-M3` overflow- and frame-checked).
    pub fn read_reg_range(
        &mut self,
        start: u16,
        count: i64,
        block: BlockId,
    ) -> Result<Vec<ValueId>, LiftError> {
        let Ok(count_u16) = u16::try_from(count) else {
            return Err(LiftError::RegisterRangeOverflow { start, count });
        };
        if count_u16 == 0 {
            return Ok(Vec::new());
        }
        let Some(end) = start.checked_add(count_u16) else {
            return Err(LiftError::RegisterRangeOverflow { start, count });
        };
        if end > self.frame_limit {
            return Err(LiftError::InvalidRegister {
                reg: end - 1,
                frame_limit: self.frame_limit,
            });
        }
        Ok((0..count_u16)
            .map(|i| {
                self.ssa
                    .read_variable(RegOrAcc::Reg(start + i), block, &mut self.lf.module)
            })
            .collect())
    }

    /// The `this` value (N67): the this-role frame slot per the vendored
    /// frame-slot model ([`abcd_ir::frame`] — `design/ir.md` §2,
    /// `design/decisions.md` ADR-05),
    /// resolved at entry seeding into [`FnLift::this_param`]. `ldthis`
    /// reads the frame's `thisObj`
    /// (`EcmaInterpreter::GetThis`, interpreter-inl.cpp:7907-7912), which
    /// the caller bound from the this-role slot — `params[2]` under the
    /// `0xF` default, NOT `params[0]` (the FUNC slot). When the model
    /// covers no this slot (callType without the this bit, or params
    /// fewer than the implicit slots — the conservative documented
    /// fallback), a materialized `undefined` constant.
    pub fn this_value(&mut self, block: BlockId, pc: Option<u32>) -> ValueId {
        if let Some(v) = self.this_param {
            return v;
        }
        let c = self.lf.const_scalar(Const::Undefined);
        self.emit_val(block, Op::LoadConst(c), pc)
    }

    /// Resolve a string-pool entity to a symbol.
    pub fn resolve_str(&mut self, eid: EntityId) -> Result<Sym, LiftError> {
        resolve::resolve_sym(self.lf, self.body, eid, EntityKind::StringId)
    }

    /// Resolve a method-reference entity to (display name, FuncId).
    pub fn resolve_method(&mut self, eid: EntityId) -> Result<(Sym, FuncId), LiftError> {
        resolve::resolve_method(self.lf, self.body, eid)
    }

    /// Resolve a literal-array entity to its pooled shape constant.
    pub fn resolve_literal(&mut self, eid: EntityId) -> Result<ConstId, LiftError> {
        resolve::resolve_literal_const(self.lf, self.body, eid)
    }

    /// Parse the per-member attribute payloads (B2) of a class member
    /// buffer (empty = conservative fallback, attributes unknown).
    pub fn resolve_class_member_attrs(
        &mut self,
        eid: EntityId,
        is_sendable: bool,
    ) -> Result<Vec<abcd_ir::op::MemberAttrs>, LiftError> {
        resolve::class_member_attrs(self.lf, self.body, eid, is_sendable)
    }

    /// Emit a `LoadConst` for a scalar constant (deduplicated pool).
    pub fn load_const(&mut self, block: BlockId, c: Const, pc: Option<u32>) -> ValueId {
        let ty = if matches!(c, Const::Bool(_)) {
            Ty::DynPrim(DynPrim::Bool)
        } else {
            Ty::Any
        };
        let id = self.lf.const_scalar(c);
        self.emit_val_typed(block, Op::LoadConst(id), ty, pc)
    }

    /// Whether `val` is statically proven to hold an ECMAScript boolean (`R3-X1`).
    pub fn is_proven_bool(&self, val: ValueId) -> bool {
        let v = &self.lf.module.values[val.index()];
        if matches!(v.ty, Ty::DynPrim(DynPrim::Bool) | Ty::Static(StaticTy::U1)) {
            return true;
        }
        match v.def {
            ValueDef::Const(cid) => matches!(self.lf.module.consts.get(cid), Some(Const::Bool(_))),
            ValueDef::Inst(iid) => match &self.lf.module.insts[iid.index()].op {
                Op::LoadConst(cid) => {
                    matches!(self.lf.module.consts.get(*cid), Some(Const::Bool(_)))
                }
                Op::Compare { .. } | Op::TestPrivate { .. } | Op::TestProp { .. } => true,
                Op::UnaryOp { op, .. } => op.is_boolean_result(),
                _ => false,
            },
            _ => false,
        }
    }

    /// The IR block for a jump target label (`R3-M3` bounds-checked).
    pub fn label_block(&self, pc: usize, label: abcd_isa::Label) -> Result<BlockId, LiftError> {
        let target = label.0 as usize;
        let &raw_bi =
            self.raw_cfg
                .leader_to_block
                .get(&target)
                .ok_or(LiftError::JumpTargetOutOfBounds {
                    pc,
                    target,
                    len: self.body.bytecodes.len(),
                })?;
        Ok(self.block_map[raw_bi])
    }

    /// O(1) fall-through block after raw block `bi` (`R3-A4`, `R3-M3`).
    pub fn fallthrough_block(&self, bi: usize, pc: usize) -> Result<BlockId, LiftError> {
        self.block_map
            .get(bi + 1)
            .copied()
            .ok_or(LiftError::FallthroughOutOfBounds {
                pc,
                len: self.body.bytecodes.len(),
            })
    }
}

/// Translate a single bytecode instruction into v0.2 IR.
pub fn translate_bytecode(
    fx: &mut FnLift,
    bc: &Bytecode,
    idx: usize,
    bi: usize,
    block: BlockId,
) -> Result<(), LiftError> {
    let loc = Some(idx as u32);

    match bc {
        // ── Data movement (SSA aliases only) ─────────────────────────
        Bytecode::Lda(r) => {
            let v = fx.read_reg(*r, block)?;
            fx.write_acc(block, v);
        }
        Bytecode::Sta(r) => {
            let v = fx.read_acc(block);
            fx.write_reg(*r, block, v)?;
        }
        Bytecode::Mov(dst, src) => {
            let v = fx.read_reg(*src, block)?;
            fx.write_reg(*dst, block, v)?;
        }

        // ── Literals ─────────────────────────────────────────────────
        Bytecode::Ldundefined => {
            let v = fx.load_const(block, Const::Undefined, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnull => {
            let v = fx.load_const(block, Const::Null, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldtrue => {
            let v = fx.load_const(block, Const::Bool(true), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldfalse => {
            let v = fx.load_const(block, Const::Bool(false), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldai(imm) => {
            let v = fx.load_const(block, Const::number(imm.0 as f64), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Fldai(imm) => {
            let v = fx.load_const(block, Const::Number(imm.0 as u64), loc);
            fx.write_acc(block, v);
        }
        Bytecode::LdaStr(eid) => {
            let s = fx.resolve_str(*eid)?;
            let v = fx.load_const(block, Const::String(s), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldbigint(eid) => {
            // Vendor `ldbigint string_id` (isa.yaml:1622-1626): acc out
            // is a BIGINT built from the constant-pool entry, not a
            // string — a distinct Const, never collapsible into String.
            let s = fx.resolve_str(*eid)?;
            let v = fx.load_const(block, Const::BigInt(s), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnan => {
            let v = fx.load_const(block, Const::number(f64::NAN), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldinfinity => {
            let v = fx.load_const(block, Const::number(f64::INFINITY), loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldhole => {
            let v = fx.load_const(block, Const::Hole, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldsymbol => {
            let v = fx.emit_val(block, Op::LoadSymbol, loc);
            fx.write_acc(block, v);
        }

        // ── Binary operations (acc = acc OP reg, IC slot discarded) ──
        Bytecode::Add2(_ic, r) => binary_op(fx, BinOp::Add, r, block, loc)?,
        Bytecode::Sub2(_ic, r) => binary_op(fx, BinOp::Sub, r, block, loc)?,
        Bytecode::Mul2(_ic, r) => binary_op(fx, BinOp::Mul, r, block, loc)?,
        Bytecode::Div2(_ic, r) => binary_op(fx, BinOp::Div, r, block, loc)?,
        Bytecode::Mod2(_ic, r) => binary_op(fx, BinOp::Mod, r, block, loc)?,
        Bytecode::Exp(_ic, r) => binary_op(fx, BinOp::Exp, r, block, loc)?,
        Bytecode::Shl2(_ic, r) => binary_op(fx, BinOp::Shl, r, block, loc)?,
        Bytecode::Shr2(_ic, r) => binary_op(fx, BinOp::Shr, r, block, loc)?,
        Bytecode::Ashr2(_ic, r) => binary_op(fx, BinOp::Ashr, r, block, loc)?,
        Bytecode::And2(_ic, r) => binary_op(fx, BinOp::BitAnd, r, block, loc)?,
        Bytecode::Or2(_ic, r) => binary_op(fx, BinOp::BitOr, r, block, loc)?,
        Bytecode::Xor2(_ic, r) => binary_op(fx, BinOp::BitXor, r, block, loc)?,
        Bytecode::Eq(_ic, r) => compare_op(fx, CmpOp::Eq, r, block, loc)?,
        Bytecode::Noteq(_ic, r) => compare_op(fx, CmpOp::NotEq, r, block, loc)?,
        Bytecode::Less(_ic, r) => compare_op(fx, CmpOp::Less, r, block, loc)?,
        Bytecode::Lesseq(_ic, r) => compare_op(fx, CmpOp::LessEq, r, block, loc)?,
        Bytecode::Greater(_ic, r) => compare_op(fx, CmpOp::Greater, r, block, loc)?,
        Bytecode::Greatereq(_ic, r) => compare_op(fx, CmpOp::GreaterEq, r, block, loc)?,
        Bytecode::Isin(_ic, r) => compare_op(fx, CmpOp::In, r, block, loc)?,
        Bytecode::Instanceof(_ic, r) => compare_op(fx, CmpOp::InstanceOf, r, block, loc)?,
        Bytecode::Stricteq(_ic, r) => compare_op(fx, CmpOp::StrictEq, r, block, loc)?,
        Bytecode::Strictnoteq(_ic, r) => compare_op(fx, CmpOp::StrictNotEq, r, block, loc)?,

        // ── Unary operations (acc = OP acc, IC slot discarded) ───────
        Bytecode::Neg(_ic) => unary_op(fx, UnOp::Minus, block, loc),
        // N39: vendored `not` is BITWISE ~acc, not logical negation
        // (interpreter_assembly.cpp:767-790).
        Bytecode::Not(_ic) => unary_op(fx, UnOp::BitNot, block, loc),
        Bytecode::Inc(_ic) => unary_op(fx, UnOp::Inc, block, loc),
        Bytecode::Dec(_ic) => unary_op(fx, UnOp::Dec, block, loc),
        Bytecode::Typeof(_ic) => unary_op(fx, UnOp::TypeOf, block, loc),
        Bytecode::Tonumber(_ic) => unary_op(fx, UnOp::ToNumber, block, loc),
        Bytecode::Tonumeric(_ic) => unary_op(fx, UnOp::ToNumeric, block, loc),
        Bytecode::Istrue => unary_op(fx, UnOp::IsTrue, block, loc),
        Bytecode::Isfalse => unary_op(fx, UnOp::IsFalse, block, loc),

        // ── Object / Array creation ──────────────────────────────────
        Bytecode::Createemptyobject => {
            let shape = fx.lf.empty_object_shape();
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createemptyarray(_ic) => {
            let v = fx.emit_val(block, Op::AllocArray { shape: None }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createarraywithbuffer(_ic, eid) => {
            // N59: the ARRAY tag is opcode-carried — never recoverable
            // from the flat literal-buffer content (v0.1
            // `InstData::CreateArrayWithBuffer`).
            let shape = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(block, Op::AllocArray { shape: Some(shape) }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createobjectwithbuffer(_ic, eid) => {
            let shape = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createregexpwithliteral(_ic, eid, flags_imm) => {
            let pattern = fx.resolve_str(*eid)?;
            let v = fx.emit_val(
                block,
                Op::AllocRegExp {
                    pattern,
                    flags: flags_imm.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Createobjectwithexcludedkeys(num, obj_reg, start_reg)
        | Bytecode::WideCreateobjectwithexcludedkeys(num, obj_reg, start_reg) => {
            // `isa.yaml` `range_1` (`R3-C6`): the immediate encodes `key_count - 1`,
            // so `imm + 1` consecutive registers starting at `start_reg` are read.
            let obj = fx.read_reg(*obj_reg, block)?;
            let count = num
                .0
                .checked_add(1)
                .ok_or(LiftError::RegisterRangeOverflow {
                    start: start_reg.0,
                    count: num.0,
                })?;
            let keys = fx.read_reg_range(start_reg.0, count, block)?;
            let v = fx.emit_val(block, Op::CreateObjectWithExcludedKeys { obj, keys }, loc);
            fx.write_acc(block, v);
        }

        // ── Property access ──────────────────────────────────────────
        Bytecode::Ldobjbyname(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::LoadProp { object: obj, name }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreProp {
                    object: obj,
                    name,
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyvalue(_ic, obj_reg) => {
            let key = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let v = fx.emit_val(block, Op::LoadPropDyn { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyvalue(_ic, obj_reg, key_reg) => {
            // Vendor: v1 = receiver, v2 = propKey, acc = VALUE
            // (isa.yaml:1353-1357, interpreter_assembly.cpp:2306-2335).
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            fx.emit_void(
                block,
                Op::StorePropDyn {
                    object: obj,
                    key,
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldobjbyindex(_, index) | Bytecode::WideLdobjbyindex(index) => {
            let obj = fx.read_acc(block);
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            let v = fx.emit_val(
                block,
                Op::LoadPropIdx {
                    object: obj,
                    index: konst,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stobjbyindex(_, obj_reg, index) | Bytecode::WideStobjbyindex(obj_reg, index) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StorePropIdx {
                    object: obj,
                    index: konst,
                    value,
                },
                loc,
            );
        }
        Bytecode::Stownbyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropName {
                    object: obj,
                    name,
                    value,
                    kind: OwnStoreKind::OwnProp,
                },
                loc,
            );
        }
        Bytecode::Stownbynamewithnameset(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropName {
                    object: obj,
                    name,
                    value,
                    kind: OwnStoreKind::OwnPropWithNameSet,
                },
                loc,
            );
        }
        Bytecode::Stownbyvalue(_ic, obj_reg, key_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropDyn {
                    object: obj,
                    key,
                    value,
                    kind: OwnStoreKind::OwnProp,
                },
                loc,
            );
        }
        Bytecode::Stownbyvaluewithnameset(_ic, obj_reg, key_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropDyn {
                    object: obj,
                    key,
                    value,
                    kind: OwnStoreKind::OwnPropWithNameSet,
                },
                loc,
            );
        }
        Bytecode::Stownbyindex(_, obj_reg, index) | Bytecode::WideStownbyindex(obj_reg, index) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StoreOwnPropIdx {
                    object: obj,
                    index: konst,
                    value,
                    kind: OwnStoreKind::OwnProp,
                },
                loc,
            );
        }
        // N51: the `this-by-*` family (isa.yaml:1627-1642) is IC-fused
        // `this` property access that es2panda NEVER emits (`this[k] = v`
        // compiles to `ldthis` + `stobjbyvalue`; upstream source grep zero
        // hits). Zero corpus coverage means no VM evidence for the IC
        // semantics — hard error, never silently invented (maintainer
        // ruling 2026-09-20; mirrors v0.1's
        // `LiftError::UnsupportedThisByAccess`).
        Bytecode::Ldthisbyname(..) => {
            return Err(LiftError::UnsupportedThisByAccess("ldthisbyname"));
        }
        Bytecode::Stthisbyname(..) => {
            return Err(LiftError::UnsupportedThisByAccess("stthisbyname"));
        }
        Bytecode::Ldthisbyvalue(..) => {
            return Err(LiftError::UnsupportedThisByAccess("ldthisbyvalue"));
        }
        Bytecode::Stthisbyvalue(..) => {
            return Err(LiftError::UnsupportedThisByAccess("stthisbyvalue"));
        }
        Bytecode::Ldsuperbyname(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            // Vendor `ldsuperbyname imm, string_id; acc: inout` (`R3-H1`):
            // the receiver (`thisValue`) rides `acc` in, and the property value
            // is written back to `acc` out.
            let this_value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::LoadSuper { key, this_value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stsuperbyname(_ic, eid, this_reg) => {
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            let this_value = fx.read_reg(*this_reg, block)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreSuper {
                    key,
                    this_value,
                    value,
                },
                loc,
            );
        }
        Bytecode::Ldsuperbyvalue(_ic, this_reg) => {
            let this_value = fx.read_reg(*this_reg, block)?;
            let k = fx.read_acc(block);
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let v = fx.emit_val(block, Op::LoadSuper { key, this_value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Stsuperbyvalue(_ic, this_reg, key_reg) => {
            let this_value = fx.read_reg(*this_reg, block)?;
            let k = fx.read_reg(*key_reg, block)?;
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreSuper {
                    key,
                    this_value,
                    value,
                },
                loc,
            );
        }
        Bytecode::Delobjprop(key_reg) => {
            let obj = fx.read_reg(*key_reg, block)?;
            let key = fx.read_acc(block);
            let v = fx.emit_val(block, Op::DeleteProp { object: obj, key }, loc);
            fx.write_acc(block, v);
        }

        // ── Private properties ───────────────────────────────────────
        Bytecode::Ldprivateproperty(_ic, level, slot) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(
                block,
                Op::LoadPrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stprivateproperty(_ic, level, slot, obj_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StorePrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                    value,
                },
                loc,
            );
        }
        Bytecode::Testin(_ic, level, slot) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val_typed(
                block,
                Op::TestPrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                },
                Ty::DynPrim(DynPrim::Bool),
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Define field/property by name ────────────────────────────
        Bytecode::Definefieldbyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropName {
                    object: obj,
                    name,
                    value,
                    kind: OwnStoreKind::ClassField,
                },
                loc,
            );
        }
        Bytecode::Definepropertybyname(_ic, eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropName {
                    object: obj,
                    name,
                    value,
                    kind: OwnStoreKind::DefineProperty,
                },
                loc,
            );
        }

        // ── Global variables ─────────────────────────────────────────
        Bytecode::Ldglobalvar(_ic, eid) => {
            // The THROWING form: `default: None` = no fallback when the
            // global is absent (documented convention).
            let name = fx.resolve_str(*eid)?;
            let v = fx.emit_val(
                block,
                Op::TryGetGlobal {
                    name,
                    default: None,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stglobalvar(_ic, eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::StoreGlobal { name, value }, loc);
        }
        Bytecode::Tryldglobalbyname(_ic, eid) => {
            // The tolerant form: fallback is `undefined` (vendor
            // behavior when the name is missing).
            let name = fx.resolve_str(*eid)?;
            let default = fx.load_const(block, Const::Undefined, loc);
            let v = fx.emit_val(
                block,
                Op::TryGetGlobal {
                    name,
                    default: Some(default),
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Trystglobalbyname(_ic, eid) => {
            // N61: the TOLERANT store (v0.1
            // `InstData::TryStoreGlobalByName`) — no ReferenceError when
            // the global is absent; never folds to StoreGlobal.
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::TryStoreGlobal { name, value }, loc);
        }
        Bytecode::Sttoglobalrecord(_ic, eid) => {
            // N72-C4: the global LEXICAL record store — NOT a
            // global-object property store (that is `StoreGlobal` /
            // stglobalvar). Vendor `RuntimeStGlobalRecord(name, value,
            // isConst=false)` (runtime_stubs-inl.h:780).
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreGlobalRecord {
                    name,
                    value,
                    is_const: false,
                },
                loc,
            );
        }
        Bytecode::Stconsttoglobalrecord(_ic, eid) => {
            // The const form: `RuntimeStGlobalRecord(name, value,
            // isConst=true)`.
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreGlobalRecord {
                    name,
                    value,
                    is_const: true,
                },
                loc,
            );
        }

        // ── Lexical variables ────────────────────────────────────────
        Bytecode::Ldlexvar(level, slot) | Bytecode::WideLdlexvar(level, slot) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    kind: LexEnvKind::Plain,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stlexvar(level, slot) | Bytecode::WideStlexvar(level, slot) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                    kind: LexEnvKind::Plain,
                },
                loc,
            );
        }
        Bytecode::Newlexenv(num) | Bytecode::WideNewlexenv(num) => {
            let v = fx.emit_val(
                block,
                Op::NewLexEnv {
                    num_vars: num.0 as u16,
                    kind: LexEnvKind::Plain,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newlexenvwithname(num, eid) | Bytecode::WideNewlexenvwithname(num, eid) => {
            let scope_names = fx.resolve_literal(*eid)?;
            let v = fx.emit_val(
                block,
                Op::NewLexEnvWithName {
                    num_vars: num.0 as u16,
                    scope_names,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Poplexenv => {
            fx.emit_void(block, Op::PopLexEnv, loc);
        }

        // ── Module variables ─────────────────────────────────────────
        Bytecode::Ldlocalmodulevar(index) | Bytecode::WideLdlocalmodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::Local,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Ldexternalmodulevar(index) | Bytecode::WideLdexternalmodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::External,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Stmodulevar(index) | Bytecode::WideStmodulevar(index) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreModuleVar {
                    index: index.0 as u32,
                    value,
                },
                loc,
            );
        }
        Bytecode::Getmodulenamespace(index) | Bytecode::WideGetmodulenamespace(index) => {
            let v = fx.emit_val(
                block,
                Op::GetModuleNamespace {
                    index: index.0 as u32,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Dynamicimport => {
            let specifier = fx.read_acc(block);
            let v = fx.emit_val(block, Op::DynamicImport { specifier }, loc);
            fx.write_acc(block, v);
        }

        // ── Function / Class definition ──────────────────────────────
        Bytecode::Definefunc(_ic, eid, length) => {
            let (_name, body_id) = fx.resolve_method(*eid)?;
            let f = fx.emit_val(
                block,
                Op::DefineFunc {
                    body: body_id,
                    captures: Vec::new(),
                    length: length.0 as u16,
                },
                loc,
            );
            let v = fx.emit_val(block, Op::AllocClosure { func: f }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Definemethod(_ic, eid, length) => {
            let (name, body_id) = fx.resolve_method(*eid)?;
            let home_object = fx.read_acc(block);
            let f = fx.emit_val(
                block,
                Op::DefineFunc {
                    body: body_id,
                    captures: Vec::new(),
                    length: length.0 as u16,
                },
                loc,
            );
            let c = fx.emit_val(block, Op::AllocClosure { func: f }, loc);
            let v = fx.emit_val(
                block,
                Op::DefineMethod {
                    object: home_object,
                    name,
                    func: c,
                    length: length.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Defineclasswithbuffer(_ic, method_eid, lit_eid, count, base_reg) => {
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let members = fx.resolve_literal(*lit_eid)?;
            let member_attrs = fx.resolve_class_member_attrs(*lit_eid, false)?;
            let base = fx.read_reg(*base_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor,
                    heritage: Some(base),
                    members,
                    member_attrs,
                    count: count.0 as u16,
                })),
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Definegettersetterbyvalue(obj_reg, key_reg, getter_reg, setter_reg) => {
            // Vendor `definegettersetterbyvalue v1, v2, v3, v4, acc: inout` (`R3-H2`):
            // `acc` carries the boolean `set_name` flag in and receives `obj` out.
            let set_name = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            let getter = fx.read_reg(*getter_reg, block)?;
            let setter = fx.read_reg(*setter_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::DefineGetterSetterByValue {
                    obj,
                    key,
                    getter,
                    setter,
                    set_name,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Calls ────────────────────────────────────────────────────
        Bytecode::Callarg0(_ic) => {
            let callee = fx.read_acc(block);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callarg1(_ic, a0) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callargs2(_ic, a0, a1) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callargs3(_ic, a0, a1, a2) => {
            let callee = fx.read_acc(block);
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let arg2 = fx.read_reg(*a2, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callrange(_, argc, start) | Bytecode::WideCallrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis0(_, this_reg) | Bytecode::Callthis0withname(_, _, this_reg) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis1(_, this_reg, a0) | Bytecode::Callthis1withname(_, _, this_reg, a0) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis2(_, this_reg, a0, a1)
        | Bytecode::Callthis2withname(_, _, this_reg, a0, a1) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthis3(_, this_reg, a0, a1, a2)
        | Bytecode::Callthis3withname(_, _, this_reg, a0, a1, a2) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let arg2 = fx.read_reg(*a2, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthisrange(_, argc, start) | Bytecode::WideCallthisrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = call_this_args(fx, start.0, argc.0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: args.0,
                    args: args.1,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Callthisrangewithname(_, argc, _, start)
        | Bytecode::WideCallthisrangewithname(argc, _, start) => {
            let callee = fx.read_acc(block);
            let args = call_this_args(fx, start.0, argc.0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: args.0,
                    args: args.1,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallthisrange(_, argc, start)
        | Bytecode::WideSupercallthisrange(argc, start) => {
            // Vendor `supercallthisrange` (`R3-C5`, `isa.yaml` `acc: out:top`):
            // does NOT read `acc`; resolves the super constructor from the
            // enclosing constructor function (`LoadFunction`).
            let args = fx.read_reg_range(start.0, argc.0, block)?;
            let callee = fx.emit_val(block, Op::LoadFunction, loc);
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Super,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallarrowrange(_, argc, start)
        | Bytecode::WideSupercallarrowrange(argc, start) => {
            // Vendor `supercallarrowrange` (`R3-C5`, `isa.yaml` `acc: inout:top`):
            // explicit super constructor in `acc`, distinct `CallKind::SuperArrow`.
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::SuperArrow,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Supercallspread(_ic, arg_reg) => {
            let callee = fx.read_acc(block);
            let arg = fx.read_reg(*arg_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg],
                    kind: CallKind::SuperSpread,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Apply(_ic, this_reg, args_reg) => {
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let args_arr = fx.read_reg(*args_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![args_arr],
                    kind: CallKind::Apply,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newobjrange(_, argc, start) | Bytecode::WideNewobjrange(argc, start) => {
            let range = fx.read_reg_range(start.0, argc.0, block)?;
            let (callee, args) = match range.split_first() {
                Some((&ctor, rest)) => (ctor, rest.to_vec()),
                None => (fx.read_acc(block), Vec::new()),
            };
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::New,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Newobjapply(_ic, obj_reg) => {
            // Vendor (`R3-C1`, `interpreter_assembly.cpp:1912-1926`): register
            // `obj_reg` is the constructor, `acc` is the spread array → `NewSpread`.
            let array = fx.read_acc(block);
            let ctor = fx.read_reg(*obj_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee: ctor,
                    this: None,
                    args: vec![array],
                    kind: CallKind::NewSpread,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Special value loaders ────────────────────────────────────
        Bytecode::Ldthis => {
            let v = fx.this_value(block, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldnewtarget => {
            let v = fx.emit_val(block, Op::LoadNewTarget, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldglobal => {
            let v = fx.emit_val(block, Op::LoadGlobalObject, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Ldfunction => {
            let v = fx.emit_val(block, Op::LoadFunction, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getunmappedargs => {
            let v = fx.emit_val(block, Op::GetUnmappedArgs, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Copyrestargs(index) | Bytecode::WideCopyrestargs(index) => {
            let v = fx.emit_val(
                block,
                Op::CopyRestArgs {
                    start_index: index.0 as u16,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Iterators ────────────────────────────────────────────────
        Bytecode::Getiterator(_ic) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getasynciterator(_ic) => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetAsyncIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getpropiterator => {
            let obj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetPropIterator { obj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Closeiterator(_ic, iter_reg) => {
            let iterator = fx.read_reg(*iter_reg, block)?;
            let v = fx.emit_val(block, Op::IteratorReturn { iterator }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getnextpropname(iter_reg) => {
            let iterator = fx.read_reg(*iter_reg, block)?;
            let v = fx.emit_val(block, Op::NextPropName { iterator }, loc);
            fx.write_acc(block, v);
        }

        // ── Generator / Async ────────────────────────────────────────
        Bytecode::Creategeneratorobj(func_reg) => {
            let func = fx.read_reg(*func_reg, block)?;
            let v = fx.emit_val(block, Op::CreateGenerator { func }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createasyncgeneratorobj(func_reg) => {
            let func = fx.read_reg(*func_reg, block)?;
            let v = fx.emit_val(block, Op::CreateAsyncGenerator { func }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Suspendgenerator(gen_reg) => {
            let genobj = fx.read_reg(*gen_reg, block)?;
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::SuspendGenerator { genobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Resumegenerator => {
            let genobj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::ResumeGenerator { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Getresumemode => {
            let genobj = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetResumeMode { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Setgeneratorstate(imm) => {
            // Vendor `setgeneratorstate imm:u8, acc: in:top` (`R3-C2`).
            let genobj = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::SetGeneratorState {
                    genobj,
                    state: imm.0 as u8,
                },
                loc,
            );
        }
        Bytecode::Asyncfunctionenter => {
            let v = fx.emit_val(block, Op::AsyncFunctionEnter, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionawaituncaught(func_reg) => {
            let funcobj = fx.read_reg(*func_reg, block)?;
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::AwaitUncaught { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionresolve(func_reg) => {
            let funcobj = fx.read_reg(*func_reg, block)?;
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::AsyncResolve { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncfunctionreject(func_reg) => {
            let funcobj = fx.read_reg(*func_reg, block)?;
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::AsyncReject { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Asyncgeneratorresolve(gen_reg, val_reg, done_reg) => {
            // Vendor `asyncgeneratorresolve v1, v2, v3` (`R3-C2`):
            // `v1 = genobj`, `v2 = value`, `v3 = done` (`canSuspend`).
            let genobj = fx.read_reg(*gen_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let done = fx.read_reg(*done_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::AsyncGeneratorResolve {
                    genobj,
                    value,
                    done,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::Asyncgeneratorreject(gen_reg) => {
            // Vendor `asyncgeneratorreject v:in:top, acc: inout:top` (`R3-C2`):
            // `v = genobj`, `acc = rejection reason`.
            let genobj = fx.read_reg(*gen_reg, block)?;
            let value = fx.read_acc(block);
            let v = fx.emit_val(block, Op::AsyncGeneratorReject { genobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Createiterresultobj(val_reg, done_reg) => {
            let value = fx.read_reg(*val_reg, block)?;
            let done = fx.read_reg(*done_reg, block)?;
            let v = fx.emit_val(block, Op::CreateIterResultObj { value, done }, loc);
            fx.write_acc(block, v);
        }

        // ── Misc ─────────────────────────────────────────────────────
        Bytecode::Gettemplateobject(_ic) => {
            let literal = fx.read_acc(block);
            let v = fx.emit_val(block, Op::GetTemplateObject { literal }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Setobjectwithproto(_ic, proto_reg) => {
            let obj = fx.read_acc(block);
            let proto = fx.read_reg(*proto_reg, block)?;
            fx.emit_void(block, Op::SetObjectWithProto { proto, obj }, loc);
        }
        Bytecode::Starrayspread(arr_reg, index_reg) => {
            let src = fx.read_acc(block);
            let dst = fx.read_reg(*arr_reg, block)?;
            let index = fx.read_reg(*index_reg, block)?;
            let v = fx.emit_val(block, Op::ArraySpread { dst, index, src }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::Copydataproperties(dst_reg) => {
            let src = fx.read_acc(block);
            let dst = fx.read_reg(*dst_reg, block)?;
            fx.emit_void(block, Op::CopyDataProps { dst, src }, loc);
            fx.write_acc(block, dst);
        }

        // ── Control flow — jumps ─────────────────────────────────────
        Bytecode::Jmp(label) => {
            let dest = fx.label_block(idx, *label)?;
            fx.emit_void(block, Op::Branch { dest }, loc);
        }
        Bytecode::Jeqz(label) => cond_branch_acc(fx, false, *label, idx, bi, block, loc)?,
        Bytecode::Jnez(label) => cond_branch_acc(fx, true, *label, idx, bi, block, loc)?,
        // Fused compare-and-branch family (isa.yaml:1700-1796) — HARD
        // ERROR (maintainer ruling 2026-10-04, N51 pattern). isa.yaml
        // documents only `pc += imm` for all 24 variants — NO
        // comparison semantics; the C++ interpreter FATALs every
        // variant (interpreter-inl.cpp:6853-6964), the assembly
        // interpreter NOP-skips them (interpreter_stub.cpp:5412-5516),
        // the baseline JIT/AOT ignore them, es2abc never emits them
        // (pandagen.cpp:1139-1170 lowers unfused: `ldundefined;eq;
        // jnez` / `ldundefined;stricteq;jnez`), abckit marks the
        // null/undefined/zero forms deprecated and the compare forms
        // replaced, and corpus coverage is zero (0/5517 .pa + 156
        // wild packages). The former truthiness fold contradicted the
        // mnemonic intent with no upstream behavior to justify it —
        // refused loudly, never silently invented (mirrors
        // `LiftError::UnsupportedThisByAccess`).
        Bytecode::Jstricteqz(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jstricteqz"));
        }
        Bytecode::Jnstricteqz(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jnstricteqz"));
        }
        Bytecode::Jeqnull(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jeqnull"));
        }
        Bytecode::Jnenull(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jnenull"));
        }
        Bytecode::Jstricteqnull(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jstricteqnull"));
        }
        Bytecode::Jnstricteqnull(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jnstricteqnull"));
        }
        Bytecode::Jequndefined(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jequndefined"));
        }
        Bytecode::Jneundefined(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jneundefined"));
        }
        Bytecode::Jstrictequndefined(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch(
                "jstrictequndefined",
            ));
        }
        Bytecode::Jnstrictequndefined(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch(
                "jnstrictequndefined",
            ));
        }
        Bytecode::Jeq(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jeq"));
        }
        Bytecode::Jne(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jne"));
        }
        Bytecode::Jstricteq(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jstricteq"));
        }
        Bytecode::Jnstricteq(..) => {
            return Err(LiftError::UnsupportedFusedCompareBranch("jnstricteq"));
        }

        // ── Return ───────────────────────────────────────────────────
        Bytecode::Return => {
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::Return { value: Some(value) }, loc);
        }
        Bytecode::Returnundefined => {
            fx.emit_void(block, Op::Return { value: None }, loc);
        }

        // ── Exception handling ───────────────────────────────────────
        Bytecode::Throw => {
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::Throw { value }, loc);
        }
        Bytecode::ThrowNotexists => {
            fx.emit_void(block, Op::ThrowNotExists, loc);
        }
        Bytecode::ThrowPatternnoncoercible => {
            fx.emit_void(block, Op::ThrowPatternNonCoercible, loc);
        }
        Bytecode::ThrowDeletesuperproperty => {
            fx.emit_void(block, Op::ThrowDeleteSuperProperty, loc);
        }
        Bytecode::ThrowConstassignment(name_reg) => {
            let name = fx.read_reg(*name_reg, block)?;
            fx.emit_void(block, Op::ThrowConstAssignment { name }, loc);
        }
        Bytecode::ThrowIfnotobject(val_reg) => {
            let value = fx.read_reg(*val_reg, block)?;
            fx.emit_void(block, Op::ThrowIfNotObject { value }, loc);
        }
        Bytecode::ThrowUndefinedifhole(name_reg, val_reg) => {
            let name = fx.read_reg(*name_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            fx.emit_void(block, Op::ThrowUndefinedIfHole { name, value }, loc);
        }
        Bytecode::ThrowUndefinedifholewithname(eid) => {
            let name = fx.resolve_str(*eid)?;
            let acc = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::ThrowUndefinedIfHoleWithName { name, value: acc },
                loc,
            );
        }
        Bytecode::ThrowIfsupernotcorrectcall(imm) => {
            let value = fx.read_acc(block);
            let kind = match imm.0 as u16 {
                0 => SuperCheck::NotCalled,
                1 => SuperCheck::Rebind,
                other => return Err(LiftError::InvalidSuperCheckKind(other)),
            };
            fx.emit_void(block, Op::ThrowIfSuperNotCalled { value, kind }, loc);
        }

        // ── Debug ────────────────────────────────────────────────────
        Bytecode::Debugger => {
            fx.emit_void(block, Op::Debugger, loc);
        }
        Bytecode::Nop => { /* no-op */ }

        // ── Callruntime variants ─────────────────────────────────────
        Bytecode::CallruntimeNotifyconcurrentresult => {
            // Vendor `callruntime.notifyconcurrentresult` (`R3-C4`, `acc: in:top`).
            let value = fx.read_acc(block);
            fx.emit_void(block, Op::NotifyConcurrentResult { value }, loc);
        }
        Bytecode::CallruntimeTopropertykey => unary_op(fx, UnOp::ToPropertyKey, block, loc),
        Bytecode::CallruntimeDefinefieldbyvalue(_ic, key_reg, obj_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            fx.emit_void(
                block,
                Op::StoreOwnPropDyn {
                    object: obj,
                    key,
                    value,
                    kind: OwnStoreKind::ClassField,
                },
                loc,
            );
        }
        Bytecode::CallruntimeDefinefieldbyindex(_ic, index, obj_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            fx.emit_void(
                block,
                Op::StoreOwnPropIdx {
                    object: obj,
                    index: konst,
                    value,
                    kind: OwnStoreKind::ClassField,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCreateprivateproperty(count, eid) => {
            let names = fx.resolve_literal(*eid)?;
            fx.emit_void(
                block,
                Op::CreatePrivateNames {
                    count: count.0 as u16,
                    names,
                },
                loc,
            );
        }
        Bytecode::CallruntimeDefineprivateproperty(_ic, level, slot, obj_reg) => {
            let value = fx.read_acc(block);
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(
                block,
                Op::DefinePrivate {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    obj,
                    value,
                },
                loc,
            );
        }
        Bytecode::CallruntimeCallinit(_ic, this_reg) => {
            // Vendor `callruntime.callinit` (`R3-C7`): class field-initializer
            // invocation (`CallKind::ClassInit`).
            let callee = fx.read_acc(block);
            let this = fx.read_reg(*this_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args: vec![],
                    kind: CallKind::ClassInit,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeDefinesendableclass(_ic, method_eid, lit_eid, count, base_reg) => {
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let members = fx.resolve_literal(*lit_eid)?;
            let member_attrs = fx.resolve_class_member_attrs(*lit_eid, true)?;
            let base = fx.read_reg(*base_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::DefineSendableClass(Box::new(abcd_ir::DefineClassData {
                    ctor,
                    heritage: Some(base),
                    members,
                    member_attrs,
                    count: count.0 as u16,
                })),
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdsendableclass(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::SendableClass,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdsendableexternalmodulevar(index)
        | Bytecode::CallruntimeWideldsendableexternalmodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::SendableExternal,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdsendablelocalmodulevar(index)
        | Bytecode::CallruntimeWideldsendablelocalmodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::SendableLocal,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdlazymodulevar(index)
        | Bytecode::CallruntimeWideldlazymodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::Lazy,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeLdlazysendablemodulevar(index)
        | Bytecode::CallruntimeWideldlazysendablemodulevar(index) => {
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: index.0 as u32,
                    kind: abcd_ir::ModuleVarKind::LazySendable,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeNewsendableenv(num) | Bytecode::CallruntimeWidenewsendableenv(num) => {
            let v = fx.emit_val(
                block,
                Op::NewLexEnv {
                    num_vars: num.0 as u16,
                    kind: LexEnvKind::Sendable,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeStsendablevar(level, slot)
        | Bytecode::CallruntimeWidestsendablevar(level, slot) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                    kind: LexEnvKind::Sendable,
                },
                loc,
            );
        }
        Bytecode::CallruntimeLdsendablevar(level, slot)
        | Bytecode::CallruntimeWideldsendablevar(level, slot) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    kind: LexEnvKind::Sendable,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::CallruntimeIstrue(_ic) => unary_op(fx, UnOp::IsTrue, block, loc),
        Bytecode::CallruntimeIsfalse(_ic) => unary_op(fx, UnOp::IsFalse, block, loc),
        Bytecode::CallruntimeSupercallforwardallargs(this_reg) => {
            // Vendor `callruntime.supercallforwardallargs v:in:top` (`R3-C5`,
            // `isa.yaml` `acc: out:top`): `this_reg` (`thisFunc`) is the ONLY
            // input; `acc` is NOT read. `verify_func` and `abcd-lower` model
            // `SuperForwardAllArgs` with `this: None` and `args: [this_func]`.
            let this_func = fx.read_reg(*this_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee: this_func,
                    this: None,
                    args: vec![this_func],
                    kind: CallKind::SuperForwardAllArgs,
                },
                loc,
            );
            fx.write_acc(block, v);
        }

        // ── Patch var (for hot-reload) ───────────────────────────────
        Bytecode::WideLdpatchvar(index) => {
            let v = fx.emit_val(
                block,
                Op::GetLexVar {
                    level: 0,
                    slot: index.0 as u16,
                    kind: LexEnvKind::Patch,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::WideStpatchvar(index) => {
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: 0,
                    slot: index.0 as u16,
                    value,
                    kind: LexEnvKind::Patch,
                },
                loc,
            );
        }

        // ── Deprecated variants ──────────────────────────────────────
        // Map deprecated instructions to the same IR as their modern
        // equivalents (v0.1 convention).
        Bytecode::DeprecatedLdlexenv | Bytecode::DeprecatedLdhomeobject => {
            // These load environment/home object into acc — v0.1 models
            // them as LoadFunction (parity).
            let v = fx.emit_val(block, Op::LoadFunction, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedPoplexenv => {
            fx.emit_void(block, Op::PopLexEnv, loc);
        }
        Bytecode::DeprecatedGetiteratornext(iter_reg, step_reg) => {
            // Legacy `deprecated.getiteratornext v1, v2` (`R3-M4`): advances
            // `iterator` (`v1`) using its `next` method (`v2`) → `IteratorNext`.
            let iterator = fx.read_reg(*iter_reg, block)?;
            let _step = fx.read_reg(*step_reg, block)?;
            let v = fx.emit_val(block, Op::IteratorNext { iterator }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCreatearraywithbuffer(idx) => {
            let shape = resolve::const_for_literal_array(fx.lf, idx.0 as u32)?;
            let v = fx.emit_val(block, Op::AllocArray { shape: Some(shape) }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCreateobjectwithbuffer(idx) => {
            // `R3-M4`: `deprecated.createobjectwithbuffer` allocates an OBJECT
            // literal (`AllocObject`), never an array.
            let shape = resolve::const_for_literal_array(fx.lf, idx.0 as u32)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedTonumber(src) => {
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::ToNumber,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedTonumeric(src) => {
            // `R3-M4`: preserves BigInt values (`ToNumeric`, not `ToNumber`).
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::ToNumeric,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedNeg(src) => {
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Minus,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedNot(src) => {
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::BitNot,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedInc(src) => {
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Inc,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDec(src) => {
            let val = fx.read_reg(*src, block)?;
            let v = fx.emit_val(
                block,
                Op::UnaryOp {
                    op: UnOp::Dec,
                    operand: val,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallarg0(callee_reg) => {
            let callee = fx.read_reg(*callee_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallarg1(callee_reg, a0) => {
            let callee = fx.read_reg(*callee_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallargs2(callee_reg, a0, a1) => {
            let callee = fx.read_reg(*callee_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallargs3(callee_reg, a0, a1, a2) => {
            let callee = fx.read_reg(*callee_reg, block)?;
            let arg0 = fx.read_reg(*a0, block)?;
            let arg1 = fx.read_reg(*a1, block)?;
            let arg2 = fx.read_reg(*a2, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args: vec![arg0, arg1, arg2],
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallrange(argc, start) => {
            let callee = fx.read_acc(block);
            let args = fx.read_reg_range(start.0, argc.0, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: None,
                    args,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallspread(func_reg, this_reg, array_reg) => {
            let func = fx.read_reg(*func_reg, block)?;
            let this = fx.read_reg(*this_reg, block)?;
            let array = fx.read_reg(*array_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee: func,
                    this: Some(this),
                    args: vec![array],
                    kind: CallKind::Apply,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCallthisrange(argc, start) => {
            if argc.0 < 0 {
                return Err(LiftError::RegisterRangeOverflow {
                    start: start.0,
                    count: argc.0,
                });
            }
            let total = if argc.0 == 0 {
                2
            } else {
                argc.0
                    .checked_add(1)
                    .ok_or(LiftError::RegisterRangeOverflow {
                        start: start.0,
                        count: argc.0,
                    })?
            };
            let window = fx.read_reg_range(start.0, total, block)?;
            let callee = window[0];
            let this = window[1];
            let args = window[2..].to_vec();
            let v = fx.emit_val(
                block,
                Op::Call {
                    callee,
                    this: Some(this),
                    args,
                    kind: CallKind::Dynamic,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDefineclasswithbuffer(
            method_eid,
            lit_imm,
            count_imm,
            lexenv_reg,
            proto_reg,
        ) => {
            let (_name, ctor) = fx.resolve_method(*method_eid)?;
            let raw_lit = lit_imm.0 as u32;
            let (members, member_attrs) = if fx
                .body
                .entities
                .contains_key(&(EntityKind::LiteralarrayId, raw_lit))
            {
                let lit_eid = EntityId(raw_lit);
                let members = fx.resolve_literal(lit_eid)?;
                let member_attrs = fx.resolve_class_member_attrs(lit_eid, false)?;
                (members, member_attrs)
            } else {
                let members = resolve::const_for_literal_array(fx.lf, raw_lit)?;
                let member_attrs =
                    resolve::class_member_attrs_for_index(fx.lf.file, raw_lit, false)?;
                (members, member_attrs)
            };
            let _lexenv = fx.read_reg(*lexenv_reg, block)?;
            let base = fx.read_reg(*proto_reg, block)?;
            let v = fx.emit_val(
                block,
                Op::DefineClass(Box::new(abcd_ir::DefineClassData {
                    ctor,
                    heritage: Some(base),
                    members,
                    member_attrs,
                    count: count_imm.0 as u16,
                })),
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedResumegenerator(gen_reg) => {
            let genobj = fx.read_reg(*gen_reg, block)?;
            let v = fx.emit_val(block, Op::ResumeGenerator { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedGetresumemode(gen_reg) => {
            let genobj = fx.read_reg(*gen_reg, block)?;
            let v = fx.emit_val(block, Op::GetResumeMode { genobj }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedGettemplateobject(tpl_reg) => {
            let literal = fx.read_reg(*tpl_reg, block)?;
            let v = fx.emit_val(block, Op::GetTemplateObject { literal }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDelobjprop(obj_reg, key_reg) => {
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            let v = fx.emit_val(block, Op::DeleteProp { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedSuspendgenerator(gen_reg, val_reg) => {
            let genobj = fx.read_reg(*gen_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let v = fx.emit_val(block, Op::SuspendGenerator { genobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionawaituncaught(async_reg, val_reg) => {
            let funcobj = fx.read_reg(*async_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let v = fx.emit_val(block, Op::AwaitUncaught { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedCopydataproperties(dst_reg, src_reg) => {
            let dst = fx.read_reg(*dst_reg, block)?;
            let src = fx.read_reg(*src_reg, block)?;
            fx.emit_void(block, Op::CopyDataProps { dst, src }, loc);
            fx.write_acc(block, dst);
        }
        Bytecode::DeprecatedSetobjectwithproto(proto_reg, obj_reg) => {
            let proto = fx.read_reg(*proto_reg, block)?;
            let obj = fx.read_reg(*obj_reg, block)?;
            fx.emit_void(block, Op::SetObjectWithProto { proto, obj }, loc);
        }
        Bytecode::DeprecatedLdobjbyvalue(obj_reg, key_reg) => {
            let obj = fx.read_reg(*obj_reg, block)?;
            let key = fx.read_reg(*key_reg, block)?;
            let v = fx.emit_val(block, Op::LoadPropDyn { object: obj, key }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdsuperbyvalue(obj_reg, key_reg) => {
            let this_value = fx.read_reg(*obj_reg, block)?;
            let k = fx.read_reg(*key_reg, block)?;
            let key = super_key(SuperKeyForm::Dynamic(k))?;
            let v = fx.emit_val(block, Op::LoadSuper { key, this_value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdobjbyindex(obj_reg, index) => {
            let obj = fx.read_reg(*obj_reg, block)?;
            let konst = fx.load_const(block, Const::number(index.0 as f64), loc);
            let v = fx.emit_val(
                block,
                Op::LoadPropIdx {
                    object: obj,
                    index: konst,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionresolve(async_reg, mid_reg, val_reg) => {
            let funcobj = fx.read_reg(*async_reg, block)?;
            let _mid = fx.read_reg(*mid_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let v = fx.emit_val(block, Op::AsyncResolve { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncfunctionreject(async_reg, mid_reg, val_reg) => {
            let funcobj = fx.read_reg(*async_reg, block)?;
            let _mid = fx.read_reg(*mid_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let v = fx.emit_val(block, Op::AsyncReject { funcobj, value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStlexvar(level, slot, val_reg) => {
            let value = fx.read_reg(*val_reg, block)?;
            fx.emit_void(
                block,
                Op::PutLexVar {
                    level: level.0 as u16,
                    slot: slot.0 as u16,
                    value,
                    kind: LexEnvKind::Plain,
                },
                loc,
            );
        }
        Bytecode::DeprecatedGetmodulenamespace(eid) => {
            let name = fx.resolve_str(*eid)?;
            let v = fx.emit_val(block, Op::GetModuleNamespace { index: name.0 }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStmodulevar(eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreModuleVar {
                    index: name.0,
                    value,
                },
                loc,
            );
        }
        Bytecode::DeprecatedLdobjbyname(eid, obj_reg) => {
            let name = fx.resolve_str(*eid)?;
            let obj = fx.read_reg(*obj_reg, block)?;
            let v = fx.emit_val(block, Op::LoadProp { object: obj, name }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdsuperbyname(eid, obj_reg) => {
            // `R3-M4`: legacy `deprecated.ldsuperbyname string_id, v` passes
            // the super receiver (`thisValue`) in `obj_reg`.
            let name = fx.resolve_str(*eid)?;
            let key = super_key(SuperKeyForm::Name(name))?;
            let this_value = fx.read_reg(*obj_reg, block)?;
            let v = fx.emit_val(block, Op::LoadSuper { key, this_value }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedLdmodulevar(eid, flag) => {
            let name = fx.resolve_str(*eid)?;
            let kind = if flag.0 == 0 {
                abcd_ir::ModuleVarKind::Local
            } else {
                abcd_ir::ModuleVarKind::External
            };
            let v = fx.emit_val(
                block,
                Op::LoadModuleVar {
                    index: name.0,
                    kind,
                },
                loc,
            );
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedStconsttoglobalrecord(eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreGlobalRecord {
                    name,
                    value,
                    is_const: true,
                },
                loc,
            );
        }
        Bytecode::DeprecatedStlettoglobalrecord(eid)
        | Bytecode::DeprecatedStclasstoglobalrecord(eid) => {
            let name = fx.resolve_str(*eid)?;
            let value = fx.read_acc(block);
            fx.emit_void(
                block,
                Op::StoreGlobalRecord {
                    name,
                    value,
                    is_const: false,
                },
                loc,
            );
        }
        Bytecode::DeprecatedCreateobjecthavingmethod(idx) => {
            let shape = resolve::const_for_literal_array(fx.lf, idx.0 as u32)?;
            let v = fx.emit_val(block, Op::AllocObject { shape }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedDynamicimport(spec_reg) => {
            let specifier = fx.read_reg(*spec_reg, block)?;
            let v = fx.emit_val(block, Op::DynamicImport { specifier }, loc);
            fx.write_acc(block, v);
        }
        Bytecode::DeprecatedAsyncgeneratorreject(gen_reg, val_reg) => {
            // `R3-M4`: `v1 = genobj`, `v2 = rejection reason` → `AsyncGeneratorReject`.
            let genobj = fx.read_reg(*gen_reg, block)?;
            let value = fx.read_reg(*val_reg, block)?;
            let v = fx.emit_val(block, Op::AsyncGeneratorReject { genobj, value }, loc);
            fx.write_acc(block, v);
        }
    }

    Ok(())
}

// ─── Helper functions ────────────────────────────────────────────────────────

/// Emit a binary operation: acc = acc OP reg.
fn binary_op(
    fx: &mut FnLift,
    op: BinOp,
    r: &Reg,
    block: BlockId,
    loc: Option<u32>,
) -> Result<(), LiftError> {
    let left = fx.read_acc(block);
    let right = fx.read_reg(*r, block)?;
    let v = fx.emit_val(block, Op::BinaryOp { op, left, right }, loc);
    fx.write_acc(block, v);
    Ok(())
}

/// Emit a comparison: acc = acc CMP reg.
fn compare_op(
    fx: &mut FnLift,
    op: CmpOp,
    r: &Reg,
    block: BlockId,
    loc: Option<u32>,
) -> Result<(), LiftError> {
    let left = fx.read_acc(block);
    let right = fx.read_reg(*r, block)?;
    let v = fx.emit_val_typed(
        block,
        Op::Compare { op, left, right },
        Ty::DynPrim(DynPrim::Bool),
        loc,
    );
    fx.write_acc(block, v);
    Ok(())
}

/// Emit a unary operation: acc = OP acc.
fn unary_op(fx: &mut FnLift, op: UnOp, block: BlockId, loc: Option<u32>) {
    let operand = fx.read_acc(block);
    let ty = if op.is_boolean_result() {
        Ty::DynPrim(DynPrim::Bool)
    } else {
        Ty::Any
    };
    let v = fx.emit_val_typed(block, Op::UnaryOp { op, operand }, ty, loc);
    fx.write_acc(block, v);
}

/// Read a MODERN callthisrange-family register window `[this, args...]` (`argc + 1` slots).
fn call_this_args(
    fx: &mut FnLift,
    start: u16,
    argc: i64,
    block: BlockId,
) -> Result<(Option<ValueId>, Vec<ValueId>), LiftError> {
    if argc < 0 {
        return Err(LiftError::RegisterRangeOverflow { start, count: argc });
    }
    let count = argc
        .checked_add(1)
        .ok_or(LiftError::RegisterRangeOverflow { start, count: argc })?;
    let range = fx.read_reg_range(start, count, block)?;
    match range.split_first() {
        Some((&this, rest)) => Ok((Some(this), rest.to_vec())),
        None => Ok((None, Vec::new())),
    }
}

/// Emit a conditional branch on `acc` (`#61` `R3-X1`):
/// - If `acc` is already proven boolean, emit `Op::CondBranch` directly
///   (`jnez L` → `true_dest: L, false_dest: fall`; `jeqz L` → `true_dest: fall, false_dest: L`).
/// - Otherwise, emit `Op::UnaryOp { op: JumpNez | JumpEqz, operand: acc }`
///   (preserving ArkCompiler's non-`ToBoolean` raw `jeqz`/`jnez` semantics on
///   `null`, `undefined`, `NaN`, strings, and objects) followed by `Op::CondBranch`.
fn cond_branch_acc(
    fx: &mut FnLift,
    truthy: bool,
    label: abcd_isa::Label,
    idx: usize,
    bi: usize,
    block: BlockId,
    loc: Option<u32>,
) -> Result<(), LiftError> {
    let target_dest = fx.label_block(idx, label)?;
    let fall_dest = fx.fallthrough_block(bi, idx)?;
    let val = fx.read_acc(block);
    if fx.is_proven_bool(val) {
        let (true_dest, false_dest) = if truthy {
            (target_dest, fall_dest)
        } else {
            (fall_dest, target_dest)
        };
        fx.emit_void(
            block,
            Op::CondBranch {
                cond: val,
                true_dest,
                false_dest,
            },
            loc,
        );
    } else {
        let op = if truthy { UnOp::JumpNez } else { UnOp::JumpEqz };
        let pred = fx.emit_val_typed(
            block,
            Op::UnaryOp { op, operand: val },
            Ty::DynPrim(DynPrim::Bool),
            loc,
        );
        fx.emit_void(
            block,
            Op::CondBranch {
                cond: pred,
                true_dest: target_dest,
                false_dest: fall_dest,
            },
            loc,
        );
    }
    Ok(())
}
