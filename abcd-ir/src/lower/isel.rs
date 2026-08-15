//! Instruction selection: IR instructions → ArkCompiler bytecodes.
//!
//! Takes an IR function with register allocation results and produces
//! a sequence of ArkCompiler bytecodes per basic block.

use std::collections::HashMap;

use abcd_isa::{Bytecode, EntityId, Imm, Label, Reg};

use crate::entity::{Block, FuncId, Inst, StringId, Value};
use crate::inst::{BinOp, CallKind, InstData, PropKind, UnOp};
use crate::module::Module;

use super::regalloc::{RegAlloc, RegSlot};

/// Result of instruction selection for one function.
#[derive(Debug)]
pub struct IselResult {
    /// Bytecodes per block (in RPO order).
    pub block_codes: Vec<(Block, Vec<Bytecode>)>,
    /// String pool reverse map: StringId → EntityId for the output file.
    pub string_map: HashMap<StringId, EntityId>,
    /// Total number of IC slots allocated for this function.
    pub ic_size: u16,
}

/// Per-function IC slot allocator.
struct IcAllocator {
    counter: u16,
}

impl IcAllocator {
    fn new() -> Self {
        Self { counter: 0 }
    }

    /// Allocate `slot_count` consecutive IC slots, returning the first slot's Imm.
    fn alloc(&mut self, slot_count: u16) -> Imm {
        let id = self.counter;
        self.counter += slot_count;
        Imm(id as i64)
    }

    /// Allocate 1 IC slot (arithmetic, globals, object/array creation, function def).
    fn one(&mut self) -> Imm {
        self.alloc(1)
    }

    /// Allocate 2 IC slots (property access, calls, iterators).
    fn two(&mut self) -> Imm {
        self.alloc(2)
    }
}

/// Select instructions for a function.
pub fn select(
    module: &Module,
    _func_id: FuncId,
    alloc: &RegAlloc,
    rpo: &[Block],
    string_map: &HashMap<StringId, EntityId>,
) -> IselResult {
    let mut block_codes: Vec<(Block, Vec<Bytecode>)> = Vec::new();
    let mut ic = IcAllocator::new();

    for &bb in rpo {
        let mut codes = Vec::new();
        let block = module.block(bb);

        // Phi copies from predecessors are handled in layout (inserted before terminators).
        // Skip phi instructions — they don't produce bytecodes directly.

        for &inst in &block.insts {
            let node = module.inst(inst);
            let result_slot = node
                .result
                .map(|v| alloc.allocation.get(&v).copied().unwrap_or(RegSlot::Acc));

            select_inst(
                &node.data,
                result_slot,
                inst,
                module,
                alloc,
                string_map,
                &mut codes,
                &mut ic,
            );
        }

        block_codes.push((bb, codes));
    }

    IselResult {
        block_codes,
        string_map: string_map.clone(),
        ic_size: ic.counter,
    }
}

/// Get the Reg for a value, inserting lda/sta as needed.
fn val_reg(val: Value, alloc: &RegAlloc, codes: &mut Vec<Bytecode>) -> Reg {
    match alloc.allocation.get(&val).copied().unwrap_or(RegSlot::Acc) {
        RegSlot::Reg(r) => Reg(r),
        RegSlot::Acc => {
            // Value is in acc — need to sta to a temp. This shouldn't happen often
            // because the allocator tries to keep multi-use values in registers.
            // For now, use reg 0xFFFE as a spill slot.
            let spill = Reg(0xFFFE);
            codes.push(Bytecode::Sta(spill));
            spill
        }
    }
}

/// Ensure a value is in the accumulator. If it's in a register, emit lda.
fn ensure_acc(val: Value, alloc: &RegAlloc, codes: &mut Vec<Bytecode>) {
    match alloc.allocation.get(&val).copied().unwrap_or(RegSlot::Acc) {
        RegSlot::Reg(r) => {
            codes.push(Bytecode::Lda(Reg(r)));
        }
        RegSlot::Acc => {
            // Already in acc, nothing to do.
        }
    }
}

/// If the result should go to a register (not acc), emit sta.
fn store_result(result_slot: Option<RegSlot>, codes: &mut Vec<Bytecode>) {
    if let Some(RegSlot::Reg(r)) = result_slot {
        codes.push(Bytecode::Sta(Reg(r)));
    }
}

fn eid(sid: StringId, string_map: &HashMap<StringId, EntityId>) -> EntityId {
    string_map.get(&sid).copied().unwrap_or(EntityId(sid.0))
}

/// Select bytecodes for a single IR instruction.
#[allow(clippy::too_many_arguments)]
fn select_inst(
    data: &InstData,
    result_slot: Option<RegSlot>,
    _inst: Inst,
    module: &Module,
    alloc: &RegAlloc,
    string_map: &HashMap<StringId, EntityId>,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) {
    match data {
        // ── Literals ─────────────────────────────────────────────────
        InstData::LiteralUndefined => {
            codes.push(Bytecode::Ldundefined);
            store_result(result_slot, codes);
        }
        InstData::LiteralNull => {
            codes.push(Bytecode::Ldnull);
            store_result(result_slot, codes);
        }
        InstData::LiteralBool(true) => {
            codes.push(Bytecode::Ldtrue);
            store_result(result_slot, codes);
        }
        InstData::LiteralBool(false) => {
            codes.push(Bytecode::Ldfalse);
            store_result(result_slot, codes);
        }
        InstData::LiteralNumber(n) => {
            let bits = n.to_bits();
            if *n == (*n as i32) as f64 {
                codes.push(Bytecode::Ldai(Imm(*n as i64)));
            } else {
                codes.push(Bytecode::Fldai(Imm(bits as i64)));
            }
            store_result(result_slot, codes);
        }
        InstData::LiteralString(s) => {
            codes.push(Bytecode::LdaStr(eid(*s, string_map)));
            store_result(result_slot, codes);
        }
        InstData::LiteralNaN => {
            codes.push(Bytecode::Ldnan);
            store_result(result_slot, codes);
        }
        InstData::LiteralInfinity => {
            codes.push(Bytecode::Ldinfinity);
            store_result(result_slot, codes);
        }
        InstData::LiteralHole => {
            codes.push(Bytecode::Ldhole);
            store_result(result_slot, codes);
        }

        // ── Binary operations ────────────────────────────────────────
        InstData::BinaryOp { op, left, right } => {
            ensure_acc(*left, alloc, codes);
            let r = val_reg(*right, alloc, codes);
            let bc = match op {
                BinOp::Add => Bytecode::Add2(ic.one(), r),
                BinOp::Sub => Bytecode::Sub2(ic.one(), r),
                BinOp::Mul => Bytecode::Mul2(ic.one(), r),
                BinOp::Div => Bytecode::Div2(ic.one(), r),
                BinOp::Mod => Bytecode::Mod2(ic.one(), r),
                BinOp::Exp => Bytecode::Exp(ic.one(), r),
                BinOp::Eq => Bytecode::Eq(ic.one(), r),
                BinOp::NotEq => Bytecode::Noteq(ic.one(), r),
                BinOp::StrictEq => Bytecode::Stricteq(ic.one(), r),
                BinOp::StrictNotEq => Bytecode::Strictnoteq(ic.one(), r),
                BinOp::Less => Bytecode::Less(ic.one(), r),
                BinOp::LessEq => Bytecode::Lesseq(ic.one(), r),
                BinOp::Greater => Bytecode::Greater(ic.one(), r),
                BinOp::GreaterEq => Bytecode::Greatereq(ic.one(), r),
                BinOp::Shl => Bytecode::Shl2(ic.one(), r),
                BinOp::Shr => Bytecode::Shr2(ic.one(), r),
                BinOp::Ashr => Bytecode::Ashr2(ic.one(), r),
                BinOp::BitAnd => Bytecode::And2(ic.one(), r),
                BinOp::BitOr => Bytecode::Or2(ic.one(), r),
                BinOp::BitXor => Bytecode::Xor2(ic.one(), r),
                BinOp::In => Bytecode::Isin(ic.one(), r),
                BinOp::InstanceOf => Bytecode::Instanceof(ic.one(), r),
            };
            codes.push(bc);
            store_result(result_slot, codes);
        }

        // ── Unary operations ─────────────────────────────────────────
        InstData::UnaryOp { op, operand } => {
            ensure_acc(*operand, alloc, codes);
            let bc = match op {
                UnOp::Minus => Bytecode::Neg(ic.one()),
                UnOp::LogicalNot => Bytecode::Not(ic.one()),
                UnOp::Inc => Bytecode::Inc(ic.one()),
                UnOp::Dec => Bytecode::Dec(ic.one()),
                UnOp::TypeOf => Bytecode::Typeof(ic.one()),
                UnOp::ToNumber => Bytecode::Tonumber(ic.one()),
                UnOp::ToNumeric => Bytecode::Tonumeric(ic.one()),
                UnOp::BitNot => Bytecode::Not(ic.one()), // approximate
                UnOp::Void => Bytecode::Ldundefined,     // void x → undefined
            };
            codes.push(bc);
            store_result(result_slot, codes);
        }
        InstData::IsTrue { operand } => {
            ensure_acc(*operand, alloc, codes);
            codes.push(Bytecode::Istrue);
            store_result(result_slot, codes);
        }
        InstData::IsFalse { operand } => {
            ensure_acc(*operand, alloc, codes);
            codes.push(Bytecode::Isfalse);
            store_result(result_slot, codes);
        }

        // ── Object / Array creation ──────────────────────────────────
        InstData::CreateEmptyObject => {
            codes.push(Bytecode::Createemptyobject);
            store_result(result_slot, codes);
        }
        InstData::CreateEmptyArray => {
            codes.push(Bytecode::Createemptyarray(ic.one()));
            store_result(result_slot, codes);
        }
        InstData::CreateArrayWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createarraywithbuffer(ic.one(), la_eid));
            store_result(result_slot, codes);
        }
        InstData::CreateObjectWithBuffer { literal_array } => {
            let la_eid = EntityId(*literal_array);
            codes.push(Bytecode::Createobjectwithbuffer(ic.one(), la_eid));
            store_result(result_slot, codes);
        }
        InstData::CreateRegExp { pattern, flags } => {
            let p = eid(*pattern, string_map);
            let f_str = module.strings.get(*flags);
            let f_val: i64 = f_str.parse().unwrap_or(0);
            codes.push(Bytecode::Createregexpwithliteral(ic.one(), p, Imm(f_val)));
            store_result(result_slot, codes);
        }
        InstData::CreateObjectWithExcludedKeys { obj, keys } => {
            let obj_r = val_reg(*obj, alloc, codes);
            let start_r = if let Some(first) = keys.first() {
                val_reg(*first, alloc, codes)
            } else {
                Reg(0)
            };
            codes.push(Bytecode::Createobjectwithexcludedkeys(
                Imm(keys.len() as i64),
                obj_r,
                start_r,
            ));
            store_result(result_slot, codes);
        }

        // ── Property access ──────────────────────────────────────────
        InstData::LoadProperty { object, key } => {
            match key {
                PropKind::ByName(name) => {
                    ensure_acc(*object, alloc, codes);
                    codes.push(Bytecode::Ldobjbyname(ic.two(), eid(*name, string_map)));
                }
                PropKind::ByValue(k) => {
                    ensure_acc(*k, alloc, codes);
                    let obj_r = val_reg(*object, alloc, codes);
                    codes.push(Bytecode::Ldobjbyvalue(ic.two(), obj_r));
                }
                PropKind::ByIndex(idx) => {
                    ensure_acc(*object, alloc, codes);
                    codes.push(Bytecode::Ldobjbyindex(ic.two(), Imm(*idx as i64)));
                }
            }
            store_result(result_slot, codes);
        }
        InstData::StoreProperty { object, key, value } => match key {
            PropKind::ByName(name) => {
                ensure_acc(*value, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                codes.push(Bytecode::Stobjbyname(
                    ic.two(),
                    eid(*name, string_map),
                    obj_r,
                ));
            }
            PropKind::ByValue(k) => {
                ensure_acc(*k, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                let val_r = val_reg(*value, alloc, codes);
                codes.push(Bytecode::Stobjbyvalue(ic.two(), obj_r, val_r));
            }
            PropKind::ByIndex(idx) => {
                ensure_acc(*value, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                codes.push(Bytecode::Stobjbyindex(ic.two(), obj_r, Imm(*idx as i64)));
            }
        },
        InstData::StoreOwnProperty { object, key, value } => match key {
            PropKind::ByName(name) => {
                ensure_acc(*value, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                codes.push(Bytecode::Stownbyname(
                    ic.two(),
                    eid(*name, string_map),
                    obj_r,
                ));
            }
            PropKind::ByValue(k) => {
                ensure_acc(*value, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                let key_r = val_reg(*k, alloc, codes);
                codes.push(Bytecode::Stownbyvalue(ic.two(), obj_r, key_r));
            }
            PropKind::ByIndex(idx) => {
                ensure_acc(*value, alloc, codes);
                let obj_r = val_reg(*object, alloc, codes);
                codes.push(Bytecode::Stownbyindex(ic.two(), obj_r, Imm(*idx as i64)));
            }
        },
        InstData::DeleteProperty { object, key } => {
            ensure_acc(*object, alloc, codes);
            let key_r = val_reg(*key, alloc, codes);
            codes.push(Bytecode::Delobjprop(key_r));
            store_result(result_slot, codes);
        }
        InstData::LoadSuperProperty { key } => {
            match key {
                PropKind::ByName(name) => {
                    codes.push(Bytecode::Ldsuperbyname(ic.two(), eid(*name, string_map)));
                }
                PropKind::ByValue(k) => {
                    let key_r = val_reg(*k, alloc, codes);
                    codes.push(Bytecode::Ldsuperbyvalue(ic.two(), key_r));
                }
                PropKind::ByIndex(_) => {
                    // No direct bytecode; approximate with ByValue
                }
            }
            store_result(result_slot, codes);
        }
        InstData::StoreSuperProperty { key, value } => match key {
            PropKind::ByName(name) => {
                let val_r = val_reg(*value, alloc, codes);
                codes.push(Bytecode::Stsuperbyname(
                    ic.two(),
                    eid(*name, string_map),
                    val_r,
                ));
            }
            PropKind::ByValue(k) => {
                let key_r = val_reg(*k, alloc, codes);
                let val_r = val_reg(*value, alloc, codes);
                codes.push(Bytecode::Stsuperbyvalue(ic.two(), key_r, val_r));
            }
            PropKind::ByIndex(_) => {}
        },

        // ── Global variables ─────────────────────────────────────────
        InstData::LoadGlobalVar { name } => {
            codes.push(Bytecode::Ldglobalvar(ic.one(), eid(*name, string_map)));
            store_result(result_slot, codes);
        }
        InstData::StoreGlobalVar { name, value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::Stglobalvar(ic.one(), eid(*name, string_map)));
        }
        InstData::TryLoadGlobalByName { name } => {
            codes.push(Bytecode::Tryldglobalbyname(
                ic.one(),
                eid(*name, string_map),
            ));
            store_result(result_slot, codes);
        }
        InstData::TryStoreGlobalByName { name, value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::Trystglobalbyname(
                ic.one(),
                eid(*name, string_map),
            ));
        }

        // ── Lexical variables ────────────────────────────────────────
        InstData::LoadLexVar { level, slot } => {
            codes.push(Bytecode::Ldlexvar(Imm(*level as i64), Imm(*slot as i64)));
            store_result(result_slot, codes);
        }
        InstData::StoreLexVar { level, slot, value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::Stlexvar(Imm(*level as i64), Imm(*slot as i64)));
        }
        InstData::NewLexEnv { num_vars } => {
            codes.push(Bytecode::Newlexenv(Imm(*num_vars as i64)));
            store_result(result_slot, codes);
        }
        InstData::NewLexEnvWithName {
            num_vars,
            scope_name,
        } => {
            codes.push(Bytecode::Newlexenvwithname(
                Imm(*num_vars as i64),
                eid(*scope_name, string_map),
            ));
            store_result(result_slot, codes);
        }
        InstData::PopLexEnv => {
            codes.push(Bytecode::Poplexenv);
        }

        // ── Module variables ─────────────────────────────────────────
        InstData::LoadLocalModuleVar { index } => {
            codes.push(Bytecode::Ldlocalmodulevar(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::LoadExternalModuleVar { index } => {
            codes.push(Bytecode::Ldexternalmodulevar(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::StoreModuleVar { index, value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::Stmodulevar(Imm(*index as i64)));
        }
        InstData::GetModuleNamespace { index } => {
            codes.push(Bytecode::Getmodulenamespace(Imm(*index as i64)));
            store_result(result_slot, codes);
        }
        InstData::DynamicImport { specifier } => {
            ensure_acc(*specifier, alloc, codes);
            codes.push(Bytecode::Dynamicimport);
            store_result(result_slot, codes);
        }

        // ── Function / Class definition ──────────────────────────────
        InstData::DefineFunc { method_id, length } => {
            codes.push(Bytecode::Definefunc(
                ic.one(),
                eid(*method_id, string_map),
                Imm(*length as i64),
            ));
            store_result(result_slot, codes);
        }
        InstData::DefineMethod {
            method_id,
            length,
            home_object,
        } => {
            ensure_acc(*home_object, alloc, codes);
            codes.push(Bytecode::Definemethod(
                ic.one(),
                eid(*method_id, string_map),
                Imm(*length as i64),
            ));
            store_result(result_slot, codes);
        }
        InstData::DefineClassWithBuffer {
            method_id,
            literal_array,
            base,
        } => {
            let base_r = val_reg(*base, alloc, codes);
            codes.push(Bytecode::Defineclasswithbuffer(
                ic.one(),
                eid(*method_id, string_map),
                EntityId(*literal_array),
                Imm(0),
                base_r,
            ));
            store_result(result_slot, codes);
        }
        InstData::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            let obj_r = val_reg(*obj, alloc, codes);
            let key_r = val_reg(*key, alloc, codes);
            let getter_r = val_reg(*getter, alloc, codes);
            let setter_r = val_reg(*setter, alloc, codes);
            codes.push(Bytecode::Definegettersetterbyvalue(
                obj_r, key_r, getter_r, setter_r,
            ));
            store_result(result_slot, codes);
        }

        // ── Calls ────────────────────────────────────────────────────
        InstData::Call { kind, callee, args } => {
            select_call(*kind, *callee, args, alloc, codes, ic);
            store_result(result_slot, codes);
        }

        // ── Special value loaders ────────────────────────────────────
        InstData::LoadThis => {
            codes.push(Bytecode::Ldthis);
            store_result(result_slot, codes);
        }
        InstData::LoadNewTarget => {
            codes.push(Bytecode::Ldnewtarget);
            store_result(result_slot, codes);
        }
        InstData::LoadGlobalObject => {
            codes.push(Bytecode::Ldglobal);
            store_result(result_slot, codes);
        }
        InstData::LoadFunction => {
            codes.push(Bytecode::Ldfunction);
            store_result(result_slot, codes);
        }
        InstData::GetUnmappedArgs => {
            codes.push(Bytecode::Getunmappedargs);
            store_result(result_slot, codes);
        }
        InstData::CopyRestArgs { start_index } => {
            codes.push(Bytecode::Copyrestargs(Imm(*start_index as i64)));
            store_result(result_slot, codes);
        }

        // ── Iterators ────────────────────────────────────────────────
        InstData::GetIterator { obj } => {
            ensure_acc(*obj, alloc, codes);
            codes.push(Bytecode::Getiterator(ic.two()));
            store_result(result_slot, codes);
        }
        InstData::GetAsyncIterator { obj } => {
            ensure_acc(*obj, alloc, codes);
            codes.push(Bytecode::Getasynciterator(ic.two()));
            store_result(result_slot, codes);
        }
        InstData::GetPropIterator { obj } => {
            ensure_acc(*obj, alloc, codes);
            codes.push(Bytecode::Getpropiterator);
            store_result(result_slot, codes);
        }
        InstData::CloseIterator { iterator } => {
            let iter_r = val_reg(*iterator, alloc, codes);
            codes.push(Bytecode::Closeiterator(ic.two(), iter_r));
            store_result(result_slot, codes);
        }

        // ── Generator / Async ────────────────────────────────────────
        InstData::CreateGeneratorObj { func } => {
            let func_r = val_reg(*func, alloc, codes);
            codes.push(Bytecode::Creategeneratorobj(func_r));
            store_result(result_slot, codes);
        }
        InstData::SuspendGenerator { value } => {
            let val_r = val_reg(*value, alloc, codes);
            codes.push(Bytecode::Suspendgenerator(val_r));
            store_result(result_slot, codes);
        }
        InstData::ResumeGenerator => {
            codes.push(Bytecode::Resumegenerator);
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionEnter => {
            codes.push(Bytecode::Asyncfunctionenter);
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionAwaitUncaught { value } => {
            let val_r = val_reg(*value, alloc, codes);
            codes.push(Bytecode::Asyncfunctionawaituncaught(val_r));
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionResolve { value } => {
            let val_r = val_reg(*value, alloc, codes);
            codes.push(Bytecode::Asyncfunctionresolve(val_r));
            store_result(result_slot, codes);
        }
        InstData::AsyncFunctionReject { value } => {
            let val_r = val_reg(*value, alloc, codes);
            codes.push(Bytecode::Asyncfunctionreject(val_r));
            store_result(result_slot, codes);
        }
        InstData::CreateIterResultObj { value, done } => {
            let val_r = val_reg(*value, alloc, codes);
            let done_r = val_reg(*done, alloc, codes);
            codes.push(Bytecode::Createiterresultobj(val_r, done_r));
            store_result(result_slot, codes);
        }

        // ── Exception handling ───────────────────────────────────────
        InstData::Throw { value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::Throw);
        }
        InstData::ThrowIfNotObject { value } => {
            let val_r = val_reg(*value, alloc, codes);
            codes.push(Bytecode::ThrowIfnotobject(val_r));
        }
        InstData::ThrowConstAssignment { .. } => {
            // ThrowConstassignment takes a Reg; use a dummy
            codes.push(Bytecode::ThrowConstassignment(Reg(0)));
        }
        InstData::ThrowUndefinedIfHole { name, value } => {
            let val_r = val_reg(*value, alloc, codes);
            // ThrowUndefinedifholewithname is simpler
            codes.push(Bytecode::ThrowUndefinedifholewithname(eid(
                *name, string_map,
            )));
            let _ = val_r;
        }
        InstData::ThrowIfSuperNotCorrectCall { value } => {
            ensure_acc(*value, alloc, codes);
            codes.push(Bytecode::ThrowIfsupernotcorrectcall(Imm(0)));
        }
        InstData::ThrowNotExists => {
            codes.push(Bytecode::ThrowNotexists);
        }
        InstData::ThrowPatternNonCoercible => {
            codes.push(Bytecode::ThrowPatternnoncoercible);
        }
        InstData::ThrowDeleteSuperProperty => {
            codes.push(Bytecode::ThrowDeletesuperproperty);
        }

        // ── Terminators ──────────────────────────────────────────────
        // Branch/CondBranch are handled in layout.rs (jump target resolution).
        // We emit placeholder labels here; layout will fix them.
        InstData::Branch { dest } => {
            codes.push(Bytecode::Jmp(Label(dest.0)));
        }
        InstData::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            // Try compare-branch fusion: if cond is IsTrue(CmpOp(a, b)),
            // emit a fused Jeq/Jne/Jstricteq/Jnstricteq instead of Jnez.
            if let Some(fused) = try_fuse_cmp_branch(*cond, *true_dest, module, alloc, codes) {
                codes.push(fused);
            } else {
                ensure_acc(*cond, alloc, codes);
                // Emit: if acc truthy → jump to true_dest, fall through to false_dest
                codes.push(Bytecode::Jnez(Label(true_dest.0)));
            }
            // The fall-through to false_dest is implicit if it's the next block.
            // Layout will insert a Jmp if needed.
            let _ = false_dest;
        }
        InstData::Return { value } => {
            if let Some(val) = value {
                ensure_acc(*val, alloc, codes);
                codes.push(Bytecode::Return);
            } else {
                codes.push(Bytecode::Returnundefined);
            }
        }
        InstData::Unreachable => {
            codes.push(Bytecode::Returnundefined);
        }

        // ── Phi / Debug ──────────────────────────────────────────────
        InstData::Phi { .. } => {
            // Handled by phi elimination, not emitted directly.
        }
        InstData::Debugger => {
            codes.push(Bytecode::Debugger);
        }
    }
}

/// Select call bytecodes based on kind and argument count.
fn select_call(
    kind: CallKind,
    callee: Value,
    args: &[Value],
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
    ic: &mut IcAllocator,
) {
    match kind {
        CallKind::Call => {
            ensure_acc(callee, alloc, codes);
            match args.len() {
                0 => codes.push(Bytecode::Callarg0(ic.two())),
                1 => {
                    let a0 = val_reg(args[0], alloc, codes);
                    codes.push(Bytecode::Callarg1(ic.two(), a0));
                }
                2 => {
                    let a0 = val_reg(args[0], alloc, codes);
                    let a1 = val_reg(args[1], alloc, codes);
                    codes.push(Bytecode::Callargs2(ic.two(), a0, a1));
                }
                3 => {
                    let a0 = val_reg(args[0], alloc, codes);
                    let a1 = val_reg(args[1], alloc, codes);
                    let a2 = val_reg(args[2], alloc, codes);
                    codes.push(Bytecode::Callargs3(ic.two(), a0, a1, a2));
                }
                n => {
                    let start = val_reg(args[0], alloc, codes);
                    codes.push(Bytecode::Callrange(ic.two(), Imm(n as i64), start));
                }
            }
        }
        CallKind::CallThis => {
            ensure_acc(callee, alloc, codes);
            // args[0] = this, args[1..] = actual args
            match args.len() {
                0 => {
                    // No this — shouldn't happen, but handle gracefully
                    codes.push(Bytecode::Callarg0(ic.two()));
                }
                1 => {
                    let this_r = val_reg(args[0], alloc, codes);
                    codes.push(Bytecode::Callthis0(ic.two(), this_r));
                }
                2 => {
                    let this_r = val_reg(args[0], alloc, codes);
                    let a0 = val_reg(args[1], alloc, codes);
                    codes.push(Bytecode::Callthis1(ic.two(), this_r, a0));
                }
                3 => {
                    let this_r = val_reg(args[0], alloc, codes);
                    let a0 = val_reg(args[1], alloc, codes);
                    let a1 = val_reg(args[2], alloc, codes);
                    codes.push(Bytecode::Callthis2(ic.two(), this_r, a0, a1));
                }
                4 => {
                    let this_r = val_reg(args[0], alloc, codes);
                    let a0 = val_reg(args[1], alloc, codes);
                    let a1 = val_reg(args[2], alloc, codes);
                    let a2 = val_reg(args[3], alloc, codes);
                    codes.push(Bytecode::Callthis3(ic.two(), this_r, a0, a1, a2));
                }
                n => {
                    let start = val_reg(args[0], alloc, codes);
                    codes.push(Bytecode::Callthisrange(ic.two(), Imm(n as i64), start));
                }
            }
        }
        CallKind::SuperCall => {
            ensure_acc(callee, alloc, codes);
            let start = if args.is_empty() {
                Reg(0)
            } else {
                val_reg(args[0], alloc, codes)
            };
            codes.push(Bytecode::Supercallthisrange(
                ic.two(),
                Imm(args.len() as i64),
                start,
            ));
        }
        CallKind::SuperCallArrow => {
            ensure_acc(callee, alloc, codes);
            let start = if args.is_empty() {
                Reg(0)
            } else {
                val_reg(args[0], alloc, codes)
            };
            codes.push(Bytecode::Supercallarrowrange(
                ic.two(),
                Imm(args.len() as i64),
                start,
            ));
        }
        CallKind::SuperCallSpread => {
            ensure_acc(callee, alloc, codes);
            let arg_r = if args.is_empty() {
                Reg(0)
            } else {
                val_reg(args[0], alloc, codes)
            };
            codes.push(Bytecode::Supercallspread(ic.two(), arg_r));
        }
        CallKind::Apply => {
            ensure_acc(callee, alloc, codes);
            if args.len() >= 2 {
                let this_r = val_reg(args[0], alloc, codes);
                let args_r = val_reg(args[1], alloc, codes);
                codes.push(Bytecode::Apply(ic.two(), this_r, args_r));
            } else if args.len() == 1 {
                let arg_r = val_reg(args[0], alloc, codes);
                codes.push(Bytecode::Newobjapply(ic.two(), arg_r));
            } else {
                codes.push(Bytecode::Callarg0(ic.two()));
            }
        }
    }
}

/// Try to fuse a compare + branch into a single bytecode.
///
/// Pattern: `CondBranch(cond: IsTrue(BinaryOp { op: Eq|StrictEq|..., left, right }), true_dest)`
/// → `Jeq(right_reg, true_dest)` with left in acc.
///
/// Returns `Some(fused_bytecode)` if fusion succeeded, `None` otherwise.
fn try_fuse_cmp_branch(
    cond: Value,
    true_dest: Block,
    module: &Module,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Option<Bytecode> {
    let cond_def = module.value(cond);
    let cond_inst = match cond_def.def {
        crate::module::ValueDef::Inst(i) => i,
        _ => return None,
    };

    // Check if cond is IsTrue { operand }
    let inner_val = match &module.inst(cond_inst).data {
        InstData::IsTrue { operand } => *operand,
        // If cond is directly a comparison (without IsTrue wrapper), also fuse.
        InstData::BinaryOp { op, left, right } => {
            return fuse_binop_branch(*op, *left, *right, true_dest, alloc, codes);
        }
        _ => return None,
    };

    // Check if inner_val is BinaryOp { op: comparison, left, right }
    let inner_def = module.value(inner_val);
    let inner_inst = match inner_def.def {
        crate::module::ValueDef::Inst(i) => i,
        _ => return None,
    };

    match &module.inst(inner_inst).data {
        InstData::BinaryOp { op, left, right } => {
            fuse_binop_branch(*op, *left, *right, true_dest, alloc, codes)
        }
        _ => None,
    }
}

/// Emit a fused compare-branch for a BinOp comparison.
fn fuse_binop_branch(
    op: BinOp,
    left: Value,
    right: Value,
    true_dest: Block,
    alloc: &RegAlloc,
    codes: &mut Vec<Bytecode>,
) -> Option<Bytecode> {
    let label = Label(true_dest.0);
    match op {
        BinOp::Eq => {
            ensure_acc(left, alloc, codes);
            let r = val_reg(right, alloc, codes);
            Some(Bytecode::Jeq(r, label))
        }
        BinOp::NotEq => {
            ensure_acc(left, alloc, codes);
            let r = val_reg(right, alloc, codes);
            Some(Bytecode::Jne(r, label))
        }
        BinOp::StrictEq => {
            ensure_acc(left, alloc, codes);
            let r = val_reg(right, alloc, codes);
            Some(Bytecode::Jstricteq(r, label))
        }
        BinOp::StrictNotEq => {
            ensure_acc(left, alloc, codes);
            let r = val_reg(right, alloc, codes);
            Some(Bytecode::Jnstricteq(r, label))
        }
        // No fused bytecodes for Less/Greater/etc in ABC ISA.
        _ => None,
    }
}
