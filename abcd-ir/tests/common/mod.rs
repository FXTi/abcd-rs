//! Minimal deterministic bytecode interpreter shared by the lowering
//! regression tests.
//!
//! It supports only the opcodes the crafted sequences use
//! (`Lda`/`Sta`/`Mov`/`Ldai`/`Ldundefined`/`Ldhole`/`Add2`/`Sub2`/
//! `Greater`/`Eq`/`Istrue`/`Jmp`/`Jnez`/`Jeq`/`Return`/`Returnundefined`,
//! no-op `Stobjbyname`, plus
//! record-and-stop for `Stobjbyvalue`). Labels in `layout` output are
//! already resolved to absolute instruction indices by `resolve_labels`,
//! so jumps use the label operand directly as a program counter.

use std::collections::HashMap;

use abcd_isa::Bytecode;

/// What the machine observed when execution stopped.
#[allow(dead_code)] // variants are constructed only when a path executes them
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Halt {
    /// `Return`: accumulator value at the point of return.
    Return(i64),
    /// `Returnundefined`.
    ReturnUndefined,
    /// `Stobjbyvalue` (record-and-inspect): `obj` is the FIRST register
    /// operand's contents (the receiver), `key` the SECOND register
    /// operand's contents (the propKey), `value` the accumulator —
    /// vendor `stobjbyvalue imm:u16, v1:in:top, v2:in:top, acc: in:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1353-1357;
    /// interpreter_assembly.cpp:2306-2335: `receiver =
    /// GET_VREG_VALUE(v0)`, `propKey = GET_VREG_VALUE(v1)`, `value =
    /// GET_ACC()`).
    StObjByValue { key: i64, obj: i64, value: i64 },
    /// `Copydataproperties` (record-and-inspect): `dst` is the operand
    /// register's contents (the target object), `src` the accumulator
    /// (the source object) — vendor `copydataproperties v:in:top,
    /// acc: inout:top`.
    CopyDataProperties { dst: i64, src: i64 },
    /// `Callrange` (record-and-inspect): vendor `callrange imm1:u8, imm2:u8,
    /// v:in:top` (isa.yaml ~:1082) — imm1 is the IC slot (ignored), imm2 the
    /// argument count, v the START of the consecutive argument register
    /// window. `argc`/`start` are the recorded operands; the argument
    /// values are `regs[start .. start + argc]` at halt time.
    CallRange { argc: i64, start: u16 },
    /// `WideCallrange` (record-and-inspect): vendor `wide.callrange imm:u16,
    /// v:in:top` (isa.yaml ~:1087) — imm is the u16 argument count, v the
    /// u8 window start; NO IC slot operand on the wide form.
    WideCallRange { argc: i64, start: u16 },
    /// `Newobjrange` (record-and-inspect): vendor `newobjrange imm1:u16,
    /// imm2:u8, v:in:top` (abcd-isa-sys/vendor/isa/isa.yaml ~:535) — imm1 is
    /// the IC slot (ignored), imm2 the argument count INCLUDING the
    /// constructor, v the START of the consecutive register window whose
    /// FIRST slot holds the constructor (vendor
    /// arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:4205
    /// passes `NewObjRange(thread, ctor, ctor, ...)` — ctor as both func and
    /// newTarget). The window contents are `regs[start .. start + argc]`
    /// at halt time: window[0] = ctor, window[1..] = the call arguments.
    NewObjRange { argc: i64, start: u16 },
    /// `WideNewobjrange` (record-and-inspect): vendor `wide.newobjrange
    /// imm:u16, v:in:top` (abcd-isa-sys/vendor/isa/isa.yaml ~:540) — u16
    /// argument count including the constructor, u8 window start, NO IC
    /// slot operand on the wide form.
    WideNewObjRange { argc: i64, start: u16 },
    /// `Suspendgenerator` (record-and-inspect): `genobj` is the operand
    /// register's contents (the generator object), `value` the
    /// accumulator (the YIELD VALUE) — vendor `suspendgenerator v:in:top,
    /// acc: inout:top` (abcd-isa-sys/vendor/isa/isa.yaml:1302-1305).
    SuspendGenerator { genobj: i64, value: i64 },
    /// `Resumegenerator` (record-and-inspect): `genobj` is the
    /// accumulator (the generator object) — vendor `resumegenerator`
    /// with `acc: inout:top`, NO register operand
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1261-1264).
    ResumeGenerator { genobj: i64 },
    /// `Getresumemode` (record-and-inspect): `genobj` is the accumulator
    /// (the generator object) — vendor `getresumemode` with
    /// `acc: inout:top`, NO register operand
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1270-1273).
    GetResumeMode { genobj: i64 },
    /// `ThrowIfsupernotcorrectcall` (record-and-stop): `value` is the
    /// accumulator (the `this` value being checked), `kind` the imm
    /// operand selecting the check kind — vendor
    /// `throw.ifsupernotcorrectcall imm:u16, acc: in:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1003-1008; kind semantics in
    /// arkcompiler_ets_runtime ecmascript/stubs/runtime_stubs-inl.h:
    /// 2520-2532).
    ThrowIfSuperNotCorrectCall { kind: i64, value: i64 },
    /// `Definegettersetterbyvalue` (record-and-inspect): the four register
    /// operands' contents (obj, key, getter, setter) — vendor
    /// `definegettersetterbyvalue v0:in:top, v1:in:top, v2:in:top,
    /// v3:in:top` with `acc: inout:top`.
    DefineGetterSetterByValue {
        obj: i64,
        key: i64,
        getter: i64,
        setter: i64,
    },
    /// `ThrowConstassignment` (record-and-stop): `name` is the operand
    /// register's contents — the variable NAME string VALUE — vendor
    /// `throw.constassignment v:in:top, acc: none`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:987-991).
    ThrowConstAssignment { name: i64 },
    /// `ThrowUndefinedifhole` (record-and-stop): `name` is the FIRST
    /// register operand's contents (the variable name string VALUE),
    /// `value` the SECOND register operand's contents (the checked
    /// value) — vendor `throw.undefinedifhole v1:in:top, v2:in:top,
    /// acc: none` (abcd-isa-sys/vendor/isa/isa.yaml:998-1002).
    ThrowUndefinedIfHole { name: i64, value: i64 },
    /// `ThrowUndefinedifholewithname` (record-and-stop): `value` is the
    /// accumulator (the checked value) — vendor
    /// `throw.undefinedifholewithname string_id, acc: in:top`
    /// (abcd-isa-sys/vendor/isa/isa.yaml:1010-1015).
    ThrowUndefinedIfHoleWithName { value: i64 },
    /// `run_until` reached the stop pc WITHOUT executing the instruction
    /// there — models an exception thrown between two instructions.
    Stopped,
}

/// A tiny register machine: `HashMap<u16, i64>` registers plus one
/// accumulator. Missing registers read as 0.
pub struct Machine {
    pub regs: HashMap<u16, i64>,
    pub acc: i64,
}

/// Frame-initial value sentinels. The i64 machine has no tagged values,
/// so the two VM frame-initial states are modeled as distinct sentinels:
///
/// - `UNDEFINED`: every vreg slot is initialized to `undefined` at frame
///   creation — vendor `CALL_PUSH_UNDEFINED(numVregs)` pushing
///   `JSTaggedValue::VALUE_UNDEFINED`
///   (arkcompiler_ets_runtime-master/ecmascript/interpreter/interpreter-inl.cpp:285-291,
///   call sites :731-732 and :1471-1472; same fill in the fast-new-frame
///   path, interpreter_assembly.cpp:3653-3657).
/// - `HOLE`: the accumulator is initialized to the hole at frame creation
///   — vendor `state->acc = JSTaggedValue::Hole()`
///   (interpreter-inl.cpp:739 and :1482, interpreter_assembly.cpp:3695).
#[allow(dead_code)] // used by the vreg-hole regressions
pub const UNDEFINED: i64 = i64::MIN;
#[allow(dead_code)]
pub const HOLE: i64 = i64::MIN + 1;
/// Sentinel for `createemptyobject` — the i64 machine has no objects, so
/// the created empty object is modeled as a distinct sentinel (N27 tests).
#[allow(dead_code)]
pub const EMPTY_OBJECT: i64 = i64::MIN + 2;

#[allow(dead_code)] // helpers are shared across several test binaries
impl Machine {
    pub fn new() -> Self {
        Self {
            regs: HashMap::new(),
            acc: 0,
        }
    }

    pub fn with_reg(mut self, reg: u16, val: i64) -> Self {
        self.regs.insert(reg, val);
        self
    }

    pub fn with_acc(mut self, val: i64) -> Self {
        self.acc = val;
        self
    }

    pub fn reg(&self, reg: u16) -> i64 {
        self.regs.get(&reg).copied().unwrap_or(0)
    }

    /// Execute `code` from index 0 until a terminator/`Stobjbyvalue`.
    /// Panics on any opcode outside the supported subset.
    pub fn run(&mut self, code: &[Bytecode]) -> Halt {
        self.run_at(code, 0)
    }

    /// Execute `code` from `pc` until a terminator/`Stobjbyvalue`.
    /// Used to simulate exception dispatch: the VM enters a catch handler
    /// at its `TryBlock` offset, not at pc 0.
    pub fn run_at(&mut self, code: &[Bytecode], pc: usize) -> Halt {
        self.exec(code, pc, None)
    }

    /// Execute `code` from `pc`, stopping WITHOUT executing the
    /// instruction at `stop_pc` (returns [`Halt::Stopped`]). Simulates an
    /// exception thrown between two instructions: run a try body up to
    /// the throw point, then enter the handler with `run_at`.
    pub fn run_until(&mut self, code: &[Bytecode], pc: usize, stop_pc: usize) -> Halt {
        self.exec(code, pc, Some(stop_pc))
    }

    fn exec(&mut self, code: &[Bytecode], pc: usize, stop_pc: Option<usize>) -> Halt {
        let mut pc = pc;
        loop {
            if Some(pc) == stop_pc {
                return Halt::Stopped;
            }
            let Some(bc) = code.get(pc) else {
                panic!("simulator: program counter {pc} escaped the code buffer")
            };
            match *bc {
                Bytecode::Lda(r) => {
                    self.acc = self.reg(r.0);
                    pc += 1;
                }
                Bytecode::Sta(r) => {
                    self.regs.insert(r.0, self.acc);
                    pc += 1;
                }
                // `mov v1:out, v2:in` — first operand is the destination.
                Bytecode::Mov(dst, src) => {
                    let val = self.reg(src.0);
                    self.regs.insert(dst.0, val);
                    pc += 1;
                }
                Bytecode::Ldai(imm) => {
                    self.acc = imm.0;
                    pc += 1;
                }
                // `ldundefined` — acc = undefined (frame-initial vreg
                // value; see the UNDEFINED sentinel docs).
                Bytecode::Ldundefined => {
                    self.acc = UNDEFINED;
                    pc += 1;
                }
                // `ldtrue`/`ldfalse` — acc = the boolean constant
                // (modeled as 1/0).
                Bytecode::Ldtrue => {
                    self.acc = 1;
                    pc += 1;
                }
                Bytecode::Ldfalse => {
                    self.acc = 0;
                    pc += 1;
                }
                // `ldhole` — acc = hole (frame-initial acc value; see the
                // HOLE sentinel docs).
                Bytecode::Ldhole => {
                    self.acc = HOLE;
                    pc += 1;
                }
                // `createemptyobject` — acc = a fresh empty object
                // (modeled as the EMPTY_OBJECT sentinel).
                Bytecode::Createemptyobject => {
                    self.acc = EMPTY_OBJECT;
                    pc += 1;
                }
                // `add2 imm:u8, v:in:top` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 590):
                // acc = acc + v0 (ic slot operand ignored).
                Bytecode::Add2(_, r) => {
                    self.acc += self.reg(r.0);
                    pc += 1;
                }
                // `sub2 imm, v0` — acc = acc - v0 (ic slot operand ignored).
                Bytecode::Sub2(_, r) => {
                    self.acc -= self.reg(r.0);
                    pc += 1;
                }
                // `greater imm, v0` — acc = (acc > v0) (ic slot operand ignored).
                Bytecode::Greater(_, r) => {
                    self.acc = i64::from(self.acc > self.reg(r.0));
                    pc += 1;
                }
                // `eq imm:u8, v:in:top` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 615):
                // acc = (acc == v0) (ic slot operand ignored).
                Bytecode::Eq(_, r) => {
                    self.acc = i64::from(self.acc == self.reg(r.0));
                    pc += 1;
                }
                // `istrue` with `acc: inout:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 761):
                // acc = ToBoolean(acc); the machine's i64 values model
                // truthiness as != 0.
                Bytecode::Istrue => {
                    self.acc = i64::from(self.acc != 0);
                    pc += 1;
                }
                Bytecode::Jmp(label) => {
                    pc = label.0 as usize;
                }
                Bytecode::Jnez(label) => {
                    if self.acc != 0 {
                        pc = label.0 as usize;
                    } else {
                        pc += 1;
                    }
                }
                // `jeq v:in:top, imm:i16` with `acc: in:top`
                // (vendor arkcompiler_runtime_core-master/isa/isa.yaml line 1746):
                // jump if acc == v0.
                Bytecode::Jeq(r, label) => {
                    if self.acc == self.reg(r.0) {
                        pc = label.0 as usize;
                    } else {
                        pc += 1;
                    }
                }
                Bytecode::Return => return Halt::Return(self.acc),
                Bytecode::Returnundefined => return Halt::ReturnUndefined,
                Bytecode::Stobjbyvalue(_, obj_r, key_r) => {
                    return Halt::StObjByValue {
                        key: self.reg(key_r.0),
                        obj: self.reg(obj_r.0),
                        value: self.acc,
                    };
                }
                // Store to a named property: a side effect the lowering
                // regressions only use to pin register-resident values.
                Bytecode::Stobjbyname(..) => {
                    pc += 1;
                }
                // Store to a named global: same side-effect-only treatment
                // (vendor `stglobalvar imm, string_id` with `acc: in:top`
                // — it reads but never writes the accumulator).
                Bytecode::Stglobalvar(..) => {
                    pc += 1;
                }
                Bytecode::Copydataproperties(dst_r) => {
                    return Halt::CopyDataProperties {
                        dst: self.reg(dst_r.0),
                        src: self.acc,
                    };
                }
                // `callrange imm1:u8, imm2:u8, v:in:top` — record imm2 (argc)
                // and v (window start); the IC slot imm1 is ignored.
                Bytecode::Callrange(_, argc, start) => {
                    return Halt::CallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                // `wide.callrange imm:u16, v:in:top` — u16 argc, u8 start,
                // no IC slot.
                Bytecode::WideCallrange(argc, start) => {
                    return Halt::WideCallRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                // `newobjrange imm1:u16, imm2:u8, v:in:top` — record imm2
                // (argc, INCLUDING the constructor) and v (window start;
                // window[0] is the constructor). The IC slot imm1 is ignored.
                Bytecode::Newobjrange(_, argc, start) => {
                    return Halt::NewObjRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                // `wide.newobjrange imm:u16, v:in:top` — u16 argc including
                // the constructor, u8 start, no IC slot.
                Bytecode::WideNewobjrange(argc, start) => {
                    return Halt::WideNewObjRange {
                        argc: argc.0,
                        start: start.0,
                    };
                }
                // `suspendgenerator v:in:top, acc: inout:top`
                // (isa.yaml:1302-1305) — record the genobj register's
                // contents and the acc (the yield value).
                Bytecode::Suspendgenerator(gen_r) => {
                    return Halt::SuspendGenerator {
                        genobj: self.reg(gen_r.0),
                        value: self.acc,
                    };
                }
                // `resumegenerator acc: inout:top` (isa.yaml:1261-1264) —
                // record the acc (the genobj).
                Bytecode::Resumegenerator => {
                    return Halt::ResumeGenerator { genobj: self.acc };
                }
                // `getresumemode acc: inout:top` (isa.yaml:1270-1273) —
                // record the acc (the genobj).
                Bytecode::Getresumemode => {
                    return Halt::GetResumeMode { genobj: self.acc };
                }
                // `throw.ifsupernotcorrectcall imm:u16, acc: in:top`
                // (isa.yaml:1003-1008) — record the acc (the checked
                // `this` value) and the kind imm.
                Bytecode::ThrowIfsupernotcorrectcall(imm) => {
                    return Halt::ThrowIfSuperNotCorrectCall {
                        kind: imm.0,
                        value: self.acc,
                    };
                }
                // `definegettersetterbyvalue v0, v1, v2, v3` — record the
                // four register operands (obj, key, getter, setter).
                Bytecode::Definegettersetterbyvalue(obj_r, key_r, get_r, set_r) => {
                    return Halt::DefineGetterSetterByValue {
                        obj: self.reg(obj_r.0),
                        key: self.reg(key_r.0),
                        getter: self.reg(get_r.0),
                        setter: self.reg(set_r.0),
                    };
                }
                // `throw.constassignment v:in:top, acc: none`
                // (isa.yaml:987-991) — record the name register's contents
                // (the variable name string value).
                Bytecode::ThrowConstassignment(name_r) => {
                    return Halt::ThrowConstAssignment {
                        name: self.reg(name_r.0),
                    };
                }
                // `throw.undefinedifhole v1:in:top, v2:in:top, acc: none`
                // (isa.yaml:998-1002) — record the name register's and the
                // value register's contents.
                Bytecode::ThrowUndefinedifhole(name_r, val_r) => {
                    return Halt::ThrowUndefinedIfHole {
                        name: self.reg(name_r.0),
                        value: self.reg(val_r.0),
                    };
                }
                // `throw.undefinedifholewithname string_id, acc: in:top`
                // (isa.yaml:1010-1015) — record the acc (the checked value).
                Bytecode::ThrowUndefinedifholewithname(_) => {
                    return Halt::ThrowUndefinedIfHoleWithName { value: self.acc };
                }
                other => panic!("simulator: unsupported bytecode {other:?}"),
            }
        }
    }
}
