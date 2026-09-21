//! Canonical op-stream comparison: v0.1 lifted module
//! (`abcd_ir::lift::lift_file`) vs v0.2 lifted module
//! (`abcd_lift::lift_file`).
//!
//! Method (the P1 card's preferred design): per function, both modules
//! reduce to ONE canonical instruction stream —
//!
//! - op NAMES through the documented mapping table (the same table
//!   `translate.rs`'s header spells out; v0.1's ~70 `InstData` variants
//!   fold onto the v0.2 ops exactly the way the lift folds them);
//! - operand ROLES, with SSA values renamed by a stable numbering
//!   (`p{i}` params, `exc{b}` handler params, `c:<content>` constants,
//!   `t{k}` instruction results in stream position);
//! - constants BY VALUE (numbers as raw bits, strings/symbols by
//!   content, literal-array shapes as canonical content trees, method
//!   references by function-table index);
//! - blocks by index (both lifts build identical CFGs: same leader
//!   partition, same edges, same N18 sweep).
//!
//! Deliberate divergences handled by the canonicalization itself (the
//! documented list — each has a rule below):
//!
//! 1. **Frame-initial representation**: v0.1 materializes
//!    `LiteralUndefined`/`LiteralHole` seeding instructions at the entry
//!    top (loc-less); v0.2 uses `ValueDef::Const` values. Rule: v0.1's
//!    loc-less literal results rename to the constant, and the seeding
//!    instructions drop out of the stream.
//! 2. **`ldthis`**: v0.1 emits `LoadThis`; v0.2 aliases `params[0]`
//!    (non-static) or a materialized `undefined` (static). Rule:
//!    v0.1's `LoadThis` result renames accordingly, instruction drops.
//! 3. **Expansion mappings**: v0.2 materializes what v0.1 packs into
//!    one instruction — `definefunc` → `DefineFunc` + `AllocClosure`;
//!    `definemethod` → + `DefineMethod`; constant property indices →
//!    `LoadConst` + `LoadPropIdx`; try-load-global → `LoadConst` +
//!    `TryGetGlobal`; throw-undefined-if-hole-with-name → (name as
//!    `Sym`, no materialization in v0.2). Rule: the v0.1 side expands
//!    to the same token sequence.
//! 4. **Call-kind normalization**: v0.1's arity/leak kinds (`CallThis`,
//!    `SuperCall`, `SuperCallArrow`, `NewObjApply`, `Construct`)
//!    normalize to `Dynamic`/`Super`/`New` with explicit `this` roles —
//!    including `NewObjApply`'s swapped vendor roles (v0.2 normalizes
//!    to callee=ctor). `Apply` (N57) and `SuperCallSpread` (N58) are
//!    NOT normalized: both IRs carry those distinctions explicitly and
//!    they compare exactly. v0.2's `SuperForwardAllArgs` canonicalizes
//!    DOWN to `super` (N58 residual fold): v0.1 represents the
//!    forward-all form as plain `SuperCall`, indistinguishable from
//!    `supercallthisrange` — the v0.2 kind is strictly more precise
//!    than anything v0.1 can express.
//! 5. **Folded distinctions**: local-vs-external module vars and
//!    async-vs-sync iterators/generators fold per the mapping table.
//!    NOT folded (they compare exactly): the object/array
//!    literal-buffer tag (N59 — v0.1
//!    `CreateObjectWithBuffer`/`CreateArrayWithBuffer` vs v0.2
//!    `AllocObject`/`AllocArray{Some}`), the own-vs-plain store
//!    distinction (N60 — v0.1 `StoreOwnProperty` vs v0.2
//!    `StoreOwnProp{Name,Dyn,Idx}`), and the tolerant-vs-throwing
//!    global store (N61 — v0.1 `TryStoreGlobalByName` vs v0.2
//!    `TryStoreGlobal`).
//! 6. **Edge-keyed phis**: v0.2 phi entries key on `(Edge, value)` —
//!    a block that is both a Normal and an Exceptional predecessor
//!    produces two entries with the same value where v0.1 has one.
//!    Rule: v0.2's entries collapse by source block (values must
//!    agree) before comparison.
//! 7. **Deprecated→modern folds**: identical on both sides by
//!    construction (the lift ports v0.1's arms verbatim).
//! 8. **Sendable class definition (N53)**: v0.1 folds
//!    `callruntime.definesendableclass` into
//!    `InstData::DefineClassWithBuffer` — the known N53 opcode-identity
//!    collapse (the vendor runtime builds sendable classes through
//!    SlowRuntimeStub::CreateSharedClass, a different stub from the
//!    contemporary defineclasswithbuffer's CreateClassWithBuffer;
//!    interpreter_assembly.cpp:6157-6180 vs :6007/6033). v0.2 models
//!    the distinction with `Op::DefineSendableClass` and is
//!    SEMANTICALLY CORRECT where v0.1 is collapsed. Rule: v0.2's
//!    `DefineSendableClass` canonicalizes DOWN to the `DefineClass`
//!    token (v0.2 is strictly more precise than anything v0.1 can
//!    express; the operand roles — ctor, heritage, members, count —
//!    are identical, so the streams compare exactly).
//!
//! Any remaining difference is a FINDING, reported with fixture,
//! function, and stream position.

use std::collections::HashMap;

use abcd_file::{File, LiteralValue};
use abcd_ir::inst::{BinOp as V1BinOp, CallKind as V1CallKind, InstData, PropKind, UnOp as V1UnOp};
use abcd_ir::module::{Module as V1Module, ValueDef as V1ValueDef};
use abcd_ir2::{Const, Module as V2Module, Op, ValueDef};

/// One comparison finding.
// The locating fields are consumed by corpus_parity's diagnostic output;
// each test target compiles this shared module separately, so targets that
// only count mismatches would otherwise trip per-target dead_code.
#[derive(Clone, Debug)]
#[allow(dead_code)]
pub struct Mismatch {
    /// Function-table index.
    pub func: usize,
    /// Function display name (v0.1 side).
    pub func_name: String,
    /// Stream position of the first divergence.
    pub token: usize,
    /// v0.1 canonical line (or context).
    pub v1: String,
    /// v0.2 canonical line (or context).
    pub v2: String,
}

/// The comparison outcome for one module pair.
#[derive(Clone, Debug, Default)]
pub struct CompareReport {
    /// Functions compared (both sides).
    pub functions_compared: usize,
    /// Tokens compared (v0.1 side stream length, summed).
    pub tokens_compared: usize,
    /// Findings, in encounter order.
    pub mismatches: Vec<Mismatch>,
}

impl CompareReport {
    /// Whether the modules are canonically equal.
    pub fn is_parity(&self) -> bool {
        self.mismatches.is_empty()
    }
}

/// Compare the two lifted modules function-by-function (function tables
/// align by construction: both lifts iterate classes in file order and
/// methods in declaration order).
pub fn compare_modules(file: &File, v1: &V1Module, v2: &V2Module) -> CompareReport {
    let mut report = CompareReport::default();
    if v1.functions.len() != v2.functions.len() {
        report.mismatches.push(Mismatch {
            func: usize::MAX,
            func_name: "<module>".into(),
            token: 0,
            v1: format!("{} functions", v1.functions.len()),
            v2: format!("{} functions", v2.functions.len()),
        });
        return report;
    }
    for fi in 0..v1.functions.len() {
        let s1 = canon_func_v1(file, v1, fi);
        let s2 = canon_func_v2(v2, fi);
        report.functions_compared += 1;
        report.tokens_compared += s1.len();
        if s1 != s2 {
            let name = v1
                .functions
                .get(fi)
                .map(|f| v1.strings.get(f.name).to_owned())
                .unwrap_or_default();
            let token = s1
                .iter()
                .zip(s2.iter())
                .position(|(a, b)| a != b)
                .unwrap_or_else(|| s1.len().min(s2.len()));
            report.mismatches.push(Mismatch {
                func: fi,
                func_name: name,
                token,
                v1: context(&s1, token),
                v2: context(&s2, token),
            });
        }
    }
    report
}

/// Render a stream line with neighbors for context.
fn context(stream: &[String], token: usize) -> String {
    let lo = token.saturating_sub(1);
    let hi = (token + 2).min(stream.len());
    stream[lo..hi].join(" | ")
}

// ─── Canonical operand ───────────────────────────────────────────────────────

/// A canonical operand/value reference.
#[derive(Clone, Debug, PartialEq, Eq)]
enum CVal {
    /// `p{i}` — function parameter i.
    Param(u16),
    /// `exc{b}` — handler exception param of block b.
    Exc(usize),
    /// `c:<content>` — a constant by value.
    Konst(String),
    /// `t{k}` — the result of stream token k.
    Tok(usize),
}

impl std::fmt::Display for CVal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CVal::Param(i) => write!(f, "p{i}"),
            CVal::Exc(b) => write!(f, "exc{b}"),
            CVal::Konst(c) => write!(f, "c:{c}"),
            CVal::Tok(k) => write!(f, "t{k}"),
        }
    }
}

// ─── Constant content canonicalization ───────────────────────────────────────

/// Canonical content of a v0.2 constant.
fn canon_const_v2(m: &V2Module, c: &Const) -> String {
    match c {
        Const::Undefined => "undefined".into(),
        Const::Hole => "hole".into(),
        Const::Null => "null".into(),
        Const::Bool(b) => format!("bool:{b}"),
        Const::Number(bits) => format!("num:{bits:#x}"),
        Const::String(s) => format!("str:{}", m.sym.resolve(*s).unwrap_or("?")),
        Const::BigInt(s) => format!("bigint:{}", m.sym.resolve(*s).unwrap_or("?")),
        Const::ArrayLiteral(items) => {
            let inner: Vec<String> = items.iter().map(|c| canon_const_v2(m, c)).collect();
            format!("arr:[{}]", inner.join(","))
        }
        Const::ObjectLiteral { keys, values } => {
            let k: Vec<String> = keys.iter().map(|c| canon_const_v2(m, c)).collect();
            let v: Vec<String> = values.iter().map(|c| canon_const_v2(m, c)).collect();
            format!("obj:{{{}}}/{{{}}}", k.join(","), v.join(","))
        }
        Const::MethodRef(fid) => format!("method:{}", fid.index()),
    }
}

/// Canonical content of a v0.1 file literal value (literal-array
/// element), with nested arrays resolved like the lift resolves them.
fn canon_literal_value(file: &File, v: &LiteralValue, depth: usize) -> String {
    if depth > 32 {
        return "cycle".into();
    }
    match v {
        LiteralValue::Bool(b) => format!("bool:{b}"),
        LiteralValue::Integer8(n) => format!("num:{:#x}", (*n as f64).to_bits()),
        LiteralValue::Integer(n) => format!("num:{:#x}", (*n as f64).to_bits()),
        LiteralValue::Float(x) => format!("num:{:#x}", (*x as f64).to_bits()),
        LiteralValue::Double(x) => format!("num:{:#x}", x.to_bits()),
        LiteralValue::String(sid) | LiteralValue::EtsImplements(sid) => {
            format!("str:{}", file.strings.resolve(*sid).unwrap_or("?"))
        }
        LiteralValue::Method(off)
        | LiteralValue::GeneratorMethod(off)
        | LiteralValue::AsyncGeneratorMethod(off)
        | LiteralValue::Getter(off)
        | LiteralValue::Setter(off) => format!("method:{}", method_index(file, *off)),
        LiteralValue::Accessor(n) => format!("num:{:#x}", (*n as f64).to_bits()),
        LiteralValue::MethodAffiliate(n) => format!("num:{:#x}", (*n as f64).to_bits()),
        LiteralValue::BuiltinTypeIndex(n) => format!("num:{:#x}", (*n as f64).to_bits()),
        LiteralValue::NullValue(_) => "null".into(),
        LiteralValue::LiteralArray(idx) => canon_literal_array_at(file, idx.0, depth + 1),
        LiteralValue::LiteralBufferIndex(raw) => {
            let idx = resolve_offset_index(file, raw.0);
            canon_literal_array_at(file, idx, depth + 1)
        }
        LiteralValue::ArrayU1(raw)
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
            let idx = resolve_offset_index(file, raw.0);
            canon_literal_array_at(file, idx, depth + 1)
        }
    }
}

/// Resolve a raw-offset literal reference to a table index (the lift's
/// N52 rule); unresolvable references render as `usize::MAX` (the
/// registered-pending sendable class — the two sides agree on it).
fn resolve_offset_index(file: &File, raw: u32) -> u32 {
    if let Some(&idx) = file.literal_array_offsets.get(&raw) {
        return idx;
    }
    if (raw as usize) < file.literal_arrays.len() {
        return raw;
    }
    u32::MAX
}

/// Canonical content of the file literal array at `idx`.
fn canon_literal_array_at(file: &File, idx: u32, depth: usize) -> String {
    let Some(la) = file.literal_arrays.get(idx as usize) else {
        // Unregistered nested reference (the registered-pending
        // sendable class) — both sides render it identically.
        return "arr:unregistered".into();
    };
    let inner: Vec<String> = la
        .values
        .iter()
        .map(|v| canon_literal_value(file, v, depth))
        .collect();
    format!("arr:[{}]", inner.join(","))
}

/// The method's index in `file.all_methods()` order (the v0.2
/// function-table reservation order); `u32::MAX` when unknown.
fn method_index(file: &File, offset: u32) -> u32 {
    file.all_methods()
        .position(|(_, m)| m.offset == offset)
        .map(|i| i as u32)
        .unwrap_or(u32::MAX)
}

// ─── v0.1 canonicalization ───────────────────────────────────────────────────

struct V1Cx<'a> {
    file: &'a File,
    m: &'a V1Module,
    /// v0.1 value → canonical reference.
    vals: HashMap<abcd_ir::entity::Value, CVal>,
    /// Block → its position in the function's block list (block
    /// identity for rendering — arena layouts need not match).
    bpos: HashMap<abcd_ir::entity::Block, usize>,
    stream: Vec<String>,
    is_static: bool,
    has_params: bool,
}

impl<'a> V1Cx<'a> {
    fn push(&mut self, name: &str, operands: &[CVal]) -> usize {
        let ops: Vec<String> = operands.iter().map(ToString::to_string).collect();
        let k = self.stream.len();
        self.stream.push(format!("{name}({})", ops.join(",")));
        k
    }

    /// Register an instruction's result value as the given canonical
    /// reference.
    fn bind(&mut self, val: abcd_ir::entity::Value, cv: CVal) {
        self.vals.insert(val, cv);
    }

    fn val(&self, v: abcd_ir::entity::Value) -> CVal {
        if let Some(cv) = self.vals.get(&v) {
            return cv.clone();
        }
        match self.m.value(v).def {
            V1ValueDef::FuncParam(i) => CVal::Param(i),
            V1ValueDef::ExceptionParam => CVal::Exc(usize::MAX),
            V1ValueDef::Inst(_) => CVal::Konst("dangling".into()),
        }
    }

    fn name(&self, sid: abcd_ir::entity::StringId) -> CVal {
        CVal::Konst(format!("str:{}", self.m.strings.get(sid)))
    }

    fn block(&self, b: abcd_ir::entity::Block) -> CVal {
        CVal::Konst(format!("block:{}", self.bpos[&b]))
    }

    /// The canonical reference for a value produced by a frame-initial
    /// instruction; `Some` when the instruction emits NO token
    /// (divergence rule 1).
    fn alias_of(&self, inst: &abcd_ir::module::InstNode) -> Option<CVal> {
        match &inst.data {
            // Rule 1: loc-less entry literals are v0.1's frame-initial
            // seeding; real literal bytecodes carry a loc.
            InstData::LiteralUndefined if inst.loc.is_none() => {
                Some(CVal::Konst("undefined".into()))
            }
            InstData::LiteralHole if inst.loc.is_none() => Some(CVal::Konst("hole".into())),
            _ => None,
        }
    }
}

/// Canonical stream of one v0.1 function.
fn canon_func_v1(file: &File, m: &V1Module, fi: usize) -> Vec<String> {
    let func = &m.functions[fi];
    let mut cx = V1Cx {
        file,
        m,
        vals: HashMap::new(),
        bpos: func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, &b)| (b, i))
            .collect(),
        stream: Vec::new(),
        is_static: func.access_flags.contains(abcd_file::AccessFlags::STATIC),
        has_params: !func.param_values.is_empty(),
    };
    // Params are canonical by index.
    for (i, &p) in func.param_values.iter().enumerate() {
        cx.bind(p, CVal::Param(i as u16));
    }
    for &(handler, val) in &func.exception_values {
        let pos = cx.bpos.get(&handler).copied().unwrap_or(usize::MAX);
        cx.bind(val, CVal::Exc(pos));
    }
    for &bb in &func.blocks {
        cx.stream.push(format!("── block {}", cx.bpos[&bb]));
        let block = m.block(bb);
        for &iid in block.phis.iter().chain(block.insts.iter()) {
            canon_inst_v1(&mut cx, iid);
        }
    }
    cx.stream
}

/// Map one v0.1 instruction to canonical tokens (the mapping table).
#[allow(clippy::too_many_lines)]
fn canon_inst_v1(cx: &mut V1Cx, iid: abcd_ir::entity::Inst) {
    let inst = cx.m.inst(iid);
    let data = inst.data.clone();
    let result = inst.result;

    macro_rules! tok {
        ($name:expr $(, $op:expr)* $(,)?) => {{
            cx.push($name, &[$($op),*])
        }};
    }
    macro_rules! bind_last {
        ($k:expr) => {
            if let Some(r) = result {
                cx.bind(r, CVal::Tok($k));
            }
        };
    }
    macro_rules! one {
        ($name:expr $(, $op:expr)* $(,)?) => {{
            let k = tok!($name $(, $op)*);
            bind_last!(k);
        }};
    }
    macro_rules! one_slice {
        ($name:expr, $ops:expr) => {{
            let k = cx.push($name, &$ops);
            bind_last!(k);
        }};
    }

    // Divergence rules 1–2: aliased/materialized instructions.
    if let InstData::LoadThis = &data {
        // Rule 2: ldthis aliases params[0] for non-static kinds (zero
        // tokens); v0.2 materializes `LoadConst(undefined)` for
        // static/zero-param frames (one token — mirror it).
        if !cx.is_static && cx.has_params {
            if let Some(r) = result {
                cx.bind(r, CVal::Param(0));
            }
        } else {
            one!("LoadConst", CVal::Konst("undefined".into()));
        }
        return;
    }
    if let Some(alias) = cx.alias_of(inst) {
        if let Some(r) = result {
            cx.bind(r, alias);
        }
        return;
    }

    match &data {
        // ── Literals → LoadConst ──
        InstData::LiteralUndefined => one!("LoadConst", CVal::Konst("undefined".into())),
        InstData::LiteralNull => one!("LoadConst", CVal::Konst("null".into())),
        InstData::LiteralBool(b) => one!("LoadConst", CVal::Konst(format!("bool:{b}"))),
        InstData::LiteralNumber(x) => {
            one!("LoadConst", CVal::Konst(format!("num:{:#x}", x.to_bits())))
        }
        InstData::LiteralNaN => one!(
            "LoadConst",
            CVal::Konst(format!("num:{:#x}", f64::NAN.to_bits()))
        ),
        InstData::LiteralInfinity => {
            one!(
                "LoadConst",
                CVal::Konst(format!("num:{:#x}", f64::INFINITY.to_bits()))
            )
        }
        InstData::LiteralHole => one!("LoadConst", CVal::Konst("hole".into())),
        InstData::LiteralString(s) => one!("LoadConst", cx.name(*s)),
        InstData::LiteralBigInt(s) => {
            one!(
                "LoadConst",
                CVal::Konst(format!("bigint:{}", cx.m.strings.get(*s)))
            )
        }

        // ── Compute ──
        InstData::BinaryOp { op, left, right } => {
            let (name, opname) = canon_binop(*op);
            one!(
                name,
                CVal::Konst(opname.into()),
                cx.val(*left),
                cx.val(*right)
            )
        }
        InstData::UnaryOp { op, operand } => {
            let opname = canon_unop(*op);
            one!("UnaryOp", CVal::Konst(opname.into()), cx.val(*operand))
        }
        InstData::IsTrue { operand } => {
            one!("UnaryOp", CVal::Konst("IsTrue".into()), cx.val(*operand))
        }
        InstData::IsFalse { operand } => {
            one!("UnaryOp", CVal::Konst("IsFalse".into()), cx.val(*operand))
        }

        // ── Object creation ──
        InstData::CreateEmptyObject => {
            one!("AllocObject", CVal::Konst("obj:{}/{}".into()))
        }
        InstData::CreateEmptyArray => one!("AllocArray"),
        InstData::CreateObjectWithBuffer { literal_array } => {
            one!(
                "AllocObject",
                CVal::Konst(canon_literal_array_at(cx.file, *literal_array, 0))
            )
        }
        InstData::CreateArrayWithBuffer { literal_array } => {
            // N59: the object/array tag is opcode-carried on both
            // sides — compares EXACTLY (no fold to "AllocObject").
            one!(
                "AllocArray",
                CVal::Konst(canon_literal_array_at(cx.file, *literal_array, 0))
            )
        }
        InstData::CreateRegExp { pattern, flags } => {
            let flag_str = cx.m.strings.get(*flags);
            one!(
                "AllocRegExp",
                cx.name(*pattern),
                CVal::Konst(format!("flags:{}", flag_str))
            )
        }
        InstData::CreateObjectWithExcludedKeys { obj, keys } => {
            let mut ops = vec![cx.val(*obj)];
            ops.extend(keys.iter().map(|&k| cx.val(k)));
            one_slice!("CreateObjectWithExcludedKeys", ops)
        }
        InstData::SetObjectWithProto { proto, obj } => {
            let _ = tok!("SetObjectWithProto", cx.val(*proto), cx.val(*obj));
            debug_assert!(result.is_none());
        }

        // ── Property access ──
        InstData::LoadProperty { object, key } => match key {
            PropKind::ByName(n) => one!("LoadProp", cx.val(*object), cx.name(*n)),
            PropKind::ByValue(k) => one!("LoadPropDyn", cx.val(*object), cx.val(*k)),
            PropKind::ByIndex(i) => {
                let k0 = tok!(
                    "LoadConst",
                    CVal::Konst(format!("num:{:#x}", (*i as f64).to_bits()))
                );
                one!("LoadPropIdx", cx.val(*object), CVal::Tok(k0))
            }
        },
        InstData::StoreProperty { object, key, value } => {
            match key {
                PropKind::ByName(n) => {
                    let _ = tok!("StoreProp", cx.val(*object), cx.name(*n), cx.val(*value));
                }
                PropKind::ByValue(k) => {
                    let _ = tok!("StorePropDyn", cx.val(*object), cx.val(*k), cx.val(*value));
                }
                PropKind::ByIndex(i) => {
                    let k0 = tok!(
                        "LoadConst",
                        CVal::Konst(format!("num:{:#x}", (*i as f64).to_bits()))
                    );
                    let _ = tok!(
                        "StorePropIdx",
                        cx.val(*object),
                        CVal::Tok(k0),
                        cx.val(*value)
                    );
                }
            }
            debug_assert!(result.is_none());
        }
        InstData::StoreOwnProperty { object, key, value } => {
            // N60: the own-store family is IR-explicit on both sides —
            // compares EXACTLY (no fold to the plain StoreProp* tokens).
            match key {
                PropKind::ByName(n) => {
                    let _ = tok!(
                        "StoreOwnPropName",
                        cx.val(*object),
                        cx.name(*n),
                        cx.val(*value)
                    );
                }
                PropKind::ByValue(k) => {
                    let _ = tok!(
                        "StoreOwnPropDyn",
                        cx.val(*object),
                        cx.val(*k),
                        cx.val(*value)
                    );
                }
                PropKind::ByIndex(i) => {
                    let k0 = tok!(
                        "LoadConst",
                        CVal::Konst(format!("num:{:#x}", (*i as f64).to_bits()))
                    );
                    let _ = tok!(
                        "StoreOwnPropIdx",
                        cx.val(*object),
                        CVal::Tok(k0),
                        cx.val(*value)
                    );
                }
            }
            debug_assert!(result.is_none());
        }
        InstData::DeleteProperty { object, key } => {
            one!("DeleteProp", cx.val(*object), cx.val(*key))
        }
        InstData::LoadSuperProperty { key } => match key {
            PropKind::ByName(n) => one!("LoadSuper", cx.name(*n)),
            PropKind::ByValue(k) => one!("LoadSuper", cx.val(*k)),
            PropKind::ByIndex(_) => {
                one!(
                    "LoadSuper",
                    CVal::Konst("UNSUPPORTED-SUPER-BY-INDEX".into())
                )
            }
        },
        InstData::StoreSuperProperty { key, value } => {
            let key_ops = match key {
                PropKind::ByName(n) => vec![cx.name(*n)],
                PropKind::ByValue(k) => vec![cx.val(*k)],
                PropKind::ByIndex(_) => vec![CVal::Konst("UNSUPPORTED-SUPER-BY-INDEX".into())],
            };
            let mut ops = key_ops;
            ops.push(cx.val(*value));
            let _ = cx.push("StoreSuper", &ops);
            debug_assert!(result.is_none());
        }
        InstData::CopyDataProperties { dst, src } => {
            let _ = tok!("CopyDataProps", cx.val(*dst), cx.val(*src));
            debug_assert!(result.is_none());
        }
        InstData::ArraySpread { dst, index, src } => {
            one!("ArraySpread", cx.val(*dst), cx.val(*index), cx.val(*src))
        }

        // ── Private properties ──
        InstData::LoadPrivateProperty { level, slot, obj } => one!(
            "LoadPrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj)
        ),
        InstData::StorePrivateProperty {
            level,
            slot,
            obj,
            value,
        } => {
            let _ = tok!(
                "StorePrivate",
                CVal::Konst(format!("level:{level}")),
                CVal::Konst(format!("slot:{slot}")),
                cx.val(*obj),
                cx.val(*value)
            );
        }
        InstData::DefinePrivateProperty {
            level,
            slot,
            obj,
            value,
        } => {
            let _ = tok!(
                "DefinePrivate",
                CVal::Konst(format!("level:{level}")),
                CVal::Konst(format!("slot:{slot}")),
                cx.val(*obj),
                cx.val(*value)
            );
        }
        InstData::TestPrivateProperty { level, slot, obj } => one!(
            "TestPrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj)
        ),
        InstData::CreatePrivateProperty {
            count,
            literal_array,
        } => {
            let _ = tok!(
                "CreatePrivateNames",
                CVal::Konst(format!("count:{count}")),
                CVal::Konst(canon_literal_array_at(cx.file, *literal_array, 0))
            );
        }

        // ── Globals ──
        InstData::LoadGlobalVar { name } => {
            one!(
                "TryGetGlobal",
                cx.name(*name),
                CVal::Konst("default:none".into())
            )
        }
        InstData::TryLoadGlobalByName { name } => {
            let k0 = tok!("LoadConst", CVal::Konst("undefined".into()));
            one!("TryGetGlobal", cx.name(*name), CVal::Tok(k0))
        }
        InstData::StoreGlobalVar { name, value } => {
            let _ = tok!("StoreGlobal", cx.name(*name), cx.val(*value));
        }
        InstData::TryStoreGlobalByName { name, value } => {
            // N61: the tolerant-store distinction is IR-explicit on
            // both sides — compares EXACTLY (no fold to "StoreGlobal").
            let _ = tok!("TryStoreGlobal", cx.name(*name), cx.val(*value));
        }

        // ── Lexical ──
        InstData::LoadLexVar { level, slot } => one!(
            "GetLexVar",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}"))
        ),
        InstData::StoreLexVar { level, slot, value } => {
            let _ = tok!(
                "PutLexVar",
                CVal::Konst(format!("level:{level}")),
                CVal::Konst(format!("slot:{slot}")),
                cx.val(*value)
            );
        }
        InstData::NewLexEnv { num_vars } => {
            one!("NewLexEnv", CVal::Konst(format!("num:{num_vars}")))
        }
        InstData::NewLexEnvWithName {
            num_vars,
            scope_literal_array,
        } => one!(
            "NewLexEnvWithName",
            CVal::Konst(format!("num:{num_vars}")),
            CVal::Konst(canon_literal_array_at(cx.file, *scope_literal_array, 0))
        ),
        InstData::PopLexEnv => {
            let _ = tok!("PopLexEnv");
        }

        // ── Module vars ──
        InstData::LoadLocalModuleVar { index } | InstData::LoadExternalModuleVar { index } => {
            one!("LoadModuleVar", CVal::Konst(format!("index:{index}")))
        }
        InstData::StoreModuleVar { index, value } => {
            let _ = tok!(
                "StoreModuleVar",
                CVal::Konst(format!("index:{index}")),
                cx.val(*value)
            );
        }
        InstData::GetModuleNamespace { index } => {
            one!("GetModuleNamespace", CVal::Konst(format!("index:{index}")))
        }
        InstData::DynamicImport { specifier } => {
            one!("DynamicImport", cx.val(*specifier))
        }

        // ── Function / class definition ──
        InstData::DefineFunc {
            method_offset,
            length,
            ..
        } => {
            let k0 = tok!(
                "DefineFunc",
                CVal::Konst(format!("method:{}", method_index(cx.file, *method_offset))),
                CVal::Konst("caps:[]".into()),
                CVal::Konst(format!("len:{length}"))
            );
            let k1 = tok!("AllocClosure", CVal::Tok(k0));
            bind_last!(k1);
        }
        InstData::DefineMethod {
            method_id,
            method_offset,
            length,
            home_object,
        } => {
            let k0 = tok!(
                "DefineFunc",
                CVal::Konst(format!("method:{}", method_index(cx.file, *method_offset))),
                CVal::Konst("caps:[]".into()),
                CVal::Konst(format!("len:{length}"))
            );
            let k1 = tok!("AllocClosure", CVal::Tok(k0));
            let k2 = tok!(
                "DefineMethod",
                cx.val(*home_object),
                cx.name(*method_id),
                CVal::Tok(k1),
                CVal::Konst(format!("len:{length}"))
            );
            bind_last!(k2);
        }
        InstData::DefineClassWithBuffer {
            method_offset,
            literal_array,
            count,
            base,
            ..
        } => one!(
            "DefineClass",
            CVal::Konst(format!("method:{}", method_index(cx.file, *method_offset))),
            cx.val(*base),
            CVal::Konst(canon_literal_array_at(cx.file, *literal_array, 0)),
            CVal::Konst(format!("count:{count}"))
        ),
        InstData::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => one!(
            "DefineGetterSetterByValue",
            cx.val(*obj),
            cx.val(*key),
            cx.val(*getter),
            cx.val(*setter)
        ),

        // ── Calls ──
        InstData::Call { kind, callee, args } => {
            let mut ops = Vec::new();
            let kind_name = match kind {
                V1CallKind::Call => {
                    ops.push(cx.val(*callee));
                    ops.push(CVal::Konst("this:none".into()));
                    ops.extend(args.iter().map(|&a| cx.val(a)));
                    "dynamic"
                }
                V1CallKind::CallThis => {
                    ops.push(cx.val(*callee));
                    match args.split_first() {
                        Some((&this, rest)) => {
                            ops.push(cx.val(this));
                            ops.extend(rest.iter().map(|&a| cx.val(a)));
                        }
                        None => ops.push(CVal::Konst("this:none".into())),
                    }
                    "dynamic"
                }
                V1CallKind::SuperCall | V1CallKind::SuperCallArrow => {
                    ops.push(cx.val(*callee));
                    ops.push(CVal::Konst("this:none".into()));
                    ops.extend(args.iter().map(|&a| cx.val(a)));
                    "super"
                }
                V1CallKind::SuperCallSpread => {
                    ops.push(cx.val(*callee));
                    ops.push(CVal::Konst("this:none".into()));
                    ops.extend(args.iter().map(|&a| cx.val(a)));
                    // N58: the super-spread distinction is IR-explicit
                    // on both sides — compares EXACTLY (no fold to
                    // "super").
                    "superspread"
                }
                V1CallKind::Apply => {
                    ops.push(cx.val(*callee));
                    match args.as_slice() {
                        [this, array, ..] => {
                            ops.push(cx.val(*this));
                            ops.push(cx.val(*array));
                        }
                        _ => ops.push(CVal::Konst("this:none".into())),
                    }
                    // N57: the apply distinction is IR-explicit on both
                    // sides — compares EXACTLY (no fold to "dynamic").
                    "apply"
                }
                V1CallKind::NewObjApply => {
                    // v0.2 normalizes: callee = the ctor (args[0] in
                    // v0.1), args = [the acc-carried array].
                    match args.as_slice() {
                        [ctor, ..] => {
                            ops.push(cx.val(*ctor));
                            ops.push(CVal::Konst("this:none".into()));
                            ops.push(cx.val(*callee));
                        }
                        _ => {
                            ops.push(cx.val(*callee));
                            ops.push(CVal::Konst("this:none".into()));
                        }
                    }
                    "new"
                }
                V1CallKind::Construct => {
                    ops.push(cx.val(*callee));
                    ops.push(CVal::Konst("this:none".into()));
                    ops.extend(args.iter().map(|&a| cx.val(a)));
                    "new"
                }
            };
            ops.push(CVal::Konst(format!("kind:{kind_name}")));
            one_slice!("Call", ops)
        }

        // ── Special loaders ──
        InstData::LoadNewTarget => one!("LoadNewTarget"),
        InstData::LoadGlobalObject => one!("LoadGlobalObject"),
        InstData::LoadFunction => one!("LoadFunction"),
        InstData::GetUnmappedArgs => one!("GetUnmappedArgs"),
        InstData::CopyRestArgs { start_index } => {
            one!("CopyRestArgs", CVal::Konst(format!("start:{start_index}")))
        }

        // ── Iterators ──
        InstData::GetIterator { obj } => one!("GetIterator", cx.val(*obj)),
        InstData::GetAsyncIterator { obj } => one!("GetAsyncIterator", cx.val(*obj)),
        InstData::GetPropIterator { obj } => one!("GetPropIterator", cx.val(*obj)),
        InstData::GetNextPropName { iterator } => one!("NextPropName", cx.val(*iterator)),
        InstData::CloseIterator { iterator } => one!("IteratorReturn", cx.val(*iterator)),

        // ── Generator / async ──
        InstData::CreateGeneratorObj { func } => one!("CreateGenerator", cx.val(*func)),
        InstData::SuspendGenerator { genobj, value } => {
            one!("SuspendGenerator", cx.val(*genobj), cx.val(*value))
        }
        InstData::ResumeGenerator { genobj } => one!("ResumeGenerator", cx.val(*genobj)),
        InstData::GetResumeMode { genobj } => one!("GetResumeMode", cx.val(*genobj)),
        InstData::AsyncFunctionEnter => one!("AsyncFunctionEnter"),
        InstData::AsyncFunctionAwaitUncaught { value } => one!("AwaitUncaught", cx.val(*value)),
        InstData::AsyncFunctionResolve { value } => one!("AsyncResolve", cx.val(*value)),
        InstData::AsyncFunctionReject { value } => one!("AsyncReject", cx.val(*value)),
        InstData::CreateIterResultObj { value, done } => {
            one!("CreateIterResultObj", cx.val(*value), cx.val(*done))
        }
        InstData::GetTemplateObject { literal } => one!("GetTemplateObject", cx.val(*literal)),

        // ── Exceptions ──
        InstData::Throw { value } => {
            let _ = tok!("Throw", cx.val(*value));
        }
        InstData::ThrowNotExists => {
            let _ = tok!("ThrowNotExists");
        }
        InstData::ThrowPatternNonCoercible => {
            let _ = tok!("ThrowPatternNonCoercible");
        }
        InstData::ThrowDeleteSuperProperty => {
            let _ = tok!("ThrowDeleteSuperProperty");
        }
        InstData::ThrowConstAssignment { name } => {
            let _ = tok!("ThrowConstAssignment", cx.val(*name));
        }
        InstData::ThrowIfNotObject { value } => {
            let _ = tok!("ThrowIfNotObject", cx.val(*value));
        }
        InstData::ThrowUndefinedIfHole { name, value } => {
            let _ = tok!("ThrowUndefinedIfHole", cx.val(*name), cx.val(*value));
        }
        InstData::ThrowUndefinedIfHoleWithName { name, value } => {
            let _ = tok!(
                "ThrowUndefinedIfHoleWithName",
                cx.name(*name),
                cx.val(*value)
            );
        }
        InstData::ThrowIfSuperNotCorrectCall { value, kind } => {
            let _ = tok!(
                "ThrowIfSuperNotCalled",
                cx.val(*value),
                CVal::Konst(format!("supercheck:{kind}"))
            );
        }

        // ── Phi / control ──
        InstData::Phi { entries } => {
            let mut ops = Vec::new();
            for (pred, val) in entries {
                ops.push(cx.block(*pred));
                ops.push(cx.val(*val));
            }
            one_slice!("Phi", ops)
        }
        InstData::Branch { dest } => {
            let _ = tok!("Branch", cx.block(*dest));
        }
        InstData::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            let _ = tok!(
                "CondBranch",
                cx.val(*cond),
                cx.block(*true_dest),
                cx.block(*false_dest)
            );
        }
        InstData::Return { value } => {
            let ops: Vec<CVal> = value.iter().map(|&v| cx.val(v)).collect();
            let _ = cx.push("Return", &ops);
        }
        InstData::Unreachable => {
            let _ = tok!("Unreachable");
        }
        InstData::Debugger => {
            let _ = tok!("Debugger");
        }
        // Handled above (divergence rule 2).
        InstData::LoadThis => unreachable!("LoadThis handled before the match"),
    }
}

/// The v0.1 BinOp splits into v0.2's BinaryOp/Compare.
fn canon_binop(op: V1BinOp) -> (&'static str, &'static str) {
    use V1BinOp::*;
    match op {
        Add => ("BinaryOp", "Add"),
        Sub => ("BinaryOp", "Sub"),
        Mul => ("BinaryOp", "Mul"),
        Div => ("BinaryOp", "Div"),
        Mod => ("BinaryOp", "Mod"),
        Exp => ("BinaryOp", "Exp"),
        Shl => ("BinaryOp", "Shl"),
        Shr => ("BinaryOp", "Shr"),
        Ashr => ("BinaryOp", "Ashr"),
        BitAnd => ("BinaryOp", "BitAnd"),
        BitOr => ("BinaryOp", "BitOr"),
        BitXor => ("BinaryOp", "BitXor"),
        Eq => ("Compare", "Eq"),
        NotEq => ("Compare", "NotEq"),
        StrictEq => ("Compare", "StrictEq"),
        StrictNotEq => ("Compare", "StrictNotEq"),
        Less => ("Compare", "Less"),
        LessEq => ("Compare", "LessEq"),
        Greater => ("Compare", "Greater"),
        GreaterEq => ("Compare", "GreaterEq"),
        In => ("Compare", "In"),
        InstanceOf => ("Compare", "InstanceOf"),
    }
}

fn canon_unop(op: V1UnOp) -> &'static str {
    use V1UnOp::*;
    match op {
        Minus => "Minus",
        BitNot => "BitNot",
        LogicalNot => "LogicalNot",
        Inc => "Inc",
        Dec => "Dec",
        TypeOf => "TypeOf",
        ToNumber => "ToNumber",
        ToNumeric => "ToNumeric",
        Void => "Void",
    }
}

// ─── v0.2 canonicalization ───────────────────────────────────────────────────

struct V2Cx<'a> {
    m: &'a V2Module,
    /// Defining inst → its stream token.
    inst_tok: HashMap<abcd_ir2::InstId, usize>,
    /// Block → its position in the function's block list.
    bpos: HashMap<abcd_ir2::BlockId, usize>,
    stream: Vec<String>,
}

impl<'a> V2Cx<'a> {
    fn val(&self, v: abcd_ir2::ValueId) -> CVal {
        match self.m.values[v.index()].def {
            ValueDef::Param(i) => CVal::Param(i),
            ValueDef::ExceptionParam(b) => {
                CVal::Exc(self.bpos.get(&b).copied().unwrap_or(usize::MAX))
            }
            ValueDef::Const(c) => CVal::Konst(canon_const_v2(
                self.m,
                self.m.consts.get(c).expect("pooled const"),
            )),
            ValueDef::Inst(def) => match self.inst_tok.get(&def) {
                Some(&k) => CVal::Tok(k),
                None => CVal::Konst("dangling".into()),
            },
        }
    }

    fn name(&self, s: abcd_ir2::Sym) -> CVal {
        CVal::Konst(format!("str:{}", self.m.sym.resolve(s).unwrap_or("?")))
    }

    fn konst(&self, c: abcd_ir2::ConstId) -> CVal {
        CVal::Konst(canon_const_v2(
            self.m,
            self.m.consts.get(c).expect("pooled const"),
        ))
    }

    fn block(&self, b: abcd_ir2::BlockId) -> CVal {
        CVal::Konst(format!("block:{}", self.bpos[&b]))
    }

    fn push(&mut self, iid: abcd_ir2::InstId, name: &str, operands: &[CVal]) {
        let k = self.stream.len();
        self.inst_tok.insert(iid, k);
        let ops: Vec<String> = operands.iter().map(ToString::to_string).collect();
        self.stream.push(format!("{name}({})", ops.join(",")));
    }
}

/// Canonical stream of one v0.2 function.
fn canon_func_v2(m: &V2Module, fi: usize) -> Vec<String> {
    let func = &m.functions[fi];
    let mut cx = V2Cx {
        m,
        inst_tok: HashMap::new(),
        bpos: func
            .blocks
            .iter()
            .enumerate()
            .map(|(i, &b)| (b, i))
            .collect(),
        stream: Vec::new(),
    };
    for &bb in &func.blocks {
        cx.stream.push(format!("── block {}", cx.bpos[&bb]));
        let insts = m.blocks[bb.index()].insts.clone();
        for iid in insts {
            canon_inst_v2(&mut cx, iid);
        }
    }
    cx.stream
}

/// Map one v0.2 instruction to its canonical token.
#[allow(clippy::too_many_lines)]
fn canon_inst_v2(cx: &mut V2Cx, iid: abcd_ir2::InstId) {
    let op = cx.m.insts[iid.index()].op.clone();
    macro_rules! tok {
        ($name:expr $(, $op:expr)* $(,)?) => {{
            cx.push(iid, $name, &[$($op),*])
        }};
    }
    match &op {
        Op::BinaryOp { op, left, right } => tok!(
            "BinaryOp",
            CVal::Konst(format!("{op:?}")),
            cx.val(*left),
            cx.val(*right)
        ),
        Op::UnaryOp { op, operand } => {
            tok!("UnaryOp", CVal::Konst(format!("{op:?}")), cx.val(*operand))
        }
        Op::Compare { op, left, right } => tok!(
            "Compare",
            CVal::Konst(format!("{op:?}")),
            cx.val(*left),
            cx.val(*right)
        ),
        Op::Mov { src } => tok!("Mov", cx.val(*src)),
        Op::LoadConst(c) => tok!("LoadConst", cx.konst(*c)),
        Op::AllocObject { shape } => tok!("AllocObject", cx.konst(*shape)),
        Op::AllocArray { shape } => match shape {
            Some(s) => tok!("AllocArray", cx.konst(*s)),
            None => tok!("AllocArray"),
        },
        Op::AllocRegExp { pattern, flags } => {
            tok!(
                "AllocRegExp",
                cx.name(*pattern),
                CVal::Konst(format!("flags:{flags}"))
            )
        }
        Op::AllocClosure { func } => tok!("AllocClosure", cx.val(*func)),
        Op::LoadProp { object, name } => tok!("LoadProp", cx.val(*object), cx.name(*name)),
        Op::StoreProp {
            object,
            name,
            value,
        } => tok!("StoreProp", cx.val(*object), cx.name(*name), cx.val(*value)),
        Op::LoadPropIdx { object, index } => {
            tok!("LoadPropIdx", cx.val(*object), cx.val(*index))
        }
        Op::StorePropIdx {
            object,
            index,
            value,
        } => tok!(
            "StorePropIdx",
            cx.val(*object),
            cx.val(*index),
            cx.val(*value)
        ),
        Op::LoadPropDyn { object, key } => tok!("LoadPropDyn", cx.val(*object), cx.val(*key)),
        Op::StorePropDyn { object, key, value } => tok!(
            "StorePropDyn",
            cx.val(*object),
            cx.val(*key),
            cx.val(*value)
        ),
        Op::StoreOwnPropName {
            object,
            name,
            value,
        } => tok!(
            "StoreOwnPropName",
            cx.val(*object),
            cx.name(*name),
            cx.val(*value)
        ),
        Op::StoreOwnPropDyn { object, key, value } => tok!(
            "StoreOwnPropDyn",
            cx.val(*object),
            cx.val(*key),
            cx.val(*value)
        ),
        Op::StoreOwnPropIdx {
            object,
            index,
            value,
        } => tok!(
            "StoreOwnPropIdx",
            cx.val(*object),
            cx.val(*index),
            cx.val(*value)
        ),
        Op::DefineMethod {
            object,
            name,
            func,
            length,
        } => tok!(
            "DefineMethod",
            cx.val(*object),
            cx.name(*name),
            cx.val(*func),
            CVal::Konst(format!("len:{length}"))
        ),
        Op::DeleteProp { object, key } => tok!("DeleteProp", cx.val(*object), cx.val(*key)),
        Op::TestProp { object, key } => {
            let key_cv = match key {
                abcd_ir2::PropKey::Name(n) => cx.name(*n),
                abcd_ir2::PropKey::Index(v) | abcd_ir2::PropKey::Dynamic(v) => cx.val(*v),
            };
            tok!("TestProp", cx.val(*object), key_cv)
        }
        Op::CopyDataProps { dst, src } => tok!("CopyDataProps", cx.val(*dst), cx.val(*src)),
        Op::SetObjectWithProto { proto, obj } => {
            tok!("SetObjectWithProto", cx.val(*proto), cx.val(*obj))
        }
        Op::ArraySpread { dst, index, src } => {
            tok!("ArraySpread", cx.val(*dst), cx.val(*index), cx.val(*src))
        }
        Op::CreateObjectWithExcludedKeys { obj, keys } => {
            let mut ops = vec![cx.val(*obj)];
            ops.extend(keys.iter().map(|&k| cx.val(k)));
            cx.push(iid, "CreateObjectWithExcludedKeys", &ops)
        }
        Op::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => tok!(
            "DefineGetterSetterByValue",
            cx.val(*obj),
            cx.val(*key),
            cx.val(*getter),
            cx.val(*setter)
        ),
        Op::GetTemplateObject { literal } => tok!("GetTemplateObject", cx.val(*literal)),
        Op::CreateIterResultObj { value, done } => {
            tok!("CreateIterResultObj", cx.val(*value), cx.val(*done))
        }
        Op::GetIterator { obj } => tok!("GetIterator", cx.val(*obj)),
        Op::GetAsyncIterator { obj } => tok!("GetAsyncIterator", cx.val(*obj)),
        Op::IteratorNext { iterator } => tok!("IteratorNext", cx.val(*iterator)),
        Op::IteratorReturn { iterator } => tok!("IteratorReturn", cx.val(*iterator)),
        Op::IteratorThrow { iterator } => tok!("IteratorThrow", cx.val(*iterator)),
        Op::GetPropIterator { obj } => tok!("GetPropIterator", cx.val(*obj)),
        Op::NextPropName { iterator } => tok!("NextPropName", cx.val(*iterator)),
        Op::NewLexEnv { num_vars } => tok!("NewLexEnv", CVal::Konst(format!("num:{num_vars}"))),
        Op::NewLexEnvWithName {
            num_vars,
            scope_names,
        } => tok!(
            "NewLexEnvWithName",
            CVal::Konst(format!("num:{num_vars}")),
            cx.konst(*scope_names)
        ),
        Op::PopLexEnv => tok!("PopLexEnv"),
        Op::GetLexVar { level, slot } => tok!(
            "GetLexVar",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}"))
        ),
        Op::PutLexVar { level, slot, value } => tok!(
            "PutLexVar",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*value)
        ),
        Op::TryGetGlobal { name, default } => {
            let dflt = match default {
                Some(v) => cx.val(*v),
                None => CVal::Konst("default:none".into()),
            };
            tok!("TryGetGlobal", cx.name(*name), dflt)
        }
        Op::StoreGlobal { name, value } => tok!("StoreGlobal", cx.name(*name), cx.val(*value)),
        Op::TryStoreGlobal { name, value } => {
            tok!("TryStoreGlobal", cx.name(*name), cx.val(*value))
        }
        Op::LoadModuleVar { index } => tok!("LoadModuleVar", CVal::Konst(format!("index:{index}"))),
        Op::StoreModuleVar { index, value } => {
            tok!(
                "StoreModuleVar",
                CVal::Konst(format!("index:{index}")),
                cx.val(*value)
            )
        }
        Op::GetModuleNamespace { index } => {
            tok!("GetModuleNamespace", CVal::Konst(format!("index:{index}")))
        }
        Op::DynamicImport { specifier } => tok!("DynamicImport", cx.val(*specifier)),
        Op::Call {
            callee,
            this,
            args,
            kind,
        } => {
            let mut ops = vec![cx.val(*callee)];
            ops.push(match this {
                Some(v) => cx.val(*v),
                None => CVal::Konst("this:none".into()),
            });
            ops.extend(args.iter().map(|&a| cx.val(a)));
            ops.push(CVal::Konst(format!(
                "kind:{}",
                match kind {
                    abcd_ir2::CallKind::Direct => "direct",
                    abcd_ir2::CallKind::Dynamic => "dynamic",
                    abcd_ir2::CallKind::Apply => "apply",
                    abcd_ir2::CallKind::Super => "super",
                    abcd_ir2::CallKind::SuperSpread => "superspread",
                    // N58 residual fold (documented, rule 4): v0.1
                    // represents supercallforwardallargs as plain
                    // SuperCall — indistinguishable from
                    // supercallthisrange — so the strictly-more-precise
                    // v0.2 kind canonicalizes DOWN to v0.1's token.
                    abcd_ir2::CallKind::SuperForwardAllArgs => "super",
                    abcd_ir2::CallKind::New => "new",
                }
            )));
            cx.push(iid, "Call", &ops)
        }
        Op::DefineFunc {
            body,
            captures,
            length,
        } => {
            let caps = if captures.is_empty() {
                "caps:[]".to_owned()
            } else {
                let inner: Vec<String> = captures
                    .iter()
                    .map(|(s, v)| format!("{}={}", cx.m.sym.resolve(*s).unwrap_or("?"), cx.val(*v)))
                    .collect();
                format!("caps:[{}]", inner.join(","))
            };
            tok!(
                "DefineFunc",
                CVal::Konst(format!("method:{}", body.index())),
                CVal::Konst(caps),
                CVal::Konst(format!("len:{length}"))
            )
        }
        Op::DefineClass {
            ctor,
            heritage,
            members,
            count,
        } => {
            let heritage_cv = match heritage {
                Some(v) => cx.val(*v),
                None => CVal::Konst("heritage:none".into()),
            };
            tok!(
                "DefineClass",
                CVal::Konst(format!("method:{}", ctor.index())),
                heritage_cv,
                cx.konst(*members),
                CVal::Konst(format!("count:{count}"))
            )
        }
        // N53 (divergence rule 8): canonicalize DOWN to the plain
        // `DefineClass` token — v0.1's DefineClassWithBuffer cannot
        // express the sendable distinction (its known collapse), and
        // the operand roles are identical. v0.2 is semantically
        // correct here; the fold is comparator-only.
        Op::DefineSendableClass {
            ctor,
            heritage,
            members,
            count,
        } => {
            let heritage_cv = match heritage {
                Some(v) => cx.val(*v),
                None => CVal::Konst("heritage:none".into()),
            };
            tok!(
                "DefineClass",
                CVal::Konst(format!("method:{}", ctor.index())),
                heritage_cv,
                cx.konst(*members),
                CVal::Konst(format!("count:{count}"))
            )
        }
        Op::LoadPrivate { level, slot, obj } => tok!(
            "LoadPrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj)
        ),
        Op::StorePrivate {
            level,
            slot,
            obj,
            value,
        } => tok!(
            "StorePrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj),
            cx.val(*value)
        ),
        Op::DefinePrivate {
            level,
            slot,
            obj,
            value,
        } => tok!(
            "DefinePrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj),
            cx.val(*value)
        ),
        Op::TestPrivate { level, slot, obj } => tok!(
            "TestPrivate",
            CVal::Konst(format!("level:{level}")),
            CVal::Konst(format!("slot:{slot}")),
            cx.val(*obj)
        ),
        Op::CreatePrivateNames { count, names } => tok!(
            "CreatePrivateNames",
            CVal::Konst(format!("count:{count}")),
            cx.konst(*names)
        ),
        Op::Throw { value } => tok!("Throw", cx.val(*value)),
        Op::ThrowIfSuperNotCalled { value, kind } => {
            let k = match kind {
                abcd_ir2::SuperCheck::NotCalled => 0,
                abcd_ir2::SuperCheck::Rebind => 1,
            };
            tok!(
                "ThrowIfSuperNotCalled",
                cx.val(*value),
                CVal::Konst(format!("supercheck:{k}"))
            )
        }
        Op::ThrowUndefinedIfHole { name, value } => {
            tok!("ThrowUndefinedIfHole", cx.val(*name), cx.val(*value))
        }
        Op::ThrowUndefinedIfHoleWithName { name, value } => {
            tok!(
                "ThrowUndefinedIfHoleWithName",
                cx.name(*name),
                cx.val(*value)
            )
        }
        Op::ThrowConstAssignment { name } => tok!("ThrowConstAssignment", cx.val(*name)),
        Op::ThrowIfNotObject { value } => tok!("ThrowIfNotObject", cx.val(*value)),
        Op::ThrowNotExists => tok!("ThrowNotExists"),
        Op::ThrowPatternNonCoercible => tok!("ThrowPatternNonCoercible"),
        Op::ThrowDeleteSuperProperty => tok!("ThrowDeleteSuperProperty"),
        Op::CreateGenerator { func } => tok!("CreateGenerator", cx.val(*func)),
        Op::SuspendGenerator { genobj, value } => {
            tok!("SuspendGenerator", cx.val(*genobj), cx.val(*value))
        }
        Op::ResumeGenerator { genobj } => tok!("ResumeGenerator", cx.val(*genobj)),
        Op::GetResumeMode { genobj } => tok!("GetResumeMode", cx.val(*genobj)),
        Op::Await { value } => tok!("Await", cx.val(*value)),
        Op::AwaitUncaught { value } => tok!("AwaitUncaught", cx.val(*value)),
        Op::AsyncFunctionEnter => tok!("AsyncFunctionEnter"),
        Op::AsyncResolve { value } => tok!("AsyncResolve", cx.val(*value)),
        Op::AsyncReject { value } => tok!("AsyncReject", cx.val(*value)),
        Op::LoadNewTarget => tok!("LoadNewTarget"),
        Op::LoadGlobalObject => tok!("LoadGlobalObject"),
        Op::LoadFunction => tok!("LoadFunction"),
        Op::GetUnmappedArgs => tok!("GetUnmappedArgs"),
        Op::CopyRestArgs { start_index } => {
            tok!("CopyRestArgs", CVal::Konst(format!("start:{start_index}")))
        }
        Op::LoadSuper { key } => {
            let key_cv = match key {
                abcd_ir2::SuperKey::Name(n) => cx.name(*n),
                abcd_ir2::SuperKey::Dynamic(v) => cx.val(*v),
            };
            tok!("LoadSuper", key_cv)
        }
        Op::StoreSuper { key, value } => {
            let key_cv = match key {
                abcd_ir2::SuperKey::Name(n) => cx.name(*n),
                abcd_ir2::SuperKey::Dynamic(v) => cx.val(*v),
            };
            tok!("StoreSuper", key_cv, cx.val(*value))
        }
        Op::Branch { dest } => tok!("Branch", cx.block(*dest)),
        Op::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => tok!(
            "CondBranch",
            cx.val(*cond),
            cx.block(*true_dest),
            cx.block(*false_dest)
        ),
        Op::Return { value } => {
            let ops: Vec<CVal> = value.iter().map(|&v| cx.val(v)).collect();
            cx.push(iid, "Return", &ops)
        }
        Op::Phi { entries } => {
            // Rule 6: collapse entries by source block (a block that is
            // both a Normal and an Exceptional pred carries the same
            // value on both edges — agree-check, keep the first).
            let mut seen: Vec<abcd_ir2::BlockId> = Vec::new();
            let mut ops: Vec<CVal> = Vec::new();
            for (edge, val) in entries {
                if seen.contains(&edge.from) {
                    // A duplicate-from entry with a DIFFERENT value
                    // would be a real divergence — surface it.
                    if let Some(pos) = seen.iter().position(|b| *b == edge.from) {
                        let prev = &ops[2 * pos + 1];
                        if *prev != cx.val(*val) {
                            ops.push(CVal::Konst("CONFLICTING-EDGE-VALUES".into()));
                        }
                    }
                    continue;
                }
                seen.push(edge.from);
                ops.push(cx.block(edge.from));
                ops.push(cx.val(*val));
            }
            cx.push(iid, "Phi", &ops)
        }
        Op::Unreachable => tok!("Unreachable"),
        Op::Debugger => tok!("Debugger"),
    }
}
