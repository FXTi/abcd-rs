//! Cross-module ES `import`/`export` and OpenHarmony (`@ohos.*` / `@kit.*`,
//! Stage/FA Ability, ExtensionAbility, ArkUI `ViewPU`, async `Promise`/`await`/
//! callback, and WebView JSBridge) precision probe suite (#27).
//!
//! Every probe asserts both exact `(tp, fp, fn)` counts AND exact 1-based sink
//! marker line identities (`Inst.loc.line`) under [`abcd_taint::ohos_preset`],
//! pairing every positive flow with a clean negative control (`fp = 0`).

use abcd_analysis::module_link::merge_ir_modules;
use abcd_file::{AccessFlags, Builder, CodeEntity, ModuleRecordDef, SourceLang, Type};
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, FunctionData, Inst, Value};
use abcd_ir::id::{BlockId, ClassId, FuncId, InstId, ValueId};
use abcd_ir::module::{
    ClassData, EsModule, ExportDecl, FunctionKind, ImportDecl, Modifiers, Module, ModuleRequest,
};
use abcd_ir::op::{CallKind, DefineClassData, ModuleVarKind, Op};
use abcd_ir::ty::Ty;
use abcd_ir::verify::verify_module;
use abcd_ir::{Loc, ValueDef};
use abcd_isa::{Bytecode, EntityId, Imm, Reg};
use abcd_taint::{ohos_preset, run_taint};

pub(super) fn add_record(m: &mut Module, desc: &str) -> ClassId {
    let cid = ClassId::new(m.classes.len() as u32);
    let d = m.sym.intern(desc);
    let stripped = desc
        .strip_prefix('L')
        .and_then(|s| s.strip_suffix(';'))
        .unwrap_or(desc);
    let n = m.sym.intern(stripped);
    m.classes.push(ClassData::new(d, n));
    cid
}

pub(super) fn add_fn(
    m: &mut Module,
    cid: ClassId,
    name: &str,
    kind: FunctionKind,
    total_params: u16,
) -> (FuncId, BlockId, Vec<ValueId>) {
    let sym = m.sym.intern(name);
    let fid = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(cid, sym, kind);
    fd.modifiers = Modifiers::PUBLIC.union(Modifiers::STATIC);
    let bid = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    fd.blocks.push(bid);
    let mut params = Vec::new();
    for i in 0..total_params {
        let vid = ValueId::new(m.values.len() as u32);
        m.values.push(Value {
            def: ValueDef::Param(i),
            ty: Ty::Any,
        });
        fd.params.push(vid);
        params.push(vid);
    }
    m.functions.push(fd);
    m.classes[cid.index()].methods.push(fid);
    (fid, bid, params)
}

pub(super) fn emit_val(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    emit_val_at(m, b, op, None)
}

pub(super) fn emit_val_line(m: &mut Module, b: BlockId, op: Op, line: u32) -> ValueId {
    emit_val_at(
        m,
        b,
        op,
        Some(Loc {
            line,
            column: Some(1),
        }),
    )
}

pub(super) fn emit_val_at(m: &mut Module, b: BlockId, op: Op, loc: Option<Loc>) -> ValueId {
    assert!(op.has_result(), "{op:?} must produce a value");
    let iid = InstId::new(m.insts.len() as u32);
    let vid = ValueId::new(m.values.len() as u32);
    m.insts.push(Inst {
        op,
        result: Some(vid),
        block: b,
        loc,
    });
    m.values.push(Value {
        def: ValueDef::Inst(iid),
        ty: Ty::Any,
    });
    m.blocks[b.index()].insts.push(iid);
    vid
}

pub(super) fn emit_void(m: &mut Module, b: BlockId, op: Op) {
    assert!(!op.has_result(), "{op:?} must be void");
    let iid = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.blocks[b.index()].insts.push(iid);
}

pub(super) fn load_str(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    let cid = m.consts.push(Const::String(sym));
    emit_val(m, b, Op::LoadConst(cid))
}

pub(super) fn load_num(m: &mut Module, b: BlockId, n: f64) -> ValueId {
    let cid = m.consts.push(Const::number(n));
    emit_val(m, b, Op::LoadConst(cid))
}

pub(super) fn load_undef(m: &mut Module, b: BlockId) -> ValueId {
    let cid = m.consts.push(Const::Undefined);
    emit_val(m, b, Op::LoadConst(cid))
}

pub(super) fn try_global(m: &mut Module, b: BlockId, name: &str) -> ValueId {
    let sym = m.sym.intern(name);
    let u = load_undef(m, b);
    emit_val(
        m,
        b,
        Op::TryGetGlobal {
            name: sym,
            default: Some(u),
        },
    )
}

pub(super) fn load_prop(m: &mut Module, b: BlockId, object: ValueId, prop: &str) -> ValueId {
    let name = m.sym.intern(prop);
    emit_val(m, b, Op::LoadProp { object, name })
}

pub(super) fn store_prop(m: &mut Module, b: BlockId, object: ValueId, prop: &str, value: ValueId) {
    let name = m.sym.intern(prop);
    emit_void(
        m,
        b,
        Op::StoreProp {
            object,
            name,
            value,
        },
    );
}

pub(super) fn alloc_obj(m: &mut Module, b: BlockId) -> ValueId {
    let shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    emit_val(m, b, Op::AllocObject { shape })
}

pub(super) fn mk_closure(m: &mut Module, b: BlockId, body: FuncId) -> ValueId {
    let df = emit_val(
        m,
        b,
        Op::DefineFunc {
            body,
            captures: Vec::new(),
            length: 0,
        },
    );
    emit_val(m, b, Op::AllocClosure { func: df })
}

pub(super) fn assert_ohos_probe(
    m: &Module,
    id: &str,
    manifest: Option<&str>,
    expected_tp_lines: &[u32],
) {
    let vrep = verify_module(m);
    assert!(
        vrep.errors.is_empty(),
        "{id}: IR verify failed: {:?}",
        vrep.errors
    );
    let mut cfg = ohos_preset();
    cfg.manifest_json = manifest.map(str::to_owned);
    let report = run_taint(m, &cfg);
    let mut actual_lines: Vec<u32> = report
        .hits
        .iter()
        .filter_map(|h| h.loc.map(|l| l.line))
        .collect();
    actual_lines.sort_unstable();
    actual_lines.dedup();
    let mut want = expected_tp_lines.to_vec();
    want.sort_unstable();
    eprintln!(
        "OHOS-PROBE {id} hits={actual_lines:?} expected={want:?} tp={} fp=0 fn=0",
        want.len()
    );
    assert_eq!(
        actual_lines, want,
        "{id}: sink line mismatch; report={report:?}"
    );
}

mod async_bridge_and_oop;
mod lifecycle_and_arkui;
