//! Shared helpers for `abcd-decompile` tests.
//!
//! - Hand-built module scaffolding (mirrors `abcd-analysis`'s testutil:
//!   blocks get terminators, results are wired to `ValueDef::Inst`, CFG
//!   edges are recorded on the successor side).
//! - Corpus harness (`corpus_root` / `manifest_paths`): the exported
//!   GHCR corpus + python3 manifest pattern of
//!   `abcd-lift/tests/corpus_lift_verify.rs`.

// Each test binary uses a different subset.
#![allow(dead_code)]

use std::path::PathBuf;
use std::process::Command;

use abcd_ir::consts::Const;
use abcd_ir::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers, SourceLang};
use abcd_ir::ty::Ty;
use abcd_ir::{
    BlockId, ClassId, ConstId, Edge, EdgeKind, FuncId, InstId, Module, Op, Sym, ValueDef, ValueId,
};

/// A module with one empty class record (the function home).
pub fn mk_module() -> Module {
    let mut m = Module::new();
    let name = m.sym.intern("Ltest;");
    m.classes.push(ClassData {
        descriptor: name,
        name,
        modifiers: Modifiers::NONE,
        source_lang: SourceLang::EcmaScript,
        super_class: None,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        annotations: Vec::new(),
        source_file: None,
    });
    m
}

/// A fresh function named `f` with one (entry) block, wired into class 0.
pub fn add_func(m: &mut Module) -> FuncId {
    add_func_named(m, "f")
}

/// A fresh named function with one (entry) block, wired into class 0.
pub fn add_func_named(m: &mut Module, name: &str) -> FuncId {
    add_func_kind(m, name, FunctionKind::Function)
}

/// A fresh named function of a given kind with one (entry) block.
pub fn add_func_kind(m: &mut Module, name: &str, kind: FunctionKind) -> FuncId {
    let name = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    m.functions
        .push(FunctionData::new(ClassId::new(0), name, kind));
    m.classes[0].methods.push(id);
    add_block(m, id); // entry
    id
}

/// A fresh empty block appended to `f`.
pub fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

/// Append an instruction without wiring a result; returns the inst.
pub fn push_inst(m: &mut Module, b: BlockId, op: Op) -> InstId {
    let id = InstId::new(m.insts.len() as u32);
    m.insts.push(Inst {
        op,
        result: None,
        block: b,
        loc: None,
    });
    m.block_mut(b).unwrap().insts.push(id);
    id
}

/// Append an op that produces a value; returns the result value.
pub fn emit(m: &mut Module, b: BlockId, op: Op) -> ValueId {
    assert!(op.has_result(), "{op:?} has no result");
    let inst = push_inst(m, b, op);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Inst(inst),
        ty: Ty::Any,
    });
    m.inst_mut(inst).unwrap().result = Some(val);
    val
}

/// Append an op that produces no value; returns the instruction.
pub fn emit_void(m: &mut Module, b: BlockId, op: Op) -> InstId {
    assert!(!op.has_result(), "{op:?} has a result");
    push_inst(m, b, op)
}

/// Append a parameter value (`params[0]` = `this` by convention).
pub fn add_param(m: &mut Module, f: FuncId) -> ValueId {
    let idx = m.func(f).unwrap().params.len() as u16;
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Param(idx),
        ty: Ty::Any,
    });
    m.func_mut(f).unwrap().params.push(val);
    val
}

/// Append the exception-parameter value delivered at a handler entry.
pub fn add_exception_param(m: &mut Module, handler: BlockId) -> ValueId {
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::ExceptionParam(handler),
        ty: Ty::Any,
    });
    val
}

/// Record a Normal edge (on the successor side, as the IR stores them).
pub fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

/// Record an Exceptional edge.
pub fn link_exc(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(Edge {
        from,
        kind: EdgeKind::Exceptional,
    });
}

/// Add a try region protecting `protected` with a single catch-all handler.
pub fn add_try(m: &mut Module, f: FuncId, protected: Vec<BlockId>, handler: BlockId, exc: ValueId) {
    for &p in &protected {
        link_exc(m, p, handler);
    }
    m.func_mut(f).unwrap().try_regions.push(TryRegion {
        protected,
        catches: vec![Catch {
            handler,
            exception: exc,
            type_idx: None,
        }],
    });
}

/// The entry block of `f`.
pub fn entry_of(m: &Module, f: FuncId) -> BlockId {
    m.func(f).unwrap().blocks[0]
}

/// Push a constant and return a `LoadConst` of it in `b`.
pub fn load_const(m: &mut Module, b: BlockId, c: Const) -> ValueId {
    let cid = m.consts.push(c);
    emit(m, b, Op::LoadConst(cid))
}

/// A number literal load.
pub fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    load_const(m, b, Const::number(x))
}

/// A string literal load.
pub fn load_string(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    load_const(m, b, Const::String(sym))
}

/// Push a constant and return its id.
pub fn const_id(m: &mut Module, c: Const) -> ConstId {
    m.consts.push(c)
}

/// `left + right` (semantic order — N36: the IR stores `left` = acc
/// operand, `right` = vreg operand, and the vendored handlers compute
/// `vreg OP acc`, so the fields are swapped on construction).
pub fn add(m: &mut Module, b: BlockId, l: ValueId, r: ValueId) -> ValueId {
    emit(
        m,
        b,
        Op::BinaryOp {
            op: abcd_ir::op::BinOp::Add,
            left: r,
            right: l,
        },
    )
}

/// Intern a name.
pub fn intern(m: &mut Module, s: &str) -> Sym {
    m.sym.intern(s)
}

/// The corpus root: `$ABCD_CORPUS_ROOT` or `exports/corpus`.
pub fn corpus_root() -> PathBuf {
    std::env::var_os("ABCD_CORPUS_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("exports")
                .join("corpus")
        })
}

/// Every fixture path in the manifest (all 2787 rows, sorted for
/// determinism), parsed with python3's standard JSON library.
pub fn manifest_paths(root: &std::path::Path) -> Vec<String> {
    let output = Command::new("python3")
        .arg("-c")
        .arg(
            r#"
import json, sys
paths = []
with open(sys.argv[1], encoding="utf-8") as manifest:
    for line in manifest:
        row = json.loads(line)
        assert "\n" not in row["abc"] and "\t" not in row["abc"]
        paths.append(row["abc"])
for path in sorted(paths):
    print(path)
"#,
        )
        .arg(root.join("index.jsonl"))
        .output()
        .expect("python3 is required by corpus tooling");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 fixture paths")
        .lines()
        .map(str::to_string)
        .collect()
}
