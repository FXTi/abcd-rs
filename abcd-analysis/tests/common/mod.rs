//! Shared helpers for `abcd-analysis` corpus/integration tests.
//!
//! - Corpus harness (`corpus_root` / `manifest_paths`): the exported GHCR
//!   corpus + python3 manifest pattern of
//!   `abcd-lift/tests/corpus_lift_verify.rs`.
//! - The dominator-agreement reference (`verify_reference_dom_sets` /
//!   `check_function`): a VERBATIM port of `abcd-ir/src/verify.rs`'s
//!   private iterative dominator computation (`verify_dominance`, the N45
//!   check). `abcd-ir` cannot depend on `abcd-analysis` (one-way
//!   layering), so the pin between the two implementations lives here.

// Each test binary uses a different subset.
#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use abcd_analysis::control::Dominators;
use abcd_ir::consts::Const;
use abcd_ir::function::{Block, Catch, FunctionData, Inst, TryRegion, Value};
use abcd_ir::module::{ClassData, FunctionKind, Modifiers, SourceLang};
use abcd_ir::ty::Ty;
use abcd_ir::{BlockId, ClassId, EdgeKind, FuncId, Module};

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

/// Every fixture path in the manifest (all 5517 rows, sorted for
/// determinism), parsed with python3's standard JSON library.
pub fn manifest_paths(root: &Path) -> Vec<String> {
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

/// Verbatim port of abcd-ir/src/verify.rs's iterative dominator sets over
/// the Normal-edge CFG (stored predecessors). Returns, per
/// `func.blocks` index, that block's dominator set as block indices.
pub fn verify_reference_dom_sets(module: &Module, func_id: FuncId) -> Vec<HashSet<usize>> {
    let func = module.func(func_id).expect("function");
    let index: HashMap<BlockId, usize> = func
        .blocks
        .iter()
        .enumerate()
        .map(|(i, &b)| (b, i))
        .collect();
    let n = func.blocks.len();
    let entry_i = 0usize;

    // Normal-edge predecessors per block (in-function only).
    let mut npreds: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        let i = index[&bb];
        for edge in &block.preds {
            if edge.kind == EdgeKind::Normal
                && let Some(&p) = index.get(&edge.from)
            {
                npreds[i].push(p);
            }
        }
    }

    // Iterative dominator sets over the Normal-edge CFG.
    let all: HashSet<usize> = (0..n).collect();
    let mut dom: Vec<HashSet<usize>> = vec![all; n];
    dom[entry_i] = HashSet::from([entry_i]);
    loop {
        let mut changed = false;
        for i in 0..n {
            if i == entry_i {
                continue;
            }
            let mut new: HashSet<usize> = if npreds[i].is_empty() {
                HashSet::new()
            } else {
                let mut acc = dom[npreds[i][0]].clone();
                for &p in &npreds[i][1..] {
                    acc = acc.intersection(&dom[p]).copied().collect();
                }
                acc
            };
            new.insert(i);
            if new != dom[i] {
                dom[i] = new;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    dom
}

/// Check one function: the dominance agreement contract (also documented
/// in `abcd_analysis::control`'s module docs) — over all blocks BOTH
/// implementations consider Normal-reachable (reachable from the entry in
/// `Dominators`' tree AND containing the entry in the verifier's
/// `dom[b]`), the two compute the same dominator SETS.
///
/// Two documented divergence classes are excluded (both dead-code shapes
/// the verifier's N45 check exempts anyway):
///
/// 1. Unreachable Normal-edge cycles keep the verifier's initial
///    "everything" set (so they look entry-dominated) while the tree
///    reports them unreachable.
/// 2. A reachable block with an unreachable Normal predecessor is
///    *polluted* by the verifier's all-set initialization: the
///    intersection with the dead predecessor's degenerate set empties it,
///    so the verifier treats the block as unreachable; the CHK tree
///    computes dominators on the reachable subgraph (the graph-theoretic
///    answer). The divergence always weakens the verifier's check, never
///    strengthens it, and `abcd-ir` is frozen for this task — so the
///    contract is the intersection domain.
///
/// Returns `(blocks compared, blocks skipped by divergence, blocks total)`.
pub fn check_function(module: &Module, func_id: FuncId, ctx: &str) -> (usize, usize, usize) {
    let func = module.func(func_id).expect("function");
    if func.blocks.is_empty() {
        return (0, 0, 0);
    }
    let index_of = |b: BlockId| {
        func.blocks
            .iter()
            .position(|&x| x == b)
            .expect("in-function")
    };

    // The shared relation: Normal-edge successors = inverse of the stored
    // Normal predecessors (in-function only). Both implementations see
    // exactly this graph.
    let mut succs: HashMap<BlockId, Vec<BlockId>> = HashMap::new();
    for &bb in &func.blocks {
        let Some(block) = module.block(bb) else {
            continue;
        };
        for edge in &block.preds {
            if edge.kind == EdgeKind::Normal && func.blocks.contains(&edge.from) {
                succs.entry(edge.from).or_default().push(bb);
            }
        }
    }
    let succ_of = |b: BlockId| succs.get(&b).cloned().unwrap_or_default();

    let dom = Dominators::over(module, func_id, &succ_of);
    let reference = verify_reference_dom_sets(module, func_id);
    let entry = func.blocks[0];

    // The agreement domain: blocks reachable from the entry over the
    // Normal relation (BFS). For these, the verifier's `dom[i]` contains
    // the entry and equals the tree-derived dominator set.
    let reachable = abcd_analysis::control::reachable_blocks(module, func_id, &succ_of);

    let mut compared = 0usize;
    let mut skipped = 0usize;
    let entry_i = 0usize;
    for &b in &reachable {
        let i = index_of(b);
        // Divergence classes (see the contract above): skip blocks the
        // verifier's sets treat as unreachable despite the tree reaching
        // them.
        if !reference[i].contains(&entry_i) {
            skipped += 1;
            continue;
        }
        let reference_set: std::collections::BTreeSet<BlockId> =
            reference[i].iter().map(|&j| func.blocks[j]).collect();
        let mine: std::collections::BTreeSet<BlockId> =
            dom.dominator_chain(b).into_iter().collect();
        assert_eq!(
            mine, reference_set,
            "dominator-set disagreement in {ctx} {func_id:?} block {b:?} (entry {entry:?})"
        );
        compared += 1;
    }
    (compared, skipped, func.blocks.len())
}

// ── IR module scaffolding (mirrors src/testutil.rs, which is cfg(test)) ──

use abcd_ir::{ConstId, InstId, Op, Sym, ValueDef, ValueId};

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

/// A fresh named function with one (entry) block, wired into class 0.
pub fn add_func_named(m: &mut Module, name: &str) -> FuncId {
    let name = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    m.functions.push(FunctionData::new(
        ClassId::new(0),
        name,
        FunctionKind::Function,
    ));
    m.classes[0].methods.push(id);
    add_block(m, id); // entry
    id
}

/// A fresh external (bodyless) function record: no blocks at all.
pub fn add_external_func(m: &mut Module, name: &str) -> FuncId {
    let name = m.sym.intern(name);
    let id = FuncId::new(m.functions.len() as u32);
    let mut fd = FunctionData::new(ClassId::new(0), name, FunctionKind::Function);
    fd.is_external = true;
    m.functions.push(fd);
    m.classes[0].methods.push(id);
    id
}

/// A fresh empty block appended to `f`.
pub fn add_block(m: &mut Module, f: FuncId) -> BlockId {
    let id = BlockId::new(m.blocks.len() as u32);
    m.blocks.push(Block::default());
    m.func_mut(f).unwrap().blocks.push(id);
    id
}

/// Append an instruction without wiring a result.
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
    assert!(op.has_result());
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
    assert!(!op.has_result());
    push_inst(m, b, op)
}

/// Append a parameter value (`params[0]` is the vendored func slot).
pub fn add_param(m: &mut Module, f: FuncId, idx: u16) -> ValueId {
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

/// A const-defined value (`ValueDef::Const`, no instruction).
pub fn const_value(m: &mut Module, c: Const) -> ValueId {
    let cid = m.consts.push(c);
    let val = ValueId::new(m.values.len() as u32);
    m.values.push(Value {
        def: ValueDef::Const(cid),
        ty: Ty::Any,
    });
    val
}

/// Record a Normal edge (on the successor side, as the IR stores them).
pub fn link(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(abcd_ir::Edge {
        from,
        kind: EdgeKind::Normal,
    });
}

/// Record an Exceptional edge.
pub fn link_exc(m: &mut Module, from: BlockId, to: BlockId) {
    m.block_mut(to).unwrap().preds.push(abcd_ir::Edge {
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

/// A number literal load.
pub fn load_number(m: &mut Module, b: BlockId, x: f64) -> ValueId {
    let c = m.consts.push(Const::number(x));
    emit(m, b, Op::LoadConst(c))
}

/// A string literal load.
pub fn load_string(m: &mut Module, b: BlockId, s: &str) -> ValueId {
    let sym = m.sym.intern(s);
    let c = m.consts.push(Const::String(sym));
    emit(m, b, Op::LoadConst(c))
}

/// A `Const::MethodRef` load (function value as a pooled constant).
pub fn load_method_ref(m: &mut Module, b: BlockId, func: FuncId) -> ValueId {
    let c = m.consts.push(Const::MethodRef(func));
    emit(m, b, Op::LoadConst(c))
}

/// Intern a name.
pub fn intern(m: &mut Module, s: &str) -> Sym {
    m.sym.intern(s)
}

/// An `AllocObject` site.
pub fn alloc_object(m: &mut Module, b: BlockId) -> ValueId {
    let shape = m.consts.push(Const::ObjectLiteral {
        keys: Vec::new(),
        values: Vec::new(),
    });
    emit(m, b, Op::AllocObject { shape })
}

/// An `AllocArray` site (empty array).
pub fn alloc_array(m: &mut Module, b: BlockId) -> ValueId {
    emit(m, b, Op::AllocArray { shape: None })
}

/// A `TryGetGlobal(name)` (no default).
pub fn try_get_global(m: &mut Module, b: BlockId, name: &str) -> ValueId {
    let sym = intern(m, name);
    emit(
        m,
        b,
        Op::TryGetGlobal {
            name: sym,
            default: None,
        },
    )
}

/// The ConstId of a pushed constant.
pub fn push_const(m: &mut Module, c: Const) -> ConstId {
    m.consts.push(c)
}

/// A static callee with the vendored 0xF implicit slots + `formals`
/// source formals (the es2abc shape). Returns (FuncId, params).
pub fn add_static_func(m: &mut Module, name: &str, formals: u16) -> (FuncId, Vec<ValueId>) {
    let f = add_func_named(m, name);
    m.func_mut(f).unwrap().modifiers = Modifiers::STATIC;
    let mut params = Vec::new();
    for i in 0..(3 + formals) {
        params.push(add_param(m, f, i));
    }
    (f, params)
}

/// Define + allocate a closure of `body` in block `b`; returns the
/// closure value.
pub fn closure_of(m: &mut Module, b: BlockId, body: FuncId) -> ValueId {
    let def = emit(
        m,
        b,
        Op::DefineFunc {
            body,
            captures: vec![],
            length: 0,
        },
    );
    emit(m, b, Op::AllocClosure { func: def })
}

/// The defining instruction of an inst-defined value.
pub fn inst_of(m: &Module, v: ValueId) -> InstId {
    match m.value(v).unwrap().def {
        ValueDef::Inst(i) => i,
        other => panic!("not inst-defined: {other:?}"),
    }
}
