# abcd-ir — the SSA IR

The format-independent SSA intermediate representation for ArkCompiler
bytecode programs. This crate **is** the IR (as of v2-P4, 2026-09-21:
the v0.1 `abcd-ir` crate was deleted — git history is the archive — and
`abcd-ir2` was renamed `abcd-ir`).

The IR describes a **program** — classes, functions, value flow, types,
annotations, module records, debug info — never a **file**. It has no
dependency on the container/ISA crates (`abcd-file`, `abcd-isa`,
`abcd-file-sys`, `abcd-isa-sys`) and never may: the crate graph is the
enforcement mechanism.

## Module map

| Module | Contents |
|--------|----------|
| [`id`](src/id.rs) | Arena ids (`FuncId`, `ClassId`, `InstId`, `ValueId`, `BlockId`, …) — stable across pass pipelines |
| [`symbol`](src/symbol.rs) | `SymbolTable` / `Sym` — content-keyed strings; every name is a `Sym` |
| [`consts`](src/consts.rs) | `ConstPool` / `Const` — typed constant trees (literal arrays, method refs) |
| [`frame`](src/frame.rs) | `FrameSlots` / `this_param_index` — vendored `[func][new.target][this]` implicit parameter-slot decoding (`L_ESCallTypeAnnotation;`) |
| [`module`](src/module.rs) | `Module` — top-level program: functions, classes (including `--merge-abc` per-record `EsModule` & `scope_names`), imports/exports, annotations |
| [`function`](src/function.rs) | `FunctionData` — CFG blocks, instructions, SSA values, try regions, debug data |
| [`op`](src/op.rs) | The 88-variant op taxonomy — every instruction is one `Op` with explicit operands |
| [`effects`](src/effects.rs) | `Effects` — the single, mechanically derived source of effect truth (`Op::effects`) |
| [`ty`](src/ty.rs) | The type lattice (`Ty`, `StaticTy`) |
| [`verify`](src/verify.rs) | The verifier — `verify_module` collects every fallible finding into a `VerifyReport` (no panics on data) |

## Pipeline

- **Lift** (`abcd-lift`): decode → IR (`abcd_file::File` → `abcd_ir::Module`)
- **Optimize** (`abcd-opt`): IR → IR passes (peephole, SCCP, ADCE + CFG
  simplify, copyprop; inline opt-in)
- **Lower** (`abcd-lower`): IR → bytecode (`abcd_ir::Module` →
  `abcd_file::MethodBody`)
- **Analyze / Taint / Decompile** (`abcd-analysis`, `abcd-taint`,
  `abcd-decompile`): pure IR consumers (dominators, regions, IFDS +
  context-sensitive PTA, taint tracking, and JS/TS source recovery)

## Design

The full design — op taxonomy, the §5.3 call-binding table, the
taint-analysis contract (T1–T10), the migration plan — is
[`design/ir-v0.2.md`](../design/ir-v0.2.md) (background:
[`design/ir.md`](../design/ir.md) §1–§8).

## License

Apache-2.0.
