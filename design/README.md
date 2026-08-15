# abcd-rs Design Docs

Design documentation for the ArkCompiler ABC bytecode Rust toolkit (second generation). All documents are Markdown and live with the code.

## Index

| Doc | Contents |
|-----|----------|
| [overview.md](overview.md) | Architecture: positioning, crate layering, data flow, version-aware design, current status |
| [isa.md](isa.md) | ISA layer: code generation pipeline, Bytecode enum, decode/encode, classification and version APIs |
| [file-format.md](file-format.md) | ABC container layer: file layout, accessor/bridge design, builder, shim strategy |
| [ir.md](ir.md) | SSA IR: lift / opt / lower end-to-end design, register allocation, paper references |
| [vendor-sync.md](vendor-sync.md) | Vendor sync system: zero-diff principle, metadata locking, consistency checks |
| [ci.md](ci.md) | CI/CD: job rationale, release policy |

## The pipeline in one line

```
.abc ──decode──▶ abcd-isa ──▶ abcd-file ──lift──▶ abcd-ir (SSA) ──opt──▶ ──lower──▶ abcd-file ──encode──▶ .abc
```
