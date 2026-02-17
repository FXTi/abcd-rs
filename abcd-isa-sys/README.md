# abcd-isa-sys

> This document is intended for crate maintainers and contributors, covering the internal architecture, build pipeline, and API design of abcd-isa-sys.
> If you just want to use the instruction set API, see the higher-level [`abcd-isa`](../abcd-isa/README.md) crate.

This crate provides complete ArkCompiler bytecode instruction set C FFI bindings for Rust, via arkcompiler's Ruby code generation pipeline + a C++ bridge layer.

## Directory Structure

```
abcd-isa-sys/
├── build.rs                           # Ruby codegen → cc compile → bindgen
├── Cargo.toml                         # links = "isa_bridge"
├── vendor-sync.rb                     # Upstream file sync script
├── src/
│   └── lib.rs                         # include!(bindings.rs)
├── bridge/
│   ├── isa_bridge.h                   # C wrapper header (extern "C")
│   ├── isa_bridge.cpp                 # C wrapper implementation
│   └── shim/                          # Minimal shims (3 files, replacing heavy deps)
│       ├── securec.h                  # Huawei secure C library shim (memcpy_s wrapper)
│       ├── file.h                     # libpandafile/file.h shim (File::EntityId + LOG macro)
│       └── utils/
│           └── const_value.h          # Empty stub
├── templates/
│   ├── isa_bridge_tables.h.erb        # Custom template (metadata static tables)
│   ├── isa_bridge_emitter.h.erb       # Custom template (emitter C bridge impl)
│   └── isa_bridge_emitter_decl.h.erb  # Custom template (emitter C bridge decl)
└── vendor/
    ├── isa/
    │   ├── gen.rb                     # arkcompiler: runtime_core/isa/gen.rb
    │   ├── isapi.rb                   # arkcompiler: runtime_core/isa/isapi.rb
    │   ├── combine.rb                 # arkcompiler: runtime_core/isa/combine.rb
    │   └── isa.yaml                   # arkcompiler: runtime_core/isa/isa.yaml (ecmascript plugin merged)
    ├── libpandafile/
    │   ├── bytecode_instruction.h     # Bytecode instruction base class
    │   ├── bytecode_instruction-inl.h # Bytecode instruction inline impl
    │   ├── bytecode_emitter.h         # Emitter base class
    │   ├── bytecode_emitter.cpp       # Emitter implementation
    │   ├── pandafile_isapi.rb         # pandafile_isapi.rb
    │   └── templates/                 # Vendor ERB templates (5 files)
    └── libpandabase/                  # Base headers (macros.h, globals.h, span.h, etc.)
```

### Vendor File Origins

22 files copied verbatim from arkcompiler runtime_core:

```
vendor/isa/gen.rb                                          — runtime_core/isa/gen.rb
vendor/isa/isapi.rb                                        — runtime_core/isa/isapi.rb
vendor/isa/combine.rb                                      — runtime_core/isa/combine.rb
vendor/isa/isa.yaml                                        — runtime_core/isa/isa.yaml
vendor/libpandafile/pandafile_isapi.rb                     — runtime_core/libpandafile/pandafile_isapi.rb
vendor/libpandafile/templates/bytecode_instruction_enum_gen.h.erb
vendor/libpandafile/templates/bytecode_instruction-inl_gen.h.erb
vendor/libpandafile/templates/bytecode_emitter_def_gen.h.erb
vendor/libpandafile/templates/bytecode_emitter_gen.h.erb
vendor/libpandafile/templates/file_format_version.h.erb
vendor/libpandafile/bytecode_instruction.h
vendor/libpandafile/bytecode_instruction-inl.h
vendor/libpandafile/bytecode_emitter.h
vendor/libpandafile/bytecode_emitter.cpp
vendor/libpandabase/macros.h, globals.h, panda_visibility.h
vendor/libpandabase/utils/debug.h, bit_helpers.h, bit_utils.h, span.h
vendor/libpandabase/os/stacktrace.h
```

5 custom shim / bridge files:

```
bridge/shim/securec.h                  — Huawei secure C library shim, memcpy_s → standard memcpy wrapper
bridge/shim/file.h                     — Minimal libpandafile/file.h shim, File::EntityId + LOG macro + transitive deps
bridge/shim/utils/const_value.h        — Empty stub (include dependency of file_format_version.h)
templates/isa_bridge_emitter.h.erb     — Custom template, per-mnemonic C bridge emit function implementations
templates/isa_bridge_emitter_decl.h.erb — Custom template, per-mnemonic C bridge emit function declarations
```

Use `vendor-sync.rb` to sync vendor files from upstream. The script tracks file changes via SHA256 hashes and supports `--dry-run`, `--check-local`, `--force` modes.

## Build Pipeline Overview

```
isa.yaml (ISA data source)
    │
    ▼
gen.rb + isapi.rb + pandafile_isapi.rb (Ruby pipeline)
    │
    ├──► bytecode_instruction_enum_gen.h   (enums: Opcode, Format, Flags, Exceptions)
    ├──► bytecode_instruction-inl_gen.h    (inline methods: decode, operand extraction, ~11577 lines)
    ├──► isa_bridge_tables.h               (custom metadata tables: mnemonic, flags, exceptions, namespace, operands)
    ├──► bytecode_emitter_def_gen.h        (emitter method declarations)
    ├──► bytecode_emitter_gen.h            (emitter method implementations)
    ├──► file_format_version.h             (version constants + API version mapping)
    ├──► isa_bridge_emitter.h              (per-mnemonic C bridge emit function implementations)
    └──► isa_bridge_emitter_decl.h         (per-mnemonic C bridge emit function declarations, for bindgen)
            │
            ▼
    bytecode_instruction.h / -inl.h (vendor originals, deps satisfied via shims)
    bytecode_emitter.h / .cpp (vendor emitter, compiled directly)
            │
            ▼
    isa_bridge.h / isa_bridge.cpp (thin C wrapper, extern "C")
            │
            ▼
    build.rs: cc compiles C++ → bindgen generates FFI bindings
            │
            ▼
    src/lib.rs (include!(bindings.rs))
            │
            ▼
    abcd-isa crate obtains bindings.rs path via DEP_ISA_BRIDGE_BINDINGS_RS
```

### Comparison with arkcompiler's Original Build System

arkcompiler uses CMake to drive Ruby code generation (`TemplateBasedGen.cmake`), consuming generated headers directly in C++ projects.

Our differences:
- Use Rust `build.rs` to drive Ruby instead of CMake
- Use vendor original C++ headers + minimal shims (securec.h, file.h, const_value.h) instead of heavy dependencies
- Added custom `isa_bridge_tables.h.erb` template to export mnemonic/flags/exceptions metadata (in the original pipeline, this info is embedded in `HasFlag` switch statements with no standalone static tables)
- Compile with `-DNDEBUG` to eliminate C++ debug assertion runtime dependencies
- All prefix detection uses `Inst::GetMinPrefixOpcodeIndex()` threshold — zero hardcoded constants
- ISA_FLAG_* and ISA_EXC_* constants generated as `#define` macros, directly exported to Rust by bindgen

## Ruby Code Generation Pipeline

### gen.rb — Template Driver

`vendor/isa/gen.rb` is the entry point. It accepts `--template`, `--data`, `--output`, `--require` arguments. Flow:

1. Load `isa.yaml` → JSON → OpenStruct (frozen to prevent accidental modification by templates)
2. Require extension scripts (isapi.rb, pandafile_isapi.rb), triggering the `Gen.on_require(data)` hook
3. ERB template rendering with `'%-'` trim mode

Invocation from build.rs:

```rust
Command::new("ruby")
    .args([gen_rb, "-t", template, "-d", isa_yaml, "-r", requires, "-o", output])
    .status()
```

### isapi.rb — ISA Data API (Core)

`vendor/isa/isapi.rb` (~670 lines) defines the `Panda` module and classes like `Instruction`, `Format`, `Operand`, `OpcodeAssigner`. All ERB templates access ISA data through these APIs.

Key concepts:

- `Panda.instructions` — Ordered array of all instructions; processes those with explicit `opcode_idx` first, then auto-assigns the rest
- `Instruction#mnemonic` — First word of the signature, e.g. `"mov v1:out:any, v2:in:any"` → `"mov"`
- `Instruction#opcode` — Unique identifier (mnemonic + format), e.g. `"mov_v8_v8"`, used as C++ enum name
- `Instruction#opcode_idx` — Numeric opcode encoding: non-prefixed instructions use the first byte value (0x00-0xDC); prefixed instructions use `(sub_opcode << 8) | prefix_byte`
- `Format#pretty` — Normalized format name, e.g. `"pref_op_v1_4_v2_4"` → `"v4_v4"`
- `Format#size` — Total instruction bytes = operand bits / 8 + opcode bytes (2 for prefixed, 1 for non-prefixed)
- `Format#encoding` — Operand encoding map (name → {offset, width}), prefixed instructions start at bit 16
- `Operand` — Operand types: `reg?`, `acc?`, `imm?`, `id?`; direction: `src?`, `dst?`
- `OpcodeAssigner` — Each prefix has an independent 0-255 namespace, auto-assigns the smallest available value

### pandafile_isapi.rb — PandaFile Extensions

`vendor/libpandafile/pandafile_isapi.rb` (~82 lines) adds methods to `Instruction` and `Operand` via `class_eval`:

- `emitter_name` — `"mov"` → `"Mov"`, `"throw.ifnotobject"` → `"ThrowIfnotobject"`
- `each_operand` — Operand iteration with type indices
- `jcmp?` / `jcmpz?` — Conditional jump classification
- `insns_uniq_sort_fmts` — Deduplicate and sort by format, used for generating switch cases

### combine.rb — YAML Merging

`vendor/isa/combine.rb` merges core + plugin ISA YAMLs. Key constraint: plugin instructions must all have a prefix, ensuring the core ISA's 0x00-0xFA namespace is not polluted.

We use the pre-merged `isa.yaml` directly and do not need to run combine.rb.

## Generated C++ Code

### bytecode_instruction_enum_gen.h

Injected into the `BytecodeInst` class body via `#include <bytecode_instruction_enum_gen.h>`, generating 4 enums:

- `Format` — ~80 formats: `NONE`, `V4_V4`, `V8`, `IMM8`, `PREF_IMM16_V8`, ...
- `Opcode` — 326 opcodes, value range: non-prefixed 0-220, prefixed 251-11772
- `Flags` — Property bitmask (JUMP, CONDITIONAL, RETURN, etc.)
- `Exceptions` — Exception type bitmask

### bytecode_instruction-inl_gen.h

Generates ~11577 lines of inline methods. Key methods:

- `GetOpcode()` — Encodes as `(secondary << 8) | primary`; primary >= 251 indicates a prefixed instruction
- `HasId/HasVReg/HasImm(Format, idx)` — Compile-time queries
- `Size(Format)` — Total instruction bytes
- `GetId/GetVReg/GetImm<format, idx>()` — Compile-time template methods
- `GetId/GetVReg/GetImm64(idx)` — Runtime methods (large switch over all formats)
- `HasFlag(Flags)` — Runtime property query
- `operator<<` — Formatted output

The runtime methods are the core dependency of the C bridge — the bridge layer calls them directly, avoiding re-implementation of operand decoding logic on the C side.

### isa_bridge_tables.h (Custom Template)

In arkcompiler's original pipeline, metadata like mnemonic/flags/exceptions is embedded in `HasFlag`/`operator<<` switch statements with no standalone static lookup tables. We wrote a custom ERB template to generate pure C static arrays:

| Table | Structure | Purpose |
|-------|-----------|---------|
| `ISA_MNEMONIC_TABLE[]` | `{opcode, mnemonic}` | opcode → mnemonic string (sorted by opcode for binary search) |
| `ISA_FLAGS_TABLE[]` | `{opcode, flags}` | opcode → property bitmask |
| `ISA_EXCEPTIONS_TABLE[]` | `{opcode, exceptions}` | opcode → exception type bitmask |
| `ISA_NAMESPACE_TABLE[]` | `{opcode, ns}` | opcode → namespace string |
| `ISA_OPERANDS_TABLE[]` | `{opcode, num_operands, acc_read, acc_write, operands[8]}` | opcode → operand details |

Property bitmask generation: collects and deduplicates all instruction `properties`, assigns each a bit position, generates `#define ISA_FLAG_<TAG> (1u << N)`. Additionally adds a synthetic `ISA_FLAG_THROW` (bit 31) flag for instructions with `x_throw` exceptions.

Each operand in the operand details table records `{kind, op_type, bit_width, is_src, is_dst}`.

### isa_bridge_emitter.h / isa_bridge_emitter_decl.h (Custom Templates)

Generates one C bridge emit function per mnemonic. Jump instructions replace `const Label&` parameters with `uint32_t label_id`, and the bridge internally looks up via `e->labels[label_id]`.

Template responsibilities:
- `isa_bridge_emitter.h.erb` — Function implementations, included in `isa_bridge.cpp`
- `isa_bridge_emitter_decl.h.erb` — Function declarations, used in the bindgen wrapper header

## C++ Base Class and Shim Strategy

The vendor `bytecode_instruction.h` (439 lines) defines the `BytecodeInst<Mode>` template class. We only use `FAST` mode (direct memory access, no bounds checking).

Original file dependencies are resolved via include path priority, requiring only 3 shim files:

```
bytecode_instruction.h
  → "file.h"              → bridge/shim/file.h (shim: File::EntityId + LOG + transitive deps)
  → "utils/bit_helpers.h"  → vendor/libpandabase/utils/bit_helpers.h (original)
  → "securec.h"            → bridge/shim/securec.h (shim: memcpy_s wrapper)

bytecode_instruction-inl.h
  → "macros.h"             → vendor/libpandabase/macros.h (original, with -DNDEBUG)
    → "os/stacktrace.h"    → vendor (declarations only)
    → "utils/debug.h"      → vendor (declarations only)
```

Compiling with `-DNDEBUG` turns ASSERT into a no-op and UNREACHABLE into `std::abort()`, eliminating dependencies on AssertionFail/PrintStack implementations.

The vendor `bytecode_emitter.cpp` obtains all dependencies via include paths (`Span<T>`, `MinimumBitsToStore`, etc.), and build.rs compiles it directly without a wrapper.

## C Bridge API Design

`bridge/isa_bridge.h` + `bridge/isa_bridge.cpp`

Design principles:
1. Pure C interface (`extern "C"`) for easy bindgen Rust FFI generation
2. Decode/metadata functions are stateless and thread-safe; Emitter is stateful
3. Byte stream operations accept `const uint8_t* bytes`, mapping naturally to Rust slices
4. Errors use sentinel values (`SIZE_MAX` = decode failure, `-1` = no result)

> Metadata query functions (mnemonic/flags/exceptions/namespace/operand_info) and classification helpers (is_jump/is_conditional/is_return/is_throw) have been removed. abcd-isa reads `ISA_*_TABLE` static tables and `OpcodeFlags` bitmasks directly, avoiding binary search overhead.

### Decode Layer

```c
size_t  isa_decode_index(const uint8_t* bytes, size_t len);  // → table index, returns SIZE_MAX on failure
uint8_t isa_get_format(uint16_t opcode);                      // → GetFormat(Opcode)
size_t  isa_get_size(uint8_t format);                          // → Size(Format)
int     isa_is_prefixed(uint16_t opcode);                      // checks low byte
```

### Operand Extraction Layer

```c
uint16_t isa_get_vreg(const uint8_t* bytes, size_t idx);
int64_t  isa_get_imm64(const uint8_t* bytes, size_t idx);
uint32_t isa_get_id(const uint8_t* bytes, size_t idx);
int      isa_has_vreg(uint8_t format, size_t idx);
int      isa_has_imm(uint8_t format, size_t idx);
int      isa_has_id(uint8_t format, size_t idx);
```

### Classification

```c
int isa_is_range(uint16_t opcode);          // IsRangeInstruction()
int isa_is_suspend(uint16_t opcode);        // HasFlag(SUSPEND)
int isa_can_throw(const uint8_t* bytes);
int isa_is_terminator(const uint8_t* bytes);
int isa_is_return_or_throw(const uint8_t* bytes);
```

### Constants and Prefix Queries

```c
uint8_t isa_min_prefix_opcode(void);              // GetMinPrefixOpcodeIndex() — currently 251
size_t  isa_prefix_count(void);
uint8_t isa_prefix_opcode_at(size_t idx);
int     isa_is_primary_opcode_valid(uint8_t primary);
```

### Additional Operand Methods

```c
int64_t isa_get_imm_data(const uint8_t* bytes, size_t idx);
size_t  isa_get_imm_count(const uint8_t* bytes);
size_t  isa_get_literal_index(const uint8_t* bytes);
void    isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx);
int64_t isa_get_last_vreg(const uint8_t* bytes);
int64_t isa_get_range_last_reg_idx(const uint8_t* bytes);
int     isa_is_id_match_flag(const uint8_t* bytes, size_t idx, uint32_t flag);
size_t  isa_format_instruction(const uint8_t* bytes, size_t len, char* buf, size_t buf_len);
```

### Version API

```c
void   isa_get_version(uint8_t out[4]);
void   isa_get_min_version(uint8_t out[4]);
size_t isa_get_api_version_count(void);
int    isa_get_version_by_api(uint8_t api_level, uint8_t out[4]);
int    isa_is_version_compatible(const uint8_t ver[4]);
```

### Emitter API

```c
typedef struct IsaEmitter IsaEmitter;

IsaEmitter* isa_emitter_create(void);
void        isa_emitter_destroy(IsaEmitter* e);
uint32_t    isa_emitter_create_label(IsaEmitter* e);
void        isa_emitter_bind(IsaEmitter* e, uint32_t label_id);
int         isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
void        isa_emitter_free_buf(uint8_t* buf);

// Per-mnemonic emit functions (generated by isa_bridge_emitter.h.erb, 326 total)
void isa_emit_mov(IsaEmitter* e, uint8_t vd, uint8_t vs);
void isa_emit_jmp(IsaEmitter* e, uint32_t label_id);
// ...
```

`IsaEmitter` internally holds a C++ `BytecodeEmitter` + `vector<Label>`. `isa_emitter_create_label` returns the labels array index; jump instruction emit functions look up the Label by index and pass it to the C++ emitter.

### Opcode Encoding

Opcode values are encoded as `(sub_opcode << 8) | prefix_byte`:
- Non-prefixed instructions: value = first byte (0x00-0xDC), upper 8 bits are 0
- Prefixed instructions: low 8 bits = prefix byte (>= 251), upper 8 bits = sub-opcode

## Cargo Metadata

`links = "isa_bridge"` — Passes the generated bindings.rs path to dependents (`abcd-isa`) via the `DEP_ISA_BRIDGE_BINDINGS_RS` environment variable.

## Build Dependencies

- Ruby 2.5+ (runs gen.rb code generation)
- C++17 compiler (compiles bridge + generated headers)
- `cc` crate (compiles C++ during Rust build)
- `bindgen` crate (generates Rust FFI bindings)

## Statistics

- 326 opcodes: 225 non-prefixed (0x00-0xDC) + 101 prefixed (4 prefix groups)
- ~80 instruction formats
- 4 prefixes: `callruntime` (0xFB), `deprecated` (0xFC), `wide` (0xFD), `throw` (0xFE)
- Ruby generates 8 header files
- C++ compiles 2 source files: isa_bridge.cpp + vendor/bytecode_emitter.cpp
- 22 vendor files, 3 shim files (~55 lines of custom code)
- C bridge exports 40+ static functions + 326 per-mnemonic emit functions
- ISA_FLAG_* 24 property flags + ISA_EXC_* exception flags
