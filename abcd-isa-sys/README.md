# abcd-isa-sys

> This document is intended for crate maintainers and contributors, covering the internal architecture, build pipeline, and API design of `abcd-isa-sys`.
> If you just want to use the instruction set API, see the higher-level [`abcd-isa`](../abcd-isa/README.md) crate.

This crate provides ArkCompiler bytecode instruction set C FFI bindings for Rust via pre-generated Rust/C++ bindings (`scripts/vendor-gen.py`) and a thin C++17 bridge layer. It exposes two pre-generated artifact families through `src/lib.rs`:

- `src/generated/bindings.rs` — raw `isa_*` FFI functions, types, and sentinel constants generated offline from `bridge/isa_bridge.h`.
- `src/generated/bytecode.rs` — a safe Rust `Bytecode` enum with per-instruction variants, operand newtypes (`Reg`/`Imm`/`EntityId`/`Label`), per-mnemonic constructors in `insn`, `BytecodeFlags`/`ExceptionType` bitflag sets, and `Bytecode::operands()` — generated offline by `templates/bytecode.rs.erb` from `vendor/arkcompiler_runtime_core/isa/isa.yaml`.

## Directory Structure

```
abcd-isa-sys/
├── build.rs                           # Pure cc::Build compiling 3 C++17 translation units
├── Cargo.toml                         # Depends only on `cc` at build time (zero bindgen/Ruby)
├── src/
│   ├── lib.rs                         # Re-exports src/generated/{bindings,bytecode}.rs + tests
│   └── generated/
│       ├── bindings.rs                # Pre-generated C FFI bindings for isa_bridge.h
│       └── bytecode.rs                # Pre-generated Rust Bytecode enum + flags + constructors
├── bridge/
│   ├── isa_bridge.h                   # C wrapper header (extern "C")
│   ├── isa_bridge.cpp                 # C wrapper implementation
│   ├── generated/
│   │   ├── isa_bridge_emit_dispatch.h # Pre-generated generic emitter dispatch switch
│   │   └── isa_bridge_valid_opcode.h  # Pre-generated opcode validity lookup tables
│   └── shim/                          # Crate-local stubs (shadowing real libpandafile headers)
│       ├── file.h                     # Minimal libpandafile/file.h stub (File::EntityId)
│       └── utils/
│           └── const_value.h          # Empty stub (include dep of file_format_version.h)
└── templates/
    ├── bytecode.rs.erb                # Custom: Rust Bytecode enum + flags + constructors
    ├── isa_bridge_emit_dispatch.h.erb # Custom: generic emitter dispatch switch
    └── isa_bridge_valid_opcode.h.erb  # Custom: opcode validity lookup

../vendor/                             # Shared workspace vendor snapshot & shims
├── UPSTREAM.toml                      # Upstream tag, commit SHA, and per-file SHA-256 manifest
├── arkcompiler_runtime_core/          # Curated upstream snapshot (isa, libpandafile, libpandabase, ...)
├── generated/                         # Pre-generated upstream C++ headers (bytecode_*_gen.h, ...)
└── shim/                              # Shared C++ shims (platform_compat.h, securec.h, logger.h, ...)
```

Upstream sources live in [`../vendor/arkcompiler_runtime_core/`](../vendor/arkcompiler_runtime_core) and are verified byte-for-byte against [`../vendor/UPSTREAM.toml`](../vendor/UPSTREAM.toml) in CI (`vendor-verify`) — never edit inside `vendor/arkcompiler_runtime_core/`. Local adaptation lives in `../vendor/shim/` (shared) and `bridge/shim/` (ISA-specific stubs). See [`../design/vendor-sync.md`](../design/vendor-sync.md).

## Build Pipeline Overview

### 1. Offline generation (`python3 scripts/vendor-gen.py codegen`, verified in CI by `vendor-verify`)

```
vendor/arkcompiler_runtime_core/isa/isa.yaml + bridge/isa_bridge.h
    │
    ├──► Ruby (gen.rb + isapi.rb + pandafile_isapi.rb)
    │       ├──► vendor/generated/bytecode_instruction_enum_gen.h
    │       ├──► vendor/generated/bytecode_instruction-inl_gen.h
    │       ├──► vendor/generated/bytecode_emitter_def_gen.h
    │       ├──► vendor/generated/bytecode_emitter_gen.h
    │       ├──► vendor/generated/file_format_version.h
    │       ├──► bridge/generated/isa_bridge_emit_dispatch.h
    │       ├──► bridge/generated/isa_bridge_valid_opcode.h
    │       └──► src/generated/bytecode.rs (+ rustfmt)
    │
    └──► C99 header parser on bridge/isa_bridge.h
            └──► src/generated/bindings.rs (+ rustfmt)
```

### 2. Ordinary `cargo build` (`build.rs`)

`build.rs` invokes only `cc::Build` to compile 3 C++17 translation units (`bridge/isa_bridge.cpp`, `vendor/arkcompiler_runtime_core/libpandafile/file_format_version.cpp`, and `vendor/arkcompiler_runtime_core/libpandafile/bytecode_emitter.cpp`) against the committed headers. No Ruby, `bindgen`, or `libclang` is invoked at build time.

### Comparison with arkcompiler's Original Build System

arkcompiler uses CMake/GN to drive Ruby code generation (`TemplateBasedGen.cmake`), consuming generated headers directly in C++ projects.

Our differences:

- Pre-generate all Ruby and FFI artifacts offline via `scripts/vendor-gen.py` and verify 100% reproducibility in CI (`vendor-verify`), keeping `cargo build` pure Rust + C++17 (`cc`).
- Use upstream C++ headers + minimal shims (`../vendor/shim/` + `bridge/shim/`) instead of heavy runtime dependencies.
- Added 3 custom templates: `bytecode.rs.erb` (the entire safe Rust ISA model), `isa_bridge_emit_dispatch.h.erb` (a single generic `isa_emitter_emit` instead of hundreds of per-mnemonic C functions), and `isa_bridge_valid_opcode.h.erb` (validity lookup backing safe decode).
- Compile with `-DNDEBUG` to eliminate C++ debug assertion runtime dependencies. Under NDEBUG the vendored `UNREACHABLE()` is `std::cerr + std::abort()`; the bridge therefore pre-validates opcodes before any vendored format lookup.
- All prefix detection uses `Inst::GetMinPrefixOpcodeIndex()` threshold — zero hardcoded constants.
- `BytecodeFlags`/`ExceptionType` are generated into `bytecode.rs` as Rust bitflags directly from `isa.yaml` properties/exceptions (no C `#define` mirror).

## Generated Code Artifacts

### `bytecode_instruction_enum_gen.h` (vendor template)

Injected into the `BytecodeInst` class body, generating the `Format`, `Opcode`, `Flags`, and `Exceptions` enums. 332 opcodes total:

- 226 non-prefixed instructions (primary byte `0x00`–`0xE1`),
- 4 prefix marker opcodes: `callruntime` (`0xFB`), `deprecated` (`0xFC`), `wide` (`0xFD`), `throw` (`0xFE`),
- 102 prefixed instructions.

Opcode values are encoded as `(sub_opcode << 8) | prefix_byte` for prefixed instructions; non-prefixed instructions use their first byte value.

### `bytecode_instruction-inl_gen.h` (vendor template)

Inline methods: `GetOpcode()`, `HasId/HasVReg/HasImm`, `Size(Format)`, typed `GetId/GetVReg/GetImm`, `HasFlag`, `operator<<`. The bridge calls these directly instead of reimplementing operand decoding on the C side.

### `isa_bridge_emit_dispatch.h` (custom template)

A single generic `isa_emitter_emit(e, opcode, args, num_args)` dispatch: switch over opcode → call the vendored emitter method with the correctly typed operands. Each operand is range-checked against the instruction's storage width before the call; an out-of-range operand fails with `ISA_EMIT_OPERAND_OUT_OF_RANGE` instead of silently truncating (audit finding #2). Jump instructions take a `label_id` operand resolved through the emitter's label vector; the label must be the last operand (verified against all jump formats upstream).

### `isa_bridge_valid_opcode.h` (custom template)

Opcode validity lookup backing `isa_is_primary_opcode_valid` and the prefixed sub-opcode ranges (derived from the vendored `isa_information` last-opcode indices). `isa_get_size_by_opcode` and the bytes-based decoders pre-validate through these tables and return 0 for invalid opcodes, so the vendored `GetFormat` `default:` arm (`UNREACHABLE()` → `std::abort()` under NDEBUG) is unreachable from the FFI surface (audit finding #1).

### `bytecode.rs` (custom template)

The safe Rust ISA model consumed directly by this crate's dependents: the `Bytecode` enum (one variant per instruction, typed operands), `insn` constructors, `BytecodeFlags`/`ExceptionType` bitflags, classification helpers (`is_jump`, `is_terminator`, `is_throw`, ...), and `Bytecode::operands()` (typed `Operand::Reg/Imm/Entity/Label` views used by the per-instruction pandasm comparison test in `abcd-file`).

## C Bridge API Design

`bridge/isa_bridge.h` + `bridge/isa_bridge.cpp`

Design principles:

1. Pure C99 interface (`extern "C"`).
2. **Every entry point is exception-guarded**: C++ exceptions (`bad_alloc`, vendored aborts reachable through allocation paths) are converted to sentinel returns, never propagated across the FFI (audit findings #11/#12; 34 exported functions).
3. Decode/metadata functions are stateless and thread-safe; the emitter is stateful.
4. Sentinel conventions:
   - `SIZE_MAX` — decode/size failures (`ISA_NO_LITERAL_INDEX` for literal-index queries).
   - `isa_emitter_emit` return codes: `ISA_EMIT_OK` (0), `ISA_EMIT_INVALID_LABEL` (-1), `ISA_EMIT_TOO_FEW_ARGS` (-2), `ISA_EMIT_UNKNOWN_OPCODE` (-3), `ISA_EMIT_OPERAND_OUT_OF_RANGE` (-4), `ISA_EMIT_INTERNAL_ERROR` (-5; C++ exception escaped into the guard).
   - `isa_emitter_build` return codes: `ISA_BUILD_OK` (0), `ISA_BUILD_INTERNAL_ERROR` (1), `ISA_BUILD_UNBOUND_LABELS` (2).
   - Version lookups (`isa_get_version_by_api`, `isa_get_version_by_api_sub`): 0 = success, 1 = not found.
   - Boolean queries return 1/0.

### Decode Layer

```c
uint16_t isa_get_opcode(const uint8_t* bytes);
uint8_t  isa_get_format(uint16_t opcode);
size_t   isa_get_size_by_opcode(uint16_t opcode);   // 0 for invalid opcodes (pre-validated)
size_t   isa_get_size_from_bytes(const uint8_t* bytes);
int      isa_is_primary_opcode_valid(uint8_t primary);
```

### Operand Extraction Layer

```c
uint16_t isa_get_vreg(const uint8_t* bytes, size_t idx);
int64_t  isa_get_imm64(const uint8_t* bytes, size_t idx);
uint32_t isa_get_id(const uint8_t* bytes, size_t idx);
int      isa_has_vreg/isa_has_imm/isa_has_id(uint8_t format, size_t idx);
int64_t  isa_get_imm_data(const uint8_t* bytes, size_t idx);  // signedness per opcode
void     isa_update_id(uint8_t* bytes, uint32_t new_id, uint32_t idx);  // relocation patching
```

### Classification

Opcode-based queries needing no instruction bytes (`isa_is_jump_opcode`, `isa_can_throw_opcode`, `isa_is_terminator_opcode`, `isa_is_suspend_opcode`, `isa_is_range_opcode`, `isa_is_throw_ex_opcode`, `isa_has_flag_opcode`, `isa_is_id_string_opcode`, `isa_is_id_method_opcode`, `isa_is_id_literal_array_opcode`). All pre-validate the opcode and delegate to the vendored generated methods.

### Version API

```c
void   isa_get_version(uint8_t out[4]);
void   isa_get_min_version(uint8_t out[4]);
int    isa_get_version_by_api(uint8_t api_level, uint8_t out[4]);
int    isa_get_version_by_api_sub(uint8_t api_level, const char* sub_api, uint8_t out[4]);
int    isa_is_version_compatible(const uint8_t ver[4]);
// + incompatible-version enumeration
```

### Emitter API

```c
IsaEmitter* isa_emitter_create(void);
void        isa_emitter_destroy(IsaEmitter* e);
uint32_t    isa_emitter_create_label(IsaEmitter* e);
int         isa_emitter_bind(IsaEmitter* e, uint32_t label_id);   // 0 ok, -1 invalid label
int         isa_emitter_emit(IsaEmitter* e, uint16_t opcode,
                             const int64_t* args, size_t num_args);  // generic dispatch
int         isa_emitter_build(IsaEmitter* e, uint8_t** out_buf, size_t* out_len);
void        isa_emitter_free_buf(uint8_t* buf);
```

`IsaEmitter` internally holds a C++ `BytecodeEmitter` + `vector<Label>`.

## Build Dependencies

- **Ordinary `cargo build` / `cargo test`**: C++17 compiler + `cc` crate only.
- **Offline binding regeneration (`scripts/vendor-gen.py`)**: Python 3 + Ruby 2.5+ + `rustfmt`.

## Statistics

- 332 opcodes: 226 non-prefixed (`0x00`–`0xE1`) + 4 prefix markers (`0xFB`–`0xFE`) + 102 prefixed
- ~80 instruction formats; 4 prefixes: `callruntime` (`0xFB`), `deprecated` (`0xFC`), `wide` (`0xFD`), `throw` (`0xFE`)
- C++ compiles 3 source files: `bridge/isa_bridge.cpp` + vendor `file_format_version.cpp` + `bytecode_emitter.cpp`
- C bridge exports 34 functions (see `bridge/isa_bridge.h`)
- `BytecodeFlags`: 30 property flags + `ExceptionType`: 14 exception flags (generated by `bytecode.rs.erb` from `isa.yaml`)

## Publishing

This crate is unpublished; its `build.rs` references the shared workspace `../vendor/` directory (`1.8 MB`). If standalone crates.io publishing is ever desired, staging `vendor/` inside the crate package at release time is straightforward since all codegen artifacts are already pre-generated and submodule-free.
