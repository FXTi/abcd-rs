# Vendor Snapshot & Codegen Maintenance (`vendor/`)

`abcd-rs` embeds a minimal, test-stripped snapshot of upstream `arkcompiler_runtime_core` (`libpandafile`, `libpandabase`, `isa/isa.yaml`, and Ruby `.erb` ISA templates) under `vendor/` so `cargo build` requires only a standard C++17 compiler (`cc::Build`)—with **zero Git submodules, zero `bindgen`/`libclang`, and zero build-time Ruby**.

---

## 1. Directory Layout

| Path | Contents & Ownership |
| :--- | :--- |
| `vendor/UPSTREAM.toml` | Pinned upstream repository URL, release tag/commit (`OpenHarmony-v7.0-Release`), and per-file SHA-256 manifest |
| `vendor/arkcompiler_runtime_core/` | Read-only upstream C++/YAML/ERB snapshot (`336` files, `~1.84 MB`); **never hand-edit** |
| `vendor/shim/` | Minimal cross-platform C++ shims (`platform_compat.h`, `utils/logger.h` silent sink + `FATAL` exception throw) |
| `vendor/generated/` | Pre-generated upstream C++ ISA/version headers + `file_bridge_enum_checks.h` (`109` C++17 `static_assert`s) |
| `abcd-isa-sys/src/generated/`, `abcd-isa/src/generated/`, `abcd-file-sys/src/generated/` | Pre-generated Rust ISA tables, FFI `extern "C"` signatures, and enum/flag bindings |
| `scripts/vendor-gen.py` | Offline maintenance tool (`sync`, `codegen`, `verify`) |

---

## 2. Standard Maintenance Workflows

### Modifying `isa_bridge.h` or `file_bridge.h`
Whenever a C99 signature, struct, or enum in `abcd-isa-sys/bridge/isa_bridge.h` or `abcd-file-sys/bridge/file_bridge.h` changes:

```sh
python3 scripts/vendor-gen.py codegen
python3 scripts/vendor-gen.py verify
./scripts/test-local.sh full
```

`codegen` re-parses the C99 bridge headers and upstream enum headers, regenerates `ffi_bindings.rs` and `file_bridge_enum_checks.h`, formats with `rustfmt`, and `verify` confirms zero drift.

### Syncing to a Newer Upstream OpenHarmony Release
1. Point `scripts/vendor-gen.py sync` at a local checkout of the target `arkcompiler_runtime_core` tag:
   ```sh
   python3 scripts/vendor-gen.py sync --upstream /path/to/arkcompiler_runtime_core --ref OpenHarmony-vX.Y-Release
   python3 scripts/vendor-gen.py codegen
   python3 scripts/vendor-gen.py verify
   ```
2. Compile and run `./scripts/test-local.sh all`:
   - Any upstream C++ enum discriminant or `AccessFlags` bit shift fails at compile time via `vendor/generated/file_bridge_enum_checks.h`.
   - Any new `isa.yaml` opcode surfaces as a compile-time non-exhaustive `Bytecode` match in `abcd-isa` / `abcd-lift`—audit its runtime semantics in `arkcompiler_ets_runtime` before mapping it into `abcd-ir` (`ADR-06`, `ADR-07`).
3. Push and verify all `26` CI jobs (including cross-OS, 32-bit, ASan, `pandasm` byte-identity, and VM oracles).
