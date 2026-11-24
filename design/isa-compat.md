# ISA & Format Version Compatibility

ArkCompiler `.abc` files carry a 4-byte format version tuple `M.m.p.b` in the container header. `abcd-rs` handles dynamic ECMAScript/ArkTS 1.1 versions across OpenHarmony 3.2 through 7.0 (`API 9`–`24`) and schedules static ArkTS 1.2 (`0.1.0.7`) in `#36`.

---

## 1. Dynamic ISA Stability (`9.0.0.0` – `24.0.0.0`)

Across modern dynamic versions (`9.0.0.0`, `11.0.2.0`, `12.0.2.0`, `12.0.6.0`, `13.0.1.0`, `24.0.0.0`):
1. **Additive Opcode Evolution**: Existing opcode byte assignments and operand layouts remain backward-compatible across `9.0.0.0` → `24.0.0.0`; newer SDK releases add prefixed extensions (e.g., `callruntime.*` sendable/lazy-module ops) without renumbering prior opcodes.
2. **Container Layout Differences Live in `abcd-file`**: Version differences between `9.0.0.0`/`12.x` and `13.x`/`24.0.0.0` reside in the `.abc` container header and record conventions (e.g., header literal-array index table removal in `13.0.1.0+`, `--merge-abc` per-record `moduleRecordIdx`/`scopeNames` fields, and es2panda `#*#` internal method name mangling in `12.0.6.0+`), handled transparently in `abcd-file` and `abcd-lift`.
3. **Output Version Selection**: `abcd_file::Builder::set_file_version` delegates directly to vendored `GetVersionByApi` / `api_version_map` so emitted `.abc` headers match upstream `es2abc` byte-for-byte.

---

## 2. Legacy Pre-Freeze Format (`0.0.0.2`)

Early OpenHarmony 3.2 / 4.0 system applications carry header version `0.0.0.2`, which predates the `9.0.0.0` opcode freeze and uses a distinct `ecma.*` prefixed opcode numbering plus a file-end global literal-array offset table:
- **Decode & Analysis**: `abcd-file::decode` automatically dispatches `0.0.0.2` methods through `abcd_isa::decode_legacy` and resolves global literal-array indices into `MethodBody::entity_offsets`, allowing `abcd-lift`, `abcd-analysis`, `abcd-taint`, `abcd-decompile`, and `abcd dis` to operate seamlessly across all legacy wild `.hap` packages (`ADR-08`).
- **Write Boundary**: Upstream `libpandafile`'s writer does not emit `0.0.0.2` containers; `abcd_file::encode` returns `Error::UnsupportedOutputVersion(0.0.0.2)` unless lowered onto a modern target version (`9.0.0.0`–`24.0.0.0`).

---

## 3. Static ArkTS 1.2 Format (`0.1.0.7`, Roadmap `#36`)

ArkTS 1.2 (`ets2panda` / `static_core`) emits statically typed Panda bytecode under header version `0.1.0.7`:
- Uses typed register/accumulator instructions (`lda.str`, `ldai.64`, `call.short` / `call.virt`, typed array/object ops) without dynamic JS `[func][new.target][this]` hidden frame slots (`H = 0`).
- Tracked in [`#36`](https://github.com/FXTi/abcd-rs/issues/36) to extend container/ISA decoding, `abcd-ir` static calling-convention & typed op lowering/lifting, static analysis, and decompilation.
