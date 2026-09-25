# Bridge/Shim Surface Analysis: Dead Code and Live-Surface Completeness (q-P1)

Date: 2026-09-25 · Worker: q-P1 (read-only analysis) · Scope:
`abcd-isa-sys/bridge/**`, `abcd-file-sys/bridge/**` (OUR C++), consumed from Rust
via the two sys crates' bindgen output. Vendored submodule contents
(`*/arkcompiler_runtime_core/`, pinned `OpenHarmony-v7.0-Release`, commit
`4fba38e`) are out of scope and untouched.

Commissioning context: MEMORY.md 2026-09-25 ruling — "bridge C++ STAYS in the
denominator … the provably-dead surface gets DELETED (q-P1), not excluded",
superseding D3 (2026-09-20, "keep the dead FFI surface"). This report is the
quantification + completeness proof that ruling asks for.

## 0. Method

1. **Export inventory (source parse).** Every `extern "C"` function declared in
   `abcd-isa-sys/bridge/isa_bridge.h` and `abcd-file-sys/bridge/file_bridge.h`
   was extracted and cross-checked against the definitions in
   `isa_bridge.cpp` / `file_bridge.cpp`. Result: **332 exports** (59 `isa_*`,
   273 `abc_*`). The two `.cpp` files define exactly the header set — the only
   additional `abc_*` identifiers in `file_bridge.cpp` are three `static`
   internal helpers (`abc_literal_enumerate_vals_tolerant` file_bridge.cpp:1882,
   `abc_builder_flush_literal_staging` :3293, `abc_builder_flush_lnp_staging`
   :3301), which are not exported. No exported data symbols exist. The `shim/`
   headers define no exported (non-`static`) functions — they are compile-time
   compatibility headers only.
   Object-level `nm` confirmation was *not* run (optional per the task; a local
   build of the sys crates is enough to confirm linkage and was not needed for
   a source-level truth claim). Flagged as *unverified at object level*: macro-
   or linkage-level surprises are theoretically possible but none are plausible
   here — every export is a plain `extern "C"` function definition.
2. **Rust-side usage map (grep + read).** Every export name was searched
   (`\b<name>\b`) across all tracked `*.rs` and `*.erb` files
   (`git ls-files`), excluding `target/`. The bindgen-generated
   `bindings.rs` lives in `OUT_DIR` (target/) and *declares* every export for
   both crates (abcd-isa-sys/build.rs:188-200 allowlists `isa_.*`/`Isa.*`/
   `ISA_.*`; abcd-file-sys/build.rs:195-205 allowlists `abc_.*`/`Abc.*`/
   `ABC_.*`), so a bindgen declaration alone is **not** evidence of use — only
   hand-written or template-generated (`abcd-isa-sys/templates/bytecode.rs.erb`)
   call sites count. The sys crates suppress unused-binding warnings with
   `#![allow(dead_code)]` (abcd-isa-sys/src/lib.rs:16-21,
   abcd-file-sys/src/lib.rs:1-6).
3. **Classification.** LIVE = ≥1 reference from non-test Rust (any workspace
   crate; templates count as live — they generate `bytecode.rs`). TEST-ONLY =
   referenced only inside `#[cfg(test)]` modules or `*/tests/` trees.
   CFG-GATED = reachable only under a cargo feature — **the workspace has no
   feature gates at all** (no `[features]` in any member `Cargo.toml`, no
   `cfg(feature` in the consuming crates), so this class is empty.
   DEAD = zero references anywhere.

Workspace members (Cargo.toml:3-14): abcd-isa-sys, abcd-isa, abcd-file-sys,
abcd-file, abcd-ir, abcd-lift, abcd-lower, abcd-opt, abcd-analysis,
abcd-taint, abcd-decompile. Only abcd-isa and abcd-file consume the sys
crates (grep for `abcd_isa_sys`/`abcd_file_sys` across all `*.rs` hits only
those two crates' `src/` and `tests/`); downstream crates see only the safe
re-exports (abcd-isa/src/lib.rs:34-47, abcd-file/src/lib.rs:41-67).

## 1. Export inventory

332 exports. Columns: export · header declaration (file:line) · cpp definition
(file:line) · class (§3) · Rust consumer(s) (first two; empty for DEAD) ·
purpose (from the header doc comment). `isa_*` header = `isa_bridge.h`,
cpp = `isa_bridge.cpp`; `abc_*` header = `file_bridge.h`, cpp =
`file_bridge.cpp` (paths abbreviated; all under the respective crate's
`bridge/`).

| Export | Header decl | cpp def | Class | Rust consumer(s) | Purpose |
|---|---|---|---|---|---|
| `isa_get_format` | isa_bridge.h:29 | isa_bridge.cpp:40 | LIVE | abcd-isa/src/relocation.rs:34 | Get instruction format for an opcode. |
| `isa_get_size` | isa_bridge.h:32 | isa_bridge.cpp:50 | DEAD |  | Get instruction size in bytes. |
| `isa_is_prefixed` | isa_bridge.h:35 | isa_bridge.cpp:58 | DEAD |  | Check if opcode is prefixed (2-byte opcode). |
| `isa_get_opcode` | isa_bridge.h:38 | isa_bridge.cpp:66 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:427,abcd-isa/src/decoder.rs:49 | Extract full opcode value from bytecode. |
| `isa_get_format_from_bytes` | isa_bridge.h:41 | isa_bridge.cpp:75 | DEAD |  | Get format directly from bytecode. |
| `isa_get_size_from_bytes` | isa_bridge.h:44 | isa_bridge.cpp:85 | LIVE | abcd-isa/src/emitter.rs:142,abcd-isa/src/emitter.rs:144 | Get instruction size directly from bytecode. |
| `isa_get_size_by_opcode` | isa_bridge.h:47 | isa_bridge.cpp:95 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:426,abcd-isa/src/decoder.rs:51 | Get instruction size by opcode. |
| `isa_get_vreg` | isa_bridge.h:52 | isa_bridge.cpp:104 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:450 | Get virtual register operand at index. |
| `isa_get_imm64` | isa_bridge.h:55 | isa_bridge.cpp:114 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:447 | Get signed 64-bit immediate operand at index. |
| `isa_get_id` | isa_bridge.h:58 | isa_bridge.cpp:124 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:452,abcd-isa/src/relocation.rs:42 | Get entity ID operand at index. |
| `isa_has_vreg` | isa_bridge.h:61 | isa_bridge.cpp:134 | DEAD |  | Query if format has vreg/imm/id at index. |
| `isa_has_imm` | isa_bridge.h:62 | isa_bridge.cpp:142 | DEAD |  |  |
| `isa_has_id` | isa_bridge.h:63 | isa_bridge.cpp:150 | LIVE | abcd-isa/src/relocation.rs:35 |  |
| `isa_can_throw` | isa_bridge.h:66 | isa_bridge.cpp:158 | DEAD |  | === Classification from bytecode (delegates to upstream generated methods) |
| `isa_is_terminator` | isa_bridge.h:67 | isa_bridge.cpp:168 | DEAD |  |  |
| `isa_is_return_or_throw` | isa_bridge.h:68 | isa_bridge.cpp:178 | DEAD |  |  |
| `isa_has_flag` | isa_bridge.h:71 | isa_bridge.cpp:188 | DEAD |  | Check if instruction has a specific property flag. |
| `isa_is_throw_ex` | isa_bridge.h:74 | isa_bridge.cpp:198 | DEAD |  | Check if instruction throws a specific exception type. |
| `isa_is_jump` | isa_bridge.h:77 | isa_bridge.cpp:208 | DEAD |  | Check if instruction is a jump. |
| `isa_is_range` | isa_bridge.h:80 | isa_bridge.cpp:218 | DEAD |  | Check if instruction is a range instruction. |
| `isa_is_suspend` | isa_bridge.h:83 | isa_bridge.cpp:228 | DEAD |  | Check if instruction is a suspend point (generator/async yield). |
| `isa_is_jump_opcode` | isa_bridge.h:86 | isa_bridge.cpp:251 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:239 | === Opcode-based classification (no operand bytes needed) === |
| `isa_can_throw_opcode` | isa_bridge.h:87 | isa_bridge.cpp:260 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:244 |  |
| `isa_is_terminator_opcode` | isa_bridge.h:88 | isa_bridge.cpp:269 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:249 |  |
| `isa_has_flag_opcode` | isa_bridge.h:89 | isa_bridge.cpp:278 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:259 |  |
| `isa_is_range_opcode` | isa_bridge.h:90 | isa_bridge.cpp:287 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:264 |  |
| `isa_is_return_or_throw_opcode` | isa_bridge.h:91 | isa_bridge.cpp:296 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:269 |  |
| `isa_is_suspend_opcode` | isa_bridge.h:92 | isa_bridge.cpp:305 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:274 |  |
| `isa_is_throw_ex_opcode` | isa_bridge.h:93 | isa_bridge.cpp:314 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:284 |  |
| `isa_format_opcode_name` | isa_bridge.h:96 | isa_bridge.cpp:323 | DEAD |  | Format opcode mnemonic name (e.g. "mov" for MOV_V4_V4). Returns bytes written. |
| `isa_min_prefix_opcode` | isa_bridge.h:99 | isa_bridge.cpp:385 | LIVE | abcd-isa/src/decoder.rs:39,abcd-isa/src/relocation.rs:23 | === Constants and prefix queries === |
| `isa_is_primary_opcode_valid` | isa_bridge.h:100 | isa_bridge.cpp:394 | DEAD |  |  |
| `isa_get_imm_data` | isa_bridge.h:105 | isa_bridge.cpp:406 | LIVE | abcd-isa-sys/templates/bytecode.rs.erb:454 | Get immediate with correct signedness per opcode (signed/unsigned/float). |
| `isa_get_imm_count` | isa_bridge.h:108 | isa_bridge.cpp:416 | DEAD |  | Get number of immediate operands. |
| `isa_get_literal_index` | isa_bridge.h:111 | isa_bridge.cpp:426 | DEAD |  | Get literal array index for instructions with LITERALARRAY_ID. Returns ISA_NO_LITERAL_INDEX if none. |
| `isa_update_id` | isa_bridge.h:114 | isa_bridge.cpp:436 | LIVE | abcd-isa/src/relocation.rs:41 | Write a new entity ID at the given index (bytecode patching). |
| `isa_get_last_vreg` | isa_bridge.h:117 | isa_bridge.cpp:450 | DEAD |  | Get last virtual register. Returns -1 if no vreg. |
| `isa_get_range_last_reg_idx` | isa_bridge.h:120 | isa_bridge.cpp:461 | DEAD |  | Get last register index for range instructions. Returns -1 if not applicable. |
| `isa_is_id_string` | isa_bridge.h:123 | isa_bridge.cpp:472 | DEAD |  | Type-safe ID operand classification. |
| `isa_is_id_method` | isa_bridge.h:124 | isa_bridge.cpp:482 | DEAD |  |  |
| `isa_is_id_literal_array` | isa_bridge.h:125 | isa_bridge.cpp:492 | DEAD |  |  |
| `isa_format_instruction` | isa_bridge.h:128 | isa_bridge.cpp:340 | DEAD |  | Format instruction as string. Returns bytes written. |
| `isa_format_opcode` | isa_bridge.h:132 | isa_bridge.cpp:364 | DEAD |  | Format opcode name as string (e.g. "MOV_V4_V4"). Returns bytes written. |
| `isa_get_version` | isa_bridge.h:137 | isa_bridge.cpp:506 | LIVE | abcd-isa/src/version.rs:61 | Write the current .abc file version (4 bytes) into out. |
| `isa_get_min_version` | isa_bridge.h:140 | isa_bridge.cpp:514 | LIVE | abcd-isa/src/version.rs:69 | Write the minimum supported .abc file version (4 bytes) into out. |
| `isa_get_api_version_count` | isa_bridge.h:143 | isa_bridge.cpp:522 | DEAD |  | Number of entries in the api_version_map. |
| `isa_get_version_by_api` | isa_bridge.h:146 | isa_bridge.cpp:530 | LIVE | abcd-isa/src/version.rs:98 | Lookup file version by API level. Returns 0 on success, 1 if not found. |
| `isa_is_version_compatible` | isa_bridge.h:149 | isa_bridge.cpp:541 | LIVE | abcd-isa/src/version.rs:80 | Check if a version is compatible (>= min_version && <= version). Returns 1 if compatible. |
| `isa_incompatible_version_count` | isa_bridge.h:152 | isa_bridge.cpp:551 | LIVE | abcd-isa/src/version.rs:122 | Number of incompatible versions. |
| `isa_incompatible_version_at` | isa_bridge.h:155 | isa_bridge.cpp:559 | LIVE | abcd-isa/src/version.rs:127 | Get incompatible version at index. |
| `isa_is_version_incompatible` | isa_bridge.h:158 | isa_bridge.cpp:571 | LIVE | abcd-isa/src/version.rs:89 | Check if a version is in the incompatible set. Returns 1 if incompatible. |
| `isa_get_version_by_api_sub` | isa_bridge.h:161 | isa_bridge.cpp:580 | LIVE | abcd-isa/src/version.rs:114 | Lookup file version by API level with sub-API string. Returns 0 on success. |
| `isa_emitter_create` | isa_bridge.h:166 | isa_bridge.cpp:594 | LIVE | abcd-isa/src/emitter.rs:69,abcd-isa/src/emitter.rs:78 |  |
| `isa_emitter_destroy` | isa_bridge.h:167 | isa_bridge.cpp:602 | LIVE | abcd-isa/src/emitter.rs:79 |  |
| `isa_emitter_create_label` | isa_bridge.h:169 | isa_bridge.cpp:610 | LIVE | abcd-isa/src/emitter.rs:86 |  |
| `isa_emitter_bind` | isa_bridge.h:172 | isa_bridge.cpp:620 | LIVE | abcd-isa/src/emitter.rs:93,abcd-isa/src/emitter.rs:97 | Bind a label to the current emit position. Returns 0 on success, -1 if label_id is invalid. |
| `isa_emitter_build` | isa_bridge.h:175 | isa_bridge.cpp:630 | LIVE | abcd-isa/src/emitter.rs:126,abcd-isa/src/emitter.rs:130 | Build: returns ISA_BUILD_OK, ISA_BUILD_INTERNAL_ERROR, or ISA_BUILD_UNBOUND_LABELS. |
| `isa_emitter_free_buf` | isa_bridge.h:176 | isa_bridge.cpp:653 | LIVE | abcd-isa/src/emitter.rs:133 |  |
| `isa_emitter_emit` | isa_bridge.h:182 | isa_bridge.cpp:661 | LIVE | abcd-isa-sys/templates/isa_bridge_emit_dispatch.h.erb:2,abcd-isa/src/emitter.rs:111 |  |
| `abc_file_open` | file_bridge.h:50 | file_bridge.cpp:395 | LIVE | abcd-file/src/file.rs:23 |  |
| `abc_file_close` | file_bridge.h:51 | file_bridge.cpp:436 | LIVE | abcd-file/src/file.rs:60 |  |
| `abc_file_open_error` | file_bridge.h:53 | file_bridge.cpp:387 | LIVE | abcd-file/src/file.rs:25,abcd-file/src/file.rs:27 | Reason for the last failed abc_file_open (thread-local; empty on success). |
| `abc_file_num_classes` | file_bridge.h:56 | file_bridge.cpp:444 | LIVE | abcd-file/src/decode.rs:76 | Header access |
| `abc_file_class_offset` | file_bridge.h:57 | file_bridge.cpp:452 | LIVE | abcd-file/src/decode.rs:78,abcd-file/src/decode.rs:141 |  |
| `abc_file_num_literalarrays` | file_bridge.h:58 | file_bridge.cpp:462 | LIVE | abcd-file/src/decode.rs:1518 |  |
| `abc_file_literalarray_offset` | file_bridge.h:59 | file_bridge.cpp:475 | LIVE | abcd-file/src/decode.rs:1522 |  |
| `abc_file_literalarray_idx_off` | file_bridge.h:60 | file_bridge.cpp:485 | DEAD |  |  |
| `abc_file_size` | file_bridge.h:61 | file_bridge.cpp:493 | LIVE | abcd-file/src/file.rs:54 |  |
| `abc_file_version` | file_bridge.h:64 | file_bridge.cpp:501 | LIVE | abcd-file/src/file.rs:41 | Version from header |
| `abc_file_get_string` | file_bridge.h:67 | file_bridge.cpp:510 | LIVE | abcd-file/src/file.rs:104,abcd-file/src/file.rs:110 | String access: returns bytes written, 0 on error |
| `abc_file_get_string_utf16` | file_bridge.h:75 | file_bridge.cpp:529 | LIVE | abcd-file/src/file.rs:83,abcd-file/src/file.rs:94 |  |
| `abc_resolve_method_index` | file_bridge.h:79 | file_bridge.cpp:544 | DEAD |  | Index resolution: returns offset, UINT32_MAX on error |
| `abc_resolve_class_index` | file_bridge.h:80 | file_bridge.cpp:554 | LIVE | abcd-file/src/decode.rs:1995 |  |
| `abc_resolve_field_index` | file_bridge.h:81 | file_bridge.cpp:564 | DEAD |  |  |
| `abc_resolve_proto_index` | file_bridge.h:82 | file_bridge.cpp:574 | DEAD |  |  |
| `abc_file_get_class_id` | file_bridge.h:85 | file_bridge.cpp:584 | TEST-ONLY | abcd-file-sys/src/lib.rs:595,abcd-file-sys/src/lib.rs:813 | Class lookup by MUTF-8 name: returns offset, UINT32_MAX if not found |
| `abc_file_is_external` | file_bridge.h:87 | file_bridge.cpp:594 | LIVE | abcd-file/src/file.rs:118 | Check if entity is in the foreign section |
| `abc_foreign_item_name_off` | file_bridge.h:91 | file_bridge.cpp:602 | LIVE | abcd-file/src/decode.rs:945 |  |
| `abc_file_get_string_utf16_len` | file_bridge.h:93 | file_bridge.cpp:629 | DEAD |  | String metadata |
| `abc_file_get_string_is_ascii` | file_bridge.h:94 | file_bridge.cpp:638 | DEAD |  |  |
| `abc_file_validate_checksum` | file_bridge.h:96 | file_bridge.cpp:647 | TEST-ONLY | abcd-file-sys/src/lib.rs:229 | Checksum validation: 1 = valid |
| `abc_file_get_type` | file_bridge.h:99 | file_bridge.cpp:655 | LIVE | abcd-file/src/file.rs:69 | File type: -1 = invalid, 0 = dynamic, 1 = static |
| `abc_file_get_raw_data` | file_bridge.h:102 | file_bridge.cpp:663 | DEAD |  | Raw data pointer (File::GetBase) |
| `abc_file_num_index_headers` | file_bridge.h:117 | file_bridge.cpp:671 | DEAD |  |  |
| `abc_file_get_index_header` | file_bridge.h:118 | file_bridge.cpp:679 | DEAD |  |  |
| `abc_resolve_offset_by_index` | file_bridge.h:122 | file_bridge.cpp:703 | LIVE | abcd-file/src/decode.rs:282 | Resolve by generic index: returns offset, UINT32_MAX on error |
| `abc_resolve_lnp_index` | file_bridge.h:124 | file_bridge.cpp:713 | DEAD |  | Resolve line number program index: returns offset, UINT32_MAX on error |
| `abc_file_checksum` | file_bridge.h:127 | file_bridge.cpp:725 | LIVE | abcd-file/src/file.rs:48 | Additional header fields |
| `abc_file_foreign_off` | file_bridge.h:128 | file_bridge.cpp:733 | TEST-ONLY | abcd-file-sys/src/lib.rs:481 |  |
| `abc_file_foreign_size` | file_bridge.h:129 | file_bridge.cpp:741 | TEST-ONLY | abcd-file-sys/src/lib.rs:482 |  |
| `abc_file_class_idx_off` | file_bridge.h:130 | file_bridge.cpp:749 | DEAD |  |  |
| `abc_file_num_lnps` | file_bridge.h:131 | file_bridge.cpp:757 | DEAD |  |  |
| `abc_file_lnp_idx_off` | file_bridge.h:132 | file_bridge.cpp:765 | DEAD |  |  |
| `abc_file_index_section_off` | file_bridge.h:133 | file_bridge.cpp:773 | DEAD |  |  |
| `abc_get_current_version` | file_bridge.h:138 | file_bridge.cpp:783 | DEAD |  | Get compile-time version / minVersion constants |
| `abc_get_min_version` | file_bridge.h:139 | file_bridge.cpp:792 | DEAD |  |  |
| `abc_is_version_less_or_equal` | file_bridge.h:141 | file_bridge.cpp:801 | DEAD |  | Version comparison: 1 if current <= target |
| `abc_contains_literal_array_in_header` | file_bridge.h:143 | file_bridge.cpp:811 | DEAD |  | 1 if version contains literal array in header |
| `abc_proto_open` | file_bridge.h:149 | file_bridge.cpp:822 | LIVE | abcd-file/src/decode.rs:1043 |  |
| `abc_proto_close` | file_bridge.h:150 | file_bridge.cpp:830 | LIVE | abcd-file/src/decode.rs:1047 |  |
| `abc_proto_num_args` | file_bridge.h:151 | file_bridge.cpp:838 | LIVE | abcd-file/src/decode.rs:1077 |  |
| `abc_proto_get_return_type` | file_bridge.h:152 | file_bridge.cpp:854 | LIVE | abcd-file/src/decode.rs:1074 |  |
| `abc_proto_get_arg_type` | file_bridge.h:153 | file_bridge.cpp:862 | LIVE | abcd-file/src/decode.rs:1080 |  |
| `abc_proto_get_reference_type` | file_bridge.h:154 | file_bridge.cpp:870 | LIVE | abcd-file/src/decode.rs:1052 |  |
| `abc_proto_get_ref_num` | file_bridge.h:155 | file_bridge.cpp:878 | LIVE | abcd-file/src/decode.rs:1049 |  |
| `abc_proto_enumerate_types` | file_bridge.h:158 | file_bridge.cpp:886 | TEST-ONLY | abcd-file/tests/proto_queries.rs:46 |  |
| `abc_proto_get_shorty` | file_bridge.h:160 | file_bridge.cpp:897 | DEAD |  | Shorty descriptor: returns length, sets *out_data to internal buffer |
| `abc_proto_get_size` | file_bridge.h:161 | file_bridge.cpp:907 | DEAD |  |  |
| `abc_proto_is_equal` | file_bridge.h:162 | file_bridge.cpp:915 | DEAD |  |  |
| `abc_proto_get_proto_id` | file_bridge.h:164 | file_bridge.cpp:923 | DEAD |  | Proto entity ID |
| `abc_class_open` | file_bridge.h:170 | file_bridge.cpp:933 | LIVE | abcd-file/src/decode.rs:92,abcd-file/src/decode.rs:169 |  |
| `abc_class_close` | file_bridge.h:171 | file_bridge.cpp:941 | LIVE | abcd-file/src/decode.rs:96,abcd-file/src/decode.rs:173 |  |
| `abc_class_super_class_off` | file_bridge.h:172 | file_bridge.cpp:949 | LIVE | abcd-file/src/decode.rs:232 |  |
| `abc_class_access_flags` | file_bridge.h:173 | file_bridge.cpp:957 | LIVE | abcd-file/src/decode.rs:218 |  |
| `abc_class_num_fields` | file_bridge.h:174 | file_bridge.cpp:965 | DEAD |  |  |
| `abc_class_num_methods` | file_bridge.h:175 | file_bridge.cpp:973 | DEAD |  |  |
| `abc_class_size` | file_bridge.h:176 | file_bridge.cpp:981 | DEAD |  |  |
| `abc_class_source_file_off` | file_bridge.h:178 | file_bridge.cpp:989 | LIVE | abcd-file/src/decode.rs:223 | Returns source file entity offset, UINT32_MAX if absent |
| `abc_class_enumerate_methods` | file_bridge.h:182 | file_bridge.cpp:999 | LIVE | abcd-file/src/decode.rs:102,abcd-file/src/decode.rs:187 |  |
| `abc_class_enumerate_fields` | file_bridge.h:186 | file_bridge.cpp:1009 | LIVE | abcd-file/src/decode.rs:113,abcd-file/src/decode.rs:193 |  |
| `abc_class_get_ifaces_number` | file_bridge.h:189 | file_bridge.cpp:1019 | LIVE | abcd-file/src/decode.rs:240 | Interfaces |
| `abc_class_get_interface_id` | file_bridge.h:190 | file_bridge.cpp:1027 | LIVE | abcd-file/src/decode.rs:243 |  |
| `abc_class_enumerate_interfaces` | file_bridge.h:192 | file_bridge.cpp:1035 | DEAD |  | cb return value DISCARDED (no early stop — see the contract block above). |
| `abc_class_get_source_lang` | file_bridge.h:195 | file_bridge.cpp:1045 | LIVE | abcd-file/src/decode.rs:220 | Source language: returns SourceLang value, UINT8_MAX if absent |
| `abc_class_enumerate_annotations` | file_bridge.h:200 | file_bridge.cpp:1055 | LIVE | abcd-file/src/decode.rs:1101 |  |
| `abc_class_enumerate_runtime_annotations` | file_bridge.h:201 | file_bridge.cpp:1065 | LIVE | abcd-file/src/decode.rs:1107 |  |
| `abc_class_enumerate_type_annotations` | file_bridge.h:204 | file_bridge.cpp:1075 | LIVE | abcd-file/src/decode.rs:1113 | Class type annotations |
| `abc_class_enumerate_runtime_type_annotations` | file_bridge.h:205 | file_bridge.cpp:1085 | LIVE | abcd-file/src/decode.rs:1119 |  |
| `abc_class_get_annotations_number` | file_bridge.h:208 | file_bridge.cpp:1095 | DEAD |  | Class annotation counts and ID |
| `abc_class_get_runtime_annotations_number` | file_bridge.h:209 | file_bridge.cpp:1103 | DEAD |  |  |
| `abc_class_get_class_id` | file_bridge.h:210 | file_bridge.cpp:1111 | LIVE | abcd-file/src/decode.rs:100,abcd-file/src/decode.rs:230 |  |
| `abc_class_get_descriptor` | file_bridge.h:213 | file_bridge.cpp:1119 | LIVE | abcd-file/src/decode.rs:1879 | Class descriptor (raw MUTF-8 bytes, null-terminated) and name |
| `abc_class_get_name` | file_bridge.h:214 | file_bridge.cpp:1127 | LIVE | abcd-file/src/decode.rs:1894 |  |
| `abc_method_open` | file_bridge.h:220 | file_bridge.cpp:1146 | LIVE | abcd-file/src/decode.rs:103,abcd-file/src/decode.rs:296 |  |
| `abc_method_close` | file_bridge.h:221 | file_bridge.cpp:1154 | LIVE | abcd-file/src/decode.rs:107,abcd-file/src/decode.rs:300 |  |
| `abc_method_name_off` | file_bridge.h:222 | file_bridge.cpp:1162 | DEAD |  |  |
| `abc_method_class_idx` | file_bridge.h:223 | file_bridge.cpp:1170 | DEAD |  |  |
| `abc_method_proto_idx` | file_bridge.h:224 | file_bridge.cpp:1178 | DEAD |  |  |
| `abc_method_access_flags` | file_bridge.h:225 | file_bridge.cpp:1186 | LIVE | abcd-file/src/decode.rs:460 |  |
| `abc_method_code_off` | file_bridge.h:227 | file_bridge.cpp:1194 | LIVE | abcd-file/src/decode.rs:383 | Returns code offset, UINT32_MAX if absent |
| `abc_method_debug_info_off` | file_bridge.h:229 | file_bridge.cpp:1204 | LIVE | abcd-file/src/decode.rs:443 | Returns debug info offset, UINT32_MAX if absent |
| `abc_method_get_class_id` | file_bridge.h:232 | file_bridge.cpp:1214 | DEAD |  | Resolved entity IDs (not raw indices) |
| `abc_method_get_proto_id` | file_bridge.h:233 | file_bridge.cpp:1222 | LIVE | abcd-file/src/decode.rs:397 |  |
| `abc_method_is_external` | file_bridge.h:234 | file_bridge.cpp:1230 | DEAD |  |  |
| `abc_method_get_source_lang` | file_bridge.h:236 | file_bridge.cpp:1238 | LIVE | abcd-file/src/decode.rs:462 | Source language: UINT8_MAX if absent |
| `abc_method_enumerate_annotations` | file_bridge.h:239 | file_bridge.cpp:1248 | LIVE | abcd-file/src/decode.rs:410 | Method annotations |
| `abc_method_enumerate_runtime_annotations` | file_bridge.h:240 | file_bridge.cpp:1258 | LIVE | abcd-file/src/decode.rs:416 |  |
| `abc_method_get_param_annotation_id` | file_bridge.h:243 | file_bridge.cpp:1268 | LIVE | abcd-file/src/decode.rs:492 | Parameter annotation IDs: UINT32_MAX if absent |
| `abc_method_get_runtime_param_annotation_id` | file_bridge.h:244 | file_bridge.cpp:1278 | LIVE | abcd-file/src/decode.rs:495 |  |
| `abc_param_annotations_enumerate` | file_bridge.h:250 | file_bridge.cpp:1288 | LIVE | abcd-file/src/decode.rs:508 |  |
| `abc_method_enumerate_types_in_proto` | file_bridge.h:256 | file_bridge.cpp:1312 | DEAD |  |  |
| `abc_method_enumerate_type_annotations` | file_bridge.h:259 | file_bridge.cpp:1322 | LIVE | abcd-file/src/decode.rs:422 | Method type annotations |
| `abc_method_enumerate_runtime_type_annotations` | file_bridge.h:260 | file_bridge.cpp:1332 | LIVE | abcd-file/src/decode.rs:428 |  |
| `abc_method_get_annotations_number` | file_bridge.h:263 | file_bridge.cpp:1342 | DEAD |  | Method annotation counts, size, ID, and misc |
| `abc_method_get_runtime_annotations_number` | file_bridge.h:264 | file_bridge.cpp:1350 | DEAD |  |  |
| `abc_method_get_type_annotations_number` | file_bridge.h:265 | file_bridge.cpp:1358 | DEAD |  |  |
| `abc_method_get_runtime_type_annotations_number` | file_bridge.h:266 | file_bridge.cpp:1366 | DEAD |  |  |
| `abc_method_get_size` | file_bridge.h:267 | file_bridge.cpp:1374 | DEAD |  |  |
| `abc_method_get_method_id` | file_bridge.h:268 | file_bridge.cpp:1382 | LIVE | abcd-file/src/decode.rs:110,abcd-file/src/decode.rs:363 |  |
| `abc_method_has_valid_proto` | file_bridge.h:269 | file_bridge.cpp:1390 | LIVE | abcd-file/src/decode.rs:393 |  |
| `abc_method_get_numerical_annotation` | file_bridge.h:270 | file_bridge.cpp:1398 | DEAD |  |  |
| `abc_method_get_name_off_static` | file_bridge.h:273 | file_bridge.cpp:1406 | DEAD |  | Method static quick-access (no accessor needed) |
| `abc_method_get_class_id_static` | file_bridge.h:274 | file_bridge.cpp:1414 | DEAD |  |  |
| `abc_method_get_proto_id_static` | file_bridge.h:275 | file_bridge.cpp:1422 | DEAD |  |  |
| `abc_method_get_name` | file_bridge.h:278 | file_bridge.cpp:1430 | DEAD |  | Method name as string (copies into buf, returns byte count; 0 on error) |
| `abc_method_get_name_utf16` | file_bridge.h:280 | file_bridge.cpp:1447 | LIVE | abcd-file/src/decode.rs:1903,abcd-file/src/decode.rs:1909 | Method name via MUTF-8 -> UTF-16 (lossless; query with buf=null) |
| `abc_method_get_name_static` | file_bridge.h:281 | file_bridge.cpp:1461 | DEAD |  |  |
| `abc_code_open` | file_bridge.h:288 | file_bridge.cpp:1481 | LIVE | abcd-file/src/decode.rs:963 |  |
| `abc_code_close` | file_bridge.h:289 | file_bridge.cpp:1489 | LIVE | abcd-file/src/decode.rs:967 |  |
| `abc_code_num_vregs` | file_bridge.h:290 | file_bridge.cpp:1497 | LIVE | abcd-file/src/decode.rs:1022 |  |
| `abc_code_num_args` | file_bridge.h:291 | file_bridge.cpp:1505 | LIVE | abcd-file/src/decode.rs:1023 |  |
| `abc_code_code_size` | file_bridge.h:292 | file_bridge.cpp:1513 | LIVE | abcd-file/src/decode.rs:971 |  |
| `abc_code_instructions` | file_bridge.h:293 | file_bridge.cpp:1521 | LIVE | abcd-file/src/decode.rs:970 |  |
| `abc_code_tries_size` | file_bridge.h:294 | file_bridge.cpp:1529 | DEAD |  |  |
| `abc_code_enumerate_try_blocks_full` | file_bridge.h:310 | file_bridge.cpp:1537 | LIVE | abcd-file/src/decode.rs:2006 |  |
| `abc_code_get_size` | file_bridge.h:313 | file_bridge.cpp:1564 | DEAD |  | Code accessor size and ID |
| `abc_code_get_code_id` | file_bridge.h:314 | file_bridge.cpp:1572 | DEAD |  |  |
| `abc_code_get_num_vregs_static` | file_bridge.h:317 | file_bridge.cpp:1580 | DEAD |  | Code static quick-access (no accessor needed) |
| `abc_code_get_instructions_static` | file_bridge.h:318 | file_bridge.cpp:1588 | DEAD |  |  |
| `abc_field_open` | file_bridge.h:324 | file_bridge.cpp:1598 | LIVE | abcd-file/src/decode.rs:114,abcd-file/src/decode.rs:732 |  |
| `abc_field_close` | file_bridge.h:325 | file_bridge.cpp:1606 | LIVE | abcd-file/src/decode.rs:118,abcd-file/src/decode.rs:736 |  |
| `abc_field_name_off` | file_bridge.h:326 | file_bridge.cpp:1614 | LIVE | abcd-file/src/decode.rs:119,abcd-file/src/decode.rs:740 |  |
| `abc_field_type` | file_bridge.h:327 | file_bridge.cpp:1622 | LIVE | abcd-file/src/decode.rs:754,abcd-file/src/decode.rs:758 |  |
| `abc_field_type_id` | file_bridge.h:330 | file_bridge.cpp:1630 | LIVE | abcd-file/src/decode.rs:759 |  |
| `abc_field_access_flags` | file_bridge.h:331 | file_bridge.cpp:1639 | LIVE | abcd-file/src/decode.rs:923 |  |
| `abc_field_is_external` | file_bridge.h:332 | file_bridge.cpp:1647 | DEAD |  |  |
| `abc_field_class_off` | file_bridge.h:333 | file_bridge.cpp:1655 | DEAD |  |  |
| `abc_field_size` | file_bridge.h:334 | file_bridge.cpp:1663 | DEAD |  |  |
| `abc_field_enumerate_annotations` | file_bridge.h:337 | file_bridge.cpp:1671 | LIVE | abcd-file/src/decode.rs:895 | Enumerate field annotations |
| `abc_field_enumerate_runtime_annotations` | file_bridge.h:338 | file_bridge.cpp:1681 | LIVE | abcd-file/src/decode.rs:901 |  |
| `abc_field_get_value_i32` | file_bridge.h:341 | file_bridge.cpp:1691 | LIVE | abcd-file/src/decode.rs:787 | Field initial values: returns 1 if present, 0 if absent |
| `abc_field_get_value_i64` | file_bridge.h:342 | file_bridge.cpp:1702 | LIVE | abcd-file/src/decode.rs:795 |  |
| `abc_field_get_value_f32` | file_bridge.h:343 | file_bridge.cpp:1713 | LIVE | abcd-file/src/decode.rs:803 |  |
| `abc_field_get_value_f64` | file_bridge.h:344 | file_bridge.cpp:1724 | LIVE | abcd-file/src/decode.rs:811 |  |
| `abc_field_enumerate_type_annotations` | file_bridge.h:347 | file_bridge.cpp:1735 | LIVE | abcd-file/src/decode.rs:907 | Field type annotations |
| `abc_field_enumerate_runtime_type_annotations` | file_bridge.h:348 | file_bridge.cpp:1745 | LIVE | abcd-file/src/decode.rs:913 |  |
| `abc_field_get_annotations_number` | file_bridge.h:351 | file_bridge.cpp:1755 | DEAD |  | Field annotation counts and ID |
| `abc_field_get_runtime_annotations_number` | file_bridge.h:352 | file_bridge.cpp:1763 | DEAD |  |  |
| `abc_field_get_type_annotations_number` | file_bridge.h:353 | file_bridge.cpp:1771 | DEAD |  |  |
| `abc_field_get_runtime_type_annotations_number` | file_bridge.h:354 | file_bridge.cpp:1779 | DEAD |  |  |
| `abc_field_get_field_id` | file_bridge.h:355 | file_bridge.cpp:1787 | LIVE | abcd-file/src/decode.rs:124,abcd-file/src/decode.rs:738 |  |
| `abc_field_get_name_off_static` | file_bridge.h:358 | file_bridge.cpp:1795 | DEAD |  | Field static quick-access (no accessor needed) |
| `abc_field_get_type_static` | file_bridge.h:359 | file_bridge.cpp:1803 | DEAD |  |  |
| `abc_literal_open` | file_bridge.h:365 | file_bridge.cpp:1813 | LIVE | abcd-file/src/decode.rs:1489,abcd-file/src/decode.rs:1564 |  |
| `abc_literal_close` | file_bridge.h:366 | file_bridge.cpp:1821 | LIVE | abcd-file/src/decode.rs:1493,abcd-file/src/decode.rs:1568 |  |
| `abc_literal_count` | file_bridge.h:367 | file_bridge.cpp:1829 | DEAD |  |  |
| `abc_literal_enumerate_vals` | file_bridge.h:391 | file_bridge.cpp:1983 | LIVE | abcd-file/src/decode.rs:1501,abcd-file/src/decode.rs:1593 |  |
| `abc_literal_get_array_id` | file_bridge.h:395 | file_bridge.cpp:1992 | DEAD |  | Literal array by index |
| `abc_literal_get_vals_num` | file_bridge.h:396 | file_bridge.cpp:2000 | DEAD |  |  |
| `abc_literal_get_vals_num_by_index` | file_bridge.h:397 | file_bridge.cpp:2008 | DEAD |  |  |
| `abc_literal_enumerate_vals_by_index` | file_bridge.h:398 | file_bridge.cpp:2016 | DEAD |  |  |
| `abc_literal_resolve_index` | file_bridge.h:402 | file_bridge.cpp:2027 | DEAD |  | Resolve literal array index from entity offset: returns index, UINT32_MAX if not found |
| `abc_literal_get_data_id` | file_bridge.h:404 | file_bridge.cpp:2037 | DEAD |  | Literal data entity ID |
| `abc_module_open` | file_bridge.h:410 | file_bridge.cpp:2047 | LIVE | abcd-file/src/decode.rs:601 |  |
| `abc_module_close` | file_bridge.h:411 | file_bridge.cpp:2055 | LIVE | abcd-file/src/decode.rs:605 |  |
| `abc_module_num_requests` | file_bridge.h:414 | file_bridge.cpp:2063 | LIVE | abcd-file/src/decode.rs:607 | Number of request modules |
| `abc_module_request_off` | file_bridge.h:416 | file_bridge.cpp:2071 | LIVE | abcd-file/src/decode.rs:610 | Get request module string offset by index |
| `abc_module_enumerate_records` | file_bridge.h:423 | file_bridge.cpp:2081 | LIVE | abcd-file/src/decode.rs:644 |  |
| `abc_module_request_phase_read` | file_bridge.h:430 | file_bridge.cpp:2111 | LIVE | abcd-file/src/decode.rs:704 |  |
| `abc_module_get_data_id` | file_bridge.h:433 | file_bridge.cpp:2094 | DEAD |  | Module data entity ID |
| `abc_annotation_open` | file_bridge.h:439 | file_bridge.cpp:2129 | LIVE | abcd-file/src/decode.rs:1137 |  |
| `abc_annotation_close` | file_bridge.h:440 | file_bridge.cpp:2137 | LIVE | abcd-file/src/decode.rs:1141 |  |
| `abc_annotation_class_off` | file_bridge.h:441 | file_bridge.cpp:2145 | LIVE | abcd-file/src/decode.rs:1143 |  |
| `abc_annotation_count` | file_bridge.h:442 | file_bridge.cpp:2153 | LIVE | abcd-file/src/decode.rs:1153 |  |
| `abc_annotation_size` | file_bridge.h:443 | file_bridge.cpp:2161 | DEAD |  |  |
| `abc_annotation_get_element` | file_bridge.h:451 | file_bridge.cpp:2169 | LIVE | abcd-file/src/decode.rs:1161 |  |
| `abc_annotation_get_array_element` | file_bridge.h:459 | file_bridge.cpp:2184 | LIVE | abcd-file/src/decode.rs:1309 |  |
| `abc_annotation_get_annotation_id` | file_bridge.h:463 | file_bridge.cpp:2198 | DEAD |  | Annotation entity ID |
| `abc_annotation_get_value_i64` | file_bridge.h:467 | file_bridge.cpp:2206 | LIVE | abcd-file/src/decode.rs:1178 |  |
| `abc_annotation_get_value_u64` | file_bridge.h:468 | file_bridge.cpp:2217 | LIVE | abcd-file/src/decode.rs:1186 |  |
| `abc_annotation_get_value_f64` | file_bridge.h:469 | file_bridge.cpp:2228 | LIVE | abcd-file/src/decode.rs:1195 |  |
| `abc_annotation_array_read` | file_bridge.h:476 | file_bridge.cpp:2239 | LIVE | abcd-file/src/decode.rs:1345,abcd-file/src/decode.rs:1382 |  |
| `abc_method_handle_read` | file_bridge.h:485 | file_bridge.cpp:2269 | LIVE | abcd-file/src/decode.rs:1245,abcd-file/src/decode.rs:1451 |  |
| `abc_debug_info_open` | file_bridge.h:492 | file_bridge.cpp:2291 | LIVE | abcd-file/src/decode.rs:60,abcd-file/src/decode.rs:66 |  |
| `abc_debug_info_close` | file_bridge.h:493 | file_bridge.cpp:2299 | LIVE | abcd-file/src/decode.rs:71 |  |
| `abc_debug_get_line_table` | file_bridge.h:502 | file_bridge.cpp:2307 | LIVE | abcd-file/src/decode.rs:1715 |  |
| `abc_debug_get_column_table` | file_bridge.h:511 | file_bridge.cpp:2322 | LIVE | abcd-file/src/decode.rs:1740 |  |
| `abc_debug_get_local_vars` | file_bridge.h:524 | file_bridge.cpp:2337 | LIVE | abcd-file/src/decode.rs:1791 |  |
| `abc_debug_get_source_file` | file_bridge.h:528 | file_bridge.cpp:2356 | LIVE | abcd-file/src/decode.rs:1676 | Source file / source code for a method (returns nullptr if absent) |
| `abc_debug_get_source_code` | file_bridge.h:529 | file_bridge.cpp:2364 | LIVE | abcd-file/src/decode.rs:1689 |  |
| `abc_debug_get_parameter_info` | file_bridge.h:537 | file_bridge.cpp:2372 | LIVE | abcd-file/src/decode.rs:1840 |  |
| `abc_debug_get_method_list` | file_bridge.h:543 | file_bridge.cpp:2387 | DEAD |  |  |
| `abc_index_open` | file_bridge.h:549 | file_bridge.cpp:2400 | LIVE | abcd-file/src/decode.rs:372 |  |
| `abc_index_close` | file_bridge.h:550 | file_bridge.cpp:2408 | LIVE | abcd-file/src/decode.rs:376 |  |
| `abc_index_get_offset_by_id` | file_bridge.h:552 | file_bridge.cpp:2416 | DEAD |  | Resolve 16-bit instruction index to entity offset |
| `abc_index_get_function_kind` | file_bridge.h:554 | file_bridge.cpp:2427 | LIVE | abcd-file/src/decode.rs:377 | FunctionKind encoded in access flags |
| `abc_index_get_header_index` | file_bridge.h:555 | file_bridge.cpp:2438 | DEAD |  |  |
| `abc_index_get_num_headers` | file_bridge.h:556 | file_bridge.cpp:2449 | DEAD |  |  |
| `abc_builder_new` | file_bridge.h:562 | file_bridge.cpp:2581 | LIVE | abcd-file/src/encode.rs:219,abcd-file/src/encode.rs:220 |  |
| `abc_builder_free` | file_bridge.h:563 | file_bridge.cpp:2589 | LIVE | abcd-file/src/encode.rs:1114 |  |
| `abc_builder_set_api` | file_bridge.h:566 | file_bridge.cpp:2606 | LIVE | abcd-file/src/encode.rs:227 | Set API policy before creating items (default: upstream current API). |
| `abc_builder_set_file_version` | file_bridge.h:569 | file_bridge.cpp:2616 | LIVE | abcd-file/src/encode.rs:235 |  |
| `abc_builder_add_string` | file_bridge.h:572 | file_bridge.cpp:2640 | LIVE | abcd-file/src/encode.rs:247 | Create / get items |
| `abc_builder_add_class` | file_bridge.h:573 | file_bridge.cpp:2651 | LIVE | abcd-file/src/encode.rs:255 |  |
| `abc_builder_add_foreign_class` | file_bridge.h:574 | file_bridge.cpp:2662 | LIVE | abcd-file/src/encode.rs:261 |  |
| `abc_builder_add_global_class` | file_bridge.h:576 | file_bridge.cpp:2675 | LIVE | abcd-file/src/encode.rs:266 | Convenience: add the global class ("L_GLOBAL;") |
| `abc_builder_add_literal_array` | file_bridge.h:577 | file_bridge.cpp:2686 | LIVE | abcd-file/src/encode.rs:569 |  |
| `abc_builder_class_add_field` | file_bridge.h:580 | file_bridge.cpp:2698 | LIVE | abcd-file/src/encode.rs:445 | Add field to a class |
| `abc_builder_class_add_field_ex` | file_bridge.h:584 | file_bridge.cpp:2719 | LIVE | abcd-file/src/encode.rs:466 | Extended: add field with reference type support |
| `abc_builder_literal_array_add_u8` | file_bridge.h:589 | file_bridge.cpp:2737 | LIVE | abcd-file/src/encode.rs:582 | Add typed items to a literal array (call once per item, in order) |
| `abc_builder_literal_array_add_u16` | file_bridge.h:590 | file_bridge.cpp:2746 | LIVE | abcd-file/src/encode.rs:587 |  |
| `abc_builder_literal_array_add_u32` | file_bridge.h:591 | file_bridge.cpp:2755 | LIVE | abcd-file/src/encode.rs:592 |  |
| `abc_builder_literal_array_add_u64` | file_bridge.h:592 | file_bridge.cpp:2764 | LIVE | abcd-file/src/encode.rs:597 |  |
| `abc_builder_literal_array_add_bool` | file_bridge.h:593 | file_bridge.cpp:2773 | LIVE | abcd-file/src/encode.rs:656 |  |
| `abc_builder_literal_array_add_f32` | file_bridge.h:594 | file_bridge.cpp:2782 | DEAD |  |  |
| `abc_builder_literal_array_add_f64` | file_bridge.h:595 | file_bridge.cpp:2793 | DEAD |  |  |
| `abc_builder_literal_array_add_string` | file_bridge.h:597 | file_bridge.cpp:2804 | LIVE | abcd-file/src/encode.rs:660 | String literal: string_handle is an index returned by abc_builder_add_string |
| `abc_builder_literal_array_add_method` | file_bridge.h:599 | file_bridge.cpp:2814 | LIVE | abcd-file/src/encode.rs:664 | Method literal: method_handle is an index returned by abc_builder_class_add_method_with_proto |
| `abc_builder_literal_array_add_literalarray` | file_bridge.h:601 | file_bridge.cpp:2824 | LIVE | abcd-file/src/encode.rs:672 | Literal array reference: ref_handle is an index returned by abc_builder_add_literal_array |
| `abc_builder_literal_array_add_module_request_phase` | file_bridge.h:628 | file_bridge.cpp:2941 | LIVE | abcd-file/src/encode.rs:721 |  |
| `abc_builder_literal_array_add_module_data` | file_bridge.h:631 | file_bridge.cpp:2834 | LIVE | abcd-file/src/encode.rs:692 |  |
| `abc_builder_finalize` | file_bridge.h:640 | file_bridge.cpp:4085 | TEST-ONLY | abcd-file-sys/src/lib.rs:178,abcd-file-sys/src/lib.rs:221 |  |
| `abc_builder_create_proto` | file_bridge.h:648 | file_bridge.cpp:2958 | LIVE | abcd-file/src/encode.rs:300 |  |
| `abc_builder_create_proto_ex` | file_bridge.h:651 | file_bridge.cpp:2979 | LIVE | abcd-file/src/encode.rs:328 | Extended proto creation with reference type support |
| `abc_builder_class_add_method_with_proto` | file_bridge.h:653 | file_bridge.cpp:3000 | LIVE | abcd-file/src/encode.rs:354 |  |
| `abc_builder_class_set_access_flags` | file_bridge.h:658 | file_bridge.cpp:3029 | LIVE | abcd-file/src/encode.rs:270 | --- Class configuration --- |
| `abc_builder_class_set_source_lang` | file_bridge.h:659 | file_bridge.cpp:3038 | LIVE | abcd-file/src/encode.rs:274 |  |
| `abc_builder_class_set_super_class` | file_bridge.h:661 | file_bridge.cpp:3047 | LIVE | abcd-file/src/encode.rs:278 | super_handle / iface_handle: high bit 0x80000000 = foreign class, else regular class |
| `abc_builder_class_add_interface` | file_bridge.h:662 | file_bridge.cpp:3058 | LIVE | abcd-file/src/encode.rs:282 |  |
| `abc_builder_class_set_source_file` | file_bridge.h:663 | file_bridge.cpp:3069 | LIVE | abcd-file/src/encode.rs:286 |  |
| `abc_builder_method_set_source_lang` | file_bridge.h:666 | file_bridge.cpp:3081 | LIVE | abcd-file/src/encode.rs:389 | --- Method configuration --- |
| `abc_builder_method_set_function_kind` | file_bridge.h:667 | file_bridge.cpp:3090 | LIVE | abcd-file/src/encode.rs:393 |  |
| `abc_builder_method_set_debug_info` | file_bridge.h:668 | file_bridge.cpp:3099 | LIVE | abcd-file/src/encode.rs:397 |  |
| `abc_builder_relocate_code_id` | file_bridge.h:678 | file_bridge.cpp:4005 | LIVE | abcd-file/src/encode.rs:1072 |  |
| `abc_builder_finalize_with_code_ids` | file_bridge.h:684 | file_bridge.cpp:4046 | LIVE | abcd-file/src/encode.rs:1094 |  |
| `abc_builder_field_set_value_i32` | file_bridge.h:688 | file_bridge.cpp:3111 | LIVE | abcd-file/src/encode.rs:486 | --- Field initial values --- |
| `abc_builder_field_set_value_i64` | file_bridge.h:689 | file_bridge.cpp:3121 | LIVE | abcd-file/src/encode.rs:490 |  |
| `abc_builder_field_set_value_f32` | file_bridge.h:690 | file_bridge.cpp:3131 | LIVE | abcd-file/src/encode.rs:494 |  |
| `abc_builder_field_set_value_f64` | file_bridge.h:691 | file_bridge.cpp:3141 | LIVE | abcd-file/src/encode.rs:498 |  |
| `abc_builder_field_set_value_literalarray` | file_bridge.h:698 | file_bridge.cpp:3151 | LIVE | abcd-file/src/encode.rs:513 |  |
| `abc_builder_create_code` | file_bridge.h:707 | file_bridge.cpp:3169 | LIVE | abcd-file/src/encode.rs:526 |  |
| `abc_builder_code_add_try_block` | file_bridge.h:709 | file_bridge.cpp:3187 | LIVE | abcd-file/src/encode.rs:553 |  |
| `abc_builder_method_set_code` | file_bridge.h:712 | file_bridge.cpp:3233 | LIVE | abcd-file/src/encode.rs:401 |  |
| `abc_builder_create_lnp` | file_bridge.h:715 | file_bridge.cpp:3365 | LIVE | abcd-file/src/encode.rs:756 | --- Debug Info --- |
| `abc_builder_lnp_emit_end` | file_bridge.h:716 | file_bridge.cpp:3376 | LIVE | abcd-file/src/encode.rs:760 |  |
| `abc_builder_lnp_emit_advance_pc` | file_bridge.h:717 | file_bridge.cpp:3385 | LIVE | abcd-file/src/encode.rs:764 |  |
| `abc_builder_lnp_emit_advance_line` | file_bridge.h:719 | file_bridge.cpp:3396 | LIVE | abcd-file/src/encode.rs:768 |  |
| `abc_builder_lnp_emit_column` | file_bridge.h:721 | file_bridge.cpp:3407 | LIVE | abcd-file/src/encode.rs:778 |  |
| `abc_builder_lnp_emit_start_local` | file_bridge.h:723 | file_bridge.cpp:3418 | LIVE | abcd-file/src/encode.rs:790 |  |
| `abc_builder_lnp_emit_start_local_extended` | file_bridge.h:725 | file_bridge.cpp:3430 | LIVE | abcd-file/src/encode.rs:811 |  |
| `abc_builder_lnp_emit_end_local` | file_bridge.h:728 | file_bridge.cpp:3443 | LIVE | abcd-file/src/encode.rs:824 |  |
| `abc_builder_lnp_emit_set_file` | file_bridge.h:729 | file_bridge.cpp:3452 | LIVE | abcd-file/src/encode.rs:833 |  |
| `abc_builder_lnp_emit_set_source_code` | file_bridge.h:731 | file_bridge.cpp:3465 | LIVE | abcd-file/src/encode.rs:843 |  |
| `abc_builder_create_debug_info` | file_bridge.h:733 | file_bridge.cpp:3478 | LIVE | abcd-file/src/encode.rs:849 |  |
| `abc_builder_debug_add_param` | file_bridge.h:734 | file_bridge.cpp:3491 | LIVE | abcd-file/src/encode.rs:854 |  |
| `abc_builder_create_annotation` | file_bridge.h:742 | file_bridge.cpp:3503 | LIVE | abcd-file/src/encode.rs:874 |  |
| `abc_builder_create_annotation_ex` | file_bridge.h:755 | file_bridge.cpp:3597 | LIVE | abcd-file/src/encode.rs:940 |  |
| `abc_builder_class_add_annotation` | file_bridge.h:757 | file_bridge.cpp:3676 | LIVE | abcd-file/src/encode.rs:951 |  |
| `abc_builder_class_add_runtime_annotation` | file_bridge.h:758 | file_bridge.cpp:3686 | LIVE | abcd-file/src/encode.rs:954 |  |
| `abc_builder_class_add_type_annotation` | file_bridge.h:759 | file_bridge.cpp:3696 | LIVE | abcd-file/src/encode.rs:957 |  |
| `abc_builder_class_add_runtime_type_annotation` | file_bridge.h:760 | file_bridge.cpp:3706 | LIVE | abcd-file/src/encode.rs:960 |  |
| `abc_builder_method_add_annotation` | file_bridge.h:761 | file_bridge.cpp:3716 | LIVE | abcd-file/src/encode.rs:964 |  |
| `abc_builder_method_add_runtime_annotation` | file_bridge.h:762 | file_bridge.cpp:3726 | LIVE | abcd-file/src/encode.rs:967 |  |
| `abc_builder_method_add_type_annotation` | file_bridge.h:763 | file_bridge.cpp:3736 | LIVE | abcd-file/src/encode.rs:970 |  |
| `abc_builder_method_add_runtime_type_annotation` | file_bridge.h:764 | file_bridge.cpp:3746 | LIVE | abcd-file/src/encode.rs:973 |  |
| `abc_builder_method_add_param` | file_bridge.h:771 | file_bridge.cpp:3758 | LIVE | abcd-file/src/encode.rs:405 |  |
| `abc_builder_method_add_param_ex` | file_bridge.h:776 | file_bridge.cpp:3772 | LIVE | abcd-file/src/encode.rs:416 |  |
| `abc_builder_method_param_add_annotation` | file_bridge.h:780 | file_bridge.cpp:3787 | LIVE | abcd-file/src/encode.rs:982 | Add annotation to a specific method parameter |
| `abc_builder_method_param_add_runtime_annotation` | file_bridge.h:782 | file_bridge.cpp:3800 | LIVE | abcd-file/src/encode.rs:991 |  |
| `abc_builder_method_param_add_type_annotation` | file_bridge.h:784 | file_bridge.cpp:3813 | LIVE | abcd-file/src/encode.rs:1001 |  |
| `abc_builder_method_param_add_runtime_type_annotation` | file_bridge.h:786 | file_bridge.cpp:3826 | LIVE | abcd-file/src/encode.rs:1011 |  |
| `abc_builder_method_seal_param_annotations` | file_bridge.h:794 | file_bridge.cpp:3839 | LIVE | abcd-file/src/encode.rs:430 |  |
| `abc_builder_field_add_annotation` | file_bridge.h:796 | file_bridge.cpp:3853 | LIVE | abcd-file/src/encode.rs:1018 |  |
| `abc_builder_field_add_runtime_annotation` | file_bridge.h:797 | file_bridge.cpp:3863 | LIVE | abcd-file/src/encode.rs:1021 |  |
| `abc_builder_field_add_type_annotation` | file_bridge.h:798 | file_bridge.cpp:3873 | LIVE | abcd-file/src/encode.rs:1024 |  |
| `abc_builder_field_add_runtime_type_annotation` | file_bridge.h:799 | file_bridge.cpp:3883 | LIVE | abcd-file/src/encode.rs:1027 |  |
| `abc_builder_add_foreign_field` | file_bridge.h:802 | file_bridge.cpp:3895 | LIVE | abcd-file/src/encode.rs:481 | --- Foreign items --- |
| `abc_builder_add_foreign_method` | file_bridge.h:804 | file_bridge.cpp:3913 | LIVE | abcd-file/src/encode.rs:378 |  |
| `abc_builder_create_method_handle` | file_bridge.h:810 | file_bridge.cpp:3933 | LIVE | abcd-file/src/encode.rs:748 |  |
| `abc_builder_deduplicate` | file_bridge.h:813 | file_bridge.cpp:3971 | LIVE | abcd-file/src/encode.rs:1033 | --- Deduplication --- |
| `abc_builder_deduplicate_code_and_debug_info` | file_bridge.h:814 | file_bridge.cpp:3981 | LIVE | abcd-file/src/encode.rs:1037 |  |
| `abc_builder_deduplicate_annotations` | file_bridge.h:815 | file_bridge.cpp:3993 | LIVE | abcd-file/src/encode.rs:1041 |  |

## 2. Rust-side usage map (summary)

The full per-export consumer mapping is the "Rust consumer(s)" column of the
§1 table. Structure of the consumption graph:

- **abcd-isa-sys → abcd-isa.** Generated `bytecode.rs` (from
  `templates/bytecode.rs.erb`) calls `isa_get_opcode` (:427), `isa_get_size_by_opcode`
  (:426), `isa_get_vreg`/`isa_get_imm64`/`isa_get_id`/`isa_get_imm_data`
  (:447-454) in `decode_one`, and the whole `*_opcode` classification family
  (:239-284) in the safe `Bytecode` methods. Hand-written consumers:
  `abcd-isa/src/decoder.rs` (`isa_min_prefix_opcode` :39, `isa_get_opcode`
  :49,60, `isa_get_size_by_opcode` :51), `emitter.rs` (the whole
  `isa_emitter_*` family :69-144), `relocation.rs` (`isa_get_opcode` :28,
  `isa_get_size_by_opcode` :29, `isa_get_format` :34, `isa_has_id` :35,
  `isa_get_id` :42, `isa_update_id` :41), `version.rs` (the whole `isa_*version*`
  family :61-127 except `isa_get_api_version_count`).
- **abcd-file-sys → abcd-file.** `abcd-file/src/file.rs` (open/close/header/
  string/checksum/type), `decode.rs` (all accessor families: class/method/
  code/field/literal/module/annotation/proto/debug/index, param annotations,
  method handles, foreign items, index resolution), `encode.rs` (the whole
  `abc_builder_*` family, `abc_builder_relocate_code_id` + the
  `AbcCodeIdUpdater` callback `update_code_id` at encode.rs:68, which re-enters
  `abcd-isa`'s relocation channel), `error.rs:85` (`abc_debug_info_open` null
  semantics). No other workspace crate names a bridge symbol.
- **TEST-ONLY consumers.** `abcd-file-sys/src/lib.rs` `#[cfg(test)]` module
  (line ≥139) alone references `abc_builder_finalize`, `abc_file_get_class_id`,
  `abc_file_validate_checksum`, `abc_file_foreign_off`, `abc_file_foreign_size`;
  `abcd-file/tests/proto_queries.rs:46` alone references
  `abc_proto_enumerate_types`.

## 3. Classification

| Class | abcd-isa-sys | abcd-file-sys | Total |
|---|---|---|---|
| LIVE | 34 | 192 | **226** |
| TEST-ONLY | 0 | 6 | **6** |
| CFG-GATED | 0 | 0 | **0** (no cargo features exist) |
| DEAD | 25 | 75 | **100** |
| **Total exports** | 59 | 273 | **332** |

### 3.1 Reconciliation with the historical "108/324" figure

The 108/324 number comes from the copy-era audit, preserved in
design/review-bridge-wrapper.md ("Dead surface" section): *"108/324
in-repo-unused exports: isa 25 (bytes-based classification family,
`isa_format_*`, `isa_get_imm_count`, `isa_get_literal_index`,
`isa_get_last_vreg`, `isa_get_range_last_reg_idx`, `isa_is_id_*`,
`isa_get_api_version_count`, …), abc 83 (incl. the whole `abc_module_*`
family, 4 dead version helpers, `*_static` quick-access family,
annotation-count getters, `abc_builder_literal_array_add_f32/f64")*.

Re-derived against the current tree:

- **ISA side is identical: 59 exports, 25 dead** — the same families the old
  audit named (verified: all 25 current dead `isa_*` exports are in the old
  audit's families).
- **File side drifted: 273 exports (was ~265), 75 dead + 6 test-only (was 83
  dead).** Two forces, both expected:
  1. **Net +8 exports** from the Phase-3/5 builder and decode work
     (module-data write path, param-annotation sealing, method-handle items,
     request-phase blobs, etc.) — all of the additions are LIVE today.
  2. **8 formerly-dead exports gained Rust references**: the `abc_module_*`
     read family (`abc_module_open/close/num_requests/request_off/
     enumerate_records` — now live in abcd-file/src/decode.rs:601-644, plus
     `abc_module_request_phase_read` at :704) moved from dead to live when
     module decode landed, and six exports (`abc_builder_finalize`,
     `abc_file_get_class_id`, `abc_file_validate_checksum`,
     `abc_file_foreign_off`, `abc_file_foreign_size`,
     `abc_proto_enumerate_types`) are now pinned by sys-crate/integration
     regression tests (audit findings #A8, #16, review #3/#4/#10 etc. — see
     abcd-file-sys/src/lib.rs:143-1165).
- If TEST-ONLY is folded into "dead" (the old audit's "in-repo-unused" did not
  distinguish test references), the comparable current figure is
  **106/332 vs 108/324** — the surface grew by 8 live exports and the
  genuinely-unreferenced count shrank by 2.
- *Unverifiable residual:* the old audit never published its per-symbol list
  beyond the families quoted above, so the exact 8-symbol diff is inferred
  from family membership, not diffed mechanically.

## 4. Deletion estimate

Per-item cpp line counts are definition spans (signature line through the
closing `}` at column 0), computed by source parse; header declaration lines
are listed in §1. "Lines" = `.cpp` body span; every item additionally deletes
1–3 header lines plus its doc comment.

### abcd-isa-sys — 25 dead functions, 222 cpp lines

| Export | `isa_bridge.cpp` def | Lines |
|---|---|---|
| `isa_get_size` | 50–55 | 6 |
| `isa_is_prefixed` | 58–63 | 6 |
| `isa_get_format_from_bytes` | 75–82 | 8 |
| `isa_has_vreg` | 134–139 | 6 |
| `isa_has_imm` | 142–147 | 6 |
| `isa_can_throw` | 158–165 | 8 |
| `isa_is_terminator` | 168–175 | 8 |
| `isa_is_return_or_throw` | 178–185 | 8 |
| `isa_has_flag` | 188–195 | 8 |
| `isa_is_throw_ex` | 198–205 | 8 |
| `isa_is_jump` | 208–215 | 8 |
| `isa_is_range` | 218–225 | 8 |
| `isa_is_suspend` | 228–235 | 8 |
| `isa_format_opcode_name` | 323–337 | 15 |
| `isa_format_instruction` | 340–361 | 22 |
| `isa_format_opcode` | 364–380 | 17 |
| `isa_is_primary_opcode_valid` | 394–401 | 8 |
| `isa_get_imm_count` | 416–423 | 8 |
| `isa_get_literal_index` | 426–433 | 8 |
| `isa_get_last_vreg` | 450–458 | 9 |
| `isa_get_range_last_reg_idx` | 461–469 | 9 |
| `isa_is_id_string` | 472–479 | 8 |
| `isa_is_id_method` | 482–489 | 8 |
| `isa_is_id_literal_array` | 492–499 | 8 |
| `isa_get_api_version_count` | 522–527 | 6 |

### abcd-file-sys — 75 dead functions, 526 cpp lines

| Export | `file_bridge.cpp` def | Lines |
|---|---|---|
| `abc_file_literalarray_idx_off` | 485–490 | 6 |
| `abc_resolve_method_index` | 544–551 | 8 |
| `abc_resolve_field_index` | 564–571 | 8 |
| `abc_resolve_proto_index` | 574–581 | 8 |
| `abc_file_get_string_utf16_len` | 629–635 | 7 |
| `abc_file_get_string_is_ascii` | 638–644 | 7 |
| `abc_file_get_raw_data` | 663–668 | 6 |
| `abc_file_num_index_headers` | 671–676 | 6 |
| `abc_file_get_index_header` | 679–700 | 22 |
| `abc_resolve_lnp_index` | 713–720 | 8 |
| `abc_file_class_idx_off` | 749–754 | 6 |
| `abc_file_num_lnps` | 757–762 | 6 |
| `abc_file_lnp_idx_off` | 765–770 | 6 |
| `abc_file_index_section_off` | 773–778 | 6 |
| `abc_get_current_version` | 783–789 | 7 |
| `abc_get_min_version` | 792–798 | 7 |
| `abc_is_version_less_or_equal` | 801–808 | 8 |
| `abc_contains_literal_array_in_header` | 811–817 | 7 |
| `abc_proto_get_shorty` | 897–904 | 8 |
| `abc_proto_get_size` | 907–912 | 6 |
| `abc_proto_is_equal` | 915–920 | 6 |
| `abc_proto_get_proto_id` | 923–928 | 6 |
| `abc_class_num_fields` | 965–970 | 6 |
| `abc_class_num_methods` | 973–978 | 6 |
| `abc_class_size` | 981–986 | 6 |
| `abc_class_enumerate_interfaces` | 1035–1042 | 8 |
| `abc_class_get_annotations_number` | 1095–1100 | 6 |
| `abc_class_get_runtime_annotations_number` | 1103–1108 | 6 |
| `abc_method_name_off` | 1162–1167 | 6 |
| `abc_method_class_idx` | 1170–1175 | 6 |
| `abc_method_proto_idx` | 1178–1183 | 6 |
| `abc_method_get_class_id` | 1214–1219 | 6 |
| `abc_method_is_external` | 1230–1235 | 6 |
| `abc_method_enumerate_types_in_proto` | 1312–1319 | 8 |
| `abc_method_get_annotations_number` | 1342–1347 | 6 |
| `abc_method_get_runtime_annotations_number` | 1350–1355 | 6 |
| `abc_method_get_type_annotations_number` | 1358–1363 | 6 |
| `abc_method_get_runtime_type_annotations_number` | 1366–1371 | 6 |
| `abc_method_get_size` | 1374–1379 | 6 |
| `abc_method_get_numerical_annotation` | 1398–1403 | 6 |
| `abc_method_get_name_off_static` | 1406–1411 | 6 |
| `abc_method_get_class_id_static` | 1414–1419 | 6 |
| `abc_method_get_proto_id_static` | 1422–1427 | 6 |
| `abc_method_get_name` | 1430–1444 | 15 |
| `abc_method_get_name_static` | 1461–1476 | 16 |
| `abc_code_tries_size` | 1529–1534 | 6 |
| `abc_code_get_size` | 1564–1569 | 6 |
| `abc_code_get_code_id` | 1572–1577 | 6 |
| `abc_code_get_num_vregs_static` | 1580–1585 | 6 |
| `abc_code_get_instructions_static` | 1588–1593 | 6 |
| `abc_field_is_external` | 1647–1652 | 6 |
| `abc_field_class_off` | 1655–1660 | 6 |
| `abc_field_size` | 1663–1668 | 6 |
| `abc_field_get_annotations_number` | 1755–1760 | 6 |
| `abc_field_get_runtime_annotations_number` | 1763–1768 | 6 |
| `abc_field_get_type_annotations_number` | 1771–1776 | 6 |
| `abc_field_get_runtime_type_annotations_number` | 1779–1784 | 6 |
| `abc_field_get_name_off_static` | 1795–1800 | 6 |
| `abc_field_get_type_static` | 1803–1808 | 6 |
| `abc_literal_count` | 1829–1834 | 6 |
| `abc_literal_get_array_id` | 1992–1997 | 6 |
| `abc_literal_get_vals_num` | 2000–2005 | 6 |
| `abc_literal_get_vals_num_by_index` | 2008–2013 | 6 |
| `abc_literal_enumerate_vals_by_index` | 2016–2024 | 9 |
| `abc_literal_resolve_index` | 2027–2034 | 8 |
| `abc_literal_get_data_id` | 2037–2042 | 6 |
| `abc_module_get_data_id` | 2094–2099 | 6 |
| `abc_annotation_size` | 2161–2166 | 6 |
| `abc_annotation_get_annotation_id` | 2198–2203 | 6 |
| `abc_debug_get_method_list` | 2387–2395 | 9 |
| `abc_index_get_offset_by_id` | 2416–2424 | 9 |
| `abc_index_get_header_index` | 2438–2446 | 9 |
| `abc_index_get_num_headers` | 2449–2454 | 6 |
| `abc_builder_literal_array_add_f32` | 2782–2790 | 9 |
| `abc_builder_literal_array_add_f64` | 2793–2801 | 9 |


### Residual-risk notes per deletable family

- **ISA bytes-based classification family** (`isa_can_throw`, `isa_is_terminator`,
  `isa_is_return_or_throw`, `isa_has_flag`, `isa_is_throw_ex`, `isa_is_jump`,
  `isa_is_range`, `isa_is_suspend`): superseded by design — the generated
  `Bytecode` methods call the `*_opcode` variants (bytecode.rs.erb:235-284),
  which need no instruction bytes. Nothing in design/ or MEMORY.md references
  them as planned future use. Risk: none internal; removes a
  "publish-shaped" convenience surface (the D3 argument, now superseded).
- **`isa_format_*` (3 fns, 54 lines)**: disassembly-style formatting via
  `operator<<`. No Rust consumer; the only design-doc mentions are audit
  history (review-bridge-wrapper.md:360). If a future disassembler tool wants
  formatting, `operator<<` can be re-wrapped in a day. Note
  `isa_format_instruction` carries an audit-driven bounds fix
  (isa_bridge.cpp:344-349) — deleting it deletes that fix too, which is fine
  because the code is unreachable.
- **ISA operand helpers** (`isa_get_imm_count`, `isa_get_literal_index`,
  `isa_get_last_vreg`, `isa_get_range_last_reg_idx`, `isa_is_id_string/method/
  literal_array`, `isa_has_vreg`, `isa_has_imm`, `isa_get_size`,
  `isa_is_prefixed`, `isa_get_format_from_bytes`, `isa_is_primary_opcode_valid`,
  `isa_get_api_version_count`): generated `decode_one` extracts operands
  directly; `relocation.rs` uses `isa_get_format` + `isa_has_id` instead of
  `isa_is_id_*`. Deleting them does **not** remove any vendor capability from
  the live surface (§5): every vendor method they wrap is either reachable
  through another live export or not needed (proof per row in §5.2).
- **`abc_*_static` quick-access family** (8 fns): decode always opens the
  typed accessor instead (`abc_method_open` etc.); the statics were a
  copy-era optimization. Zero consumers, zero doc references.
- **`abc_resolve_{method,field,proto}_index`**: decode resolves method/field/
  proto ids through the generic `abc_resolve_offset_by_index`
  (decode.rs:282) and `abc_resolve_class_index` (decode.rs:1995). The three
  typed variants are unused duplicates of vendor one-liners.
- **Header-field getters** (`abc_file_literalarray_idx_off`,
  `abc_file_class_idx_off`, `abc_file_num_lnps`, `abc_file_lnp_idx_off`,
  `abc_file_index_section_off`, `abc_file_num_index_headers`,
  `abc_file_get_index_header`, `abc_file_get_raw_data`,
  `abc_file_get_string_utf16_len`, `abc_file_get_string_is_ascii`): raw header
  plumbing with no Rust consumer; the decode model takes what it needs via
  typed accessors. `abc_file_get_raw_data` is additionally a safety smell
  (hands out the padded internal buffer) — deleting it is a small hardening
  win.
- **Version helpers** (`abc_get_current_version`, `abc_get_min_version`,
  `abc_is_version_less_or_equal`, `abc_contains_literal_array_in_header`):
  duplicated by the isa-side `isa_get_version`/`isa_get_min_version`/
  `isa_is_version_compatible` family, which is what `abcd_isa::Version` uses
  (abcd-isa/src/version.rs:61-89) and abcd-file re-exports
  (abcd-file/src/lib.rs:42). Dead duplicates.
- **Annotation/entity count + id getters** (`abc_*_get_*_number` ×8,
  `abc_annotation_size`, `abc_annotation_get_annotation_id`,
  `abc_class_num_fields/num_methods/size`, `abc_method_get_size`,
  `abc_method_name_off`, `abc_method_class_idx`, `abc_method_proto_idx`,
  `abc_method_is_external`, `abc_method_get_class_id`, `abc_field_class_off`,
  `abc_field_is_external`, `abc_field_size`, `abc_field_get_name_off_static`,
  `abc_field_get_type_static`, `abc_method_get_numerical_annotation`,
  `abc_module_get_data_id`, `abc_literal_*` index family ×6,
  `abc_proto_get_proto_id/get_shorty/get_size/is_equal`,
  `abc_code_get_size/get_code_id/tries_size/get_num_vregs_static/
  get_instructions_static`, `abc_index_get_offset_by_id/get_header_index/
  get_num_headers`, `abc_class_enumerate_interfaces`,
  `abc_class_get_annotations_number/get_runtime_annotations_number`,
  `abc_method_enumerate_types_in_proto`, `abc_debug_get_method_list`,
  `abc_resolve_lnp_index`, `abc_method_get_class_id_static`,
  `abc_method_get_name`, `abc_method_get_name_static`,
  `abc_method_get_name_off_static`, `abc_method_get_proto_id_static`):
  all pure readers/writers with no Rust consumer and no build.rs/codegen
  reference (build.rs references no bridge symbols — verified by grep of both
  build scripts). Not panic guards; the panic guards live inside LIVE
  functions.
- **`abc_builder_literal_array_add_f32/f64`**: the Rust encoder bit-casts
  floats to u32/u64 itself and calls `abc_builder_literal_array_add_u32/u64`
  (encode.rs:582-597). The C++ bit-cast adders are dead by construction.
- **TEST-ONLY 6 (38 cpp lines, not in the deletable totals above)**:
  `abc_builder_finalize` (3 lines; thin wrapper over
  `abc_builder_finalize_with_code_ids`, file_bridge.cpp:4085-4087 — production
  encode always uses the code-ids variant, encode.rs:1094),
  `abc_file_get_class_id`, `abc_file_validate_checksum`,
  `abc_file_foreign_off`, `abc_file_foreign_size`, `abc_proto_enumerate_types`.
  These pin sys-crate regression tests for audit findings #A8/#B3/#16/review
  #3/#4 (abcd-file-sys/src/lib.rs:198-510) — **keep** (they are covered by CI
  tests, so they do not hurt the coverage ratio; deleting them would force
  test rewrites for zero denominator gain).

### Non-deletable OUR C++ (explicitly in scope but must stay)

- **Merged `File` method implementations + stubs**, file_bridge.cpp:137-299
  (~163 lines): vendor `file.cpp` is excluded from the build
  (abcd-file-sys/build.rs:99-104), so the bridge provides the definitions the
  compiled vendor TUs link against — `File::File/~File`, `ThrowIfWithCheck`
  (:154, the exception-throwing error path every accessor inline uses),
  `OpenFromMemory` (:211,217), `GetClassId` (:174), `ValidateChecksum` (:198,
  real adler32), `GetFileType` (:247, ported from vendor file.cpp:677), plus
  deliberate stubs (`Open`, `OpenUncompressedArchive`, `OpenPandaFile*`,
  `CheckSecureMem`, `CheckHeader`, `CheckFileVersion`, `CalcFilenameHash`,
  `GetClassIdFromClassHashTable` → linear scan, `ARCHIVE_FILENAME`) and the
  `Timer` no-op statics (:306-309). Deleting any of these breaks the link;
  several stubs look "dead" but satisfy vendor references. *Unverified at
  object level:* which stubs are strictly required by the current vendor TU
  set (a `nm`-based reachability pass over the static archive could shrink
  this list; optional follow-up).
- **Static internal helpers** (`opcode_is_valid` isa_bridge.cpp:16,
  `inst_opcode_is_valid` :20, `inst_from_opcode` :240, the tolerant literal
  enumerator file_bridge.cpp:1882, the two staging flushes :3293/:3301,
  `resolve_type` :2598, `resolve_entity_by_tag` :3536,
  `component_type_from_tag` :3580, `BuilderVersionScope` :2563): all reachable
  from LIVE exports.
- **`shim/` headers** (both crates): compile-time shims (platform macros,
  `securec`, `zlib.h` adler32 used by `ValidateChecksum` + the finalize
  checksum backfill, `logger.h`, `file.h` force-include guard). No exports;
  untouched by this analysis.

## 5. Completeness proof

Two directions: (§5.1) every vendor capability the Rust stack needs today has
a live export chain, with vendor file:line; (§5.2) the reverse sweep — no
Rust code reaches vendor functionality except through the bridge.

Vendor path prefix below: `abcd-file-sys/arkcompiler_runtime_core/` (identical
pin in the isa-sys copy, same commit `4fba38e`). `libpandafile/` abbreviated
as `lpf/`, `libpandabase/include/libpandabase/` as `lpb/`.

### 5.1 Forward: needed vendor capability → live export chain

Every row names the Rust consumer (file:line), the live bridge export(s)
(header line), and the vendor API entry point (file:line in the pinned
submodule). All exports listed are LIVE per §3.

| # | Vendor capability | Rust consumer | Live bridge export(s) | Vendor API (file:line) |
|---|---|---|---|---|
| 1 | File open/parse from memory, error reporting | abcd-file/src/file.rs:23-27 | `abc_file_open`/`abc_file_close`/`abc_file_open_error` (file_bridge.h:50-53) | `File::OpenFromMemory` lpf/file.h:423 — **implemented in our bridge** file_bridge.cpp:211 (vendor file.cpp excluded, build.rs:99-104); magic/size validation file_bridge.cpp:395-434 |
| 2 | Header fields (num_classes, sizes, offsets, checksum, foreign region) | file.rs:41-54, decode.rs:76-78 | `abc_file_num_classes`/`_size`/`_version`/`_checksum`/… (file_bridge.h:56-64,127) | `File::GetHeader` lpf/file.h:154 |
| 3 | Class table iteration | decode.rs:78,141 | `abc_file_class_offset` (h:57) | `File::GetClasses` lpf/file.h:191 |
| 4 | Literal-array table iteration | decode.rs:1518,1522 | `abc_file_num_literalarrays`/`abc_file_literalarray_offset` (h:58-59; INVALID_INDEX guard file_bridge.cpp:462-472) | `File::GetLiteralArrays` lpf/file.h:199 |
| 5 | String access (raw MUTF-8 + lossless UTF-16) | file.rs:83-110 | `abc_file_get_string`, `abc_file_get_string_utf16` (h:67-76) | `File::GetStringData` lpf/file.h:147 + `utf::ConvertMUtf8ToUtf16` lpb/utils/utf.h:78 |
| 6 | Index resolution (16-bit insn index → entity offset) | decode.rs:282,1995 | `abc_resolve_offset_by_index`, `abc_resolve_class_index` (h:80,122) | `File::ResolveOffsetByIndex` lpf/file.h:337, `ResolveClassIndex` :319 (bounded by `ThrowIfWithCheck`, file.h:186) |
| 7 | Class lookup by name | sys tests only (TEST-ONLY `abc_file_get_class_id`) | — (live decode iterates classes; see §4 risk notes) | `File::GetClassId` implemented file_bridge.cpp:174 |
| 8 | Foreign-section membership + foreign item names | file.rs:118, decode.rs:945 | `abc_file_is_external`, `abc_foreign_item_name_off` (h:87-91) | `File::IsExternal` lpf/file.h:169 + bounded raw read (ours, file_bridge.cpp:602-627) |
| 9 | File type (dynamic/static) | file.rs:69 | `abc_file_get_type` (h:99) | `GetFileType` ported from vendor lpf/file.cpp:677 into file_bridge.cpp:247 (STATIC_VERSION lpf/file.h:62) |
| 10 | Checksum validation | sys test (TEST-ONLY `abc_file_validate_checksum`); encode side backfills adler32 | `abc_builder_finalize_with_code_ids` checksum backfill file_bridge.cpp:4073-4078 | `File::ValidateChecksum` implemented file_bridge.cpp:198; adler32 from bridge/shim/zlib.h |
| 11 | Proto accessor (arg/return types, ref types, counts) | decode.rs:1043-1080 | `abc_proto_open/close/num_args/get_return_type/get_arg_type/get_reference_type/get_ref_num` (h:149-155) | `ProtoDataAccessor` lpf/proto_data_accessor.h:36-75 (empty-shorty underflow worked around, file_bridge.cpp:838-851, audit #B3) |
| 12 | Class data accessor (super, flags, ifaces, source lang/file, methods, fields, annotations) | decode.rs:92-243 | `abc_class_open/close/super_class_off/access_flags/source_file_off/enumerate_methods/enumerate_fields/get_ifaces_number/get_interface_id/get_source_lang/enumerate_{,runtime_,type_,runtime_type_}annotations/get_class_id/get_descriptor/get_name` (h:170-214) | `ClassDataAccessor` lpf/class_data_accessor.h:33-129 |
| 13 | Method data accessor (name, proto, flags, code/debug offsets, source lang, annotations) | decode.rs:103-495 | `abc_method_open/close/access_flags/code_off/debug_info_off/get_proto_id/get_source_lang/enumerate_*annotations/get_param_annotation_id/get_runtime_param_annotation_id/get_method_id/get_name_utf16/has_valid_proto` (h:220-280) | `MethodDataAccessor` lpf/method_data_accessor.h:33-181 |
| 14 | Param annotations item enumeration | decode.rs:508 | `abc_param_annotations_enumerate` (h:250) | hand-rolled per vendor layout `ParamAnnotationsItem::Write` lpf/file_items.cpp:449; reads via `helpers::Read` lpf/helpers.h:63-117 |
| 15 | Code accessor (vregs, args, size, instructions, try blocks) | decode.rs:963-1023,2006 | `abc_code_open/close/num_vregs/num_args/code_size/instructions/enumerate_try_blocks_full` (h:288-310) | `CodeDataAccessor` lpf/code_data_accessor.h:93-150 |
| 16 | Field accessor (name, type, flags, values, annotations) | decode.rs:114-923 | `abc_field_open/close/name_off/type/type_id/access_flags/enumerate_*annotations/get_value_{i32,i64,f32,f64}/get_field_id` (h:324-355) | `FieldDataAccessor` lpf/field_data_accessor.h:42-162; `Type::GetTypeFromFieldEncoding` lpf/templates/type.h.erb:218 (generated into OUT_DIR type.h) |
| 17 | Literal arrays (count, per-array values incl. typed arrays, nested) | decode.rs:1489-1593 | `abc_literal_open/close/enumerate_vals` (h:365-392) | `LiteralDataAccessor` lpf/literal_data_accessor.h:76-110; enumeration is OUR tolerant rewrite file_bridge.cpp:1882-1981 (vendor `EnumerateLiteralVals` aborts on tag 0x00, audit #A1; tag pins :1851-1880) |
| 18 | Module records + request-phase blobs | decode.rs:601-704 | `abc_module_open/close/num_requests/request_off/enumerate_records`, `abc_module_request_phase_read` (h:410-431) | `ModuleDataAccessor` lpf/module_data_accessor.h:49-61, ctor layout lpf/module_data_accessor.cpp:20, `EnumerateModuleRecord` lpf/module_data_accessor-inl.h:25; phase blob layout hand-rolled (runtime reader is in ets_runtime, not vendored — documented file_bridge.cpp:2102-2110) |
| 19 | Annotation accessor (elements, arrays, 64-bit values, array bulk read) | decode.rs:1137-1382 | `abc_annotation_open/close/class_off/count/get_element/get_array_element/get_value_{i64,u64,f64}/array_read` (h:439-478) | `AnnotationDataAccessor` lpf/annotation_data_accessor.h:43-101; bulk read via `File::GetSpanFromId` lpf/file.h:182 + `leb128::DecodeUnsigned` lpb/utils/leb128.h:33 |
| 20 | MethodHandle items | decode.rs:1245,1451 | `abc_method_handle_read` (h:485) | hand-rolled (ours, file_bridge.cpp:2269-2287, audit #B4); vendor `MethodHandleDataAccessor` lpf/method_handle_data_accessor.h:25-51 is **not compiled** (build.rs:103) |
| 21 | Debug info (LNP line/column tables, locals, params, source) | decode.rs:60-71,1676-1840; error.rs:85 | `abc_debug_info_open/close`, `abc_debug_get_{line,column}_table`, `_get_local_vars`, `_get_source_file`, `_get_source_code`, `_get_parameter_info` (h:492-538) | `DebugInfoExtractor` lpf/debug_info_extractor.h:52-78 |
| 22 | Function kind (encoded in method access flags) | decode.rs:372-377 | `abc_index_open/close`, `abc_index_get_function_kind` (h:549-554) | re-derived ours (file_bridge.cpp:2427-2435) from `FUNCTION_KIND_MASK`/`FLAG_WIDTH` lpf/file_items.h:138-140 — vendor `IndexAccessor` lpf/index_accessor.h:25-51 **deliberately not wrapped** (unchecked header index, audit #B2) |
| 23 | Builder: strings, classes (incl. foreign/global), literal arrays | encode.rs:247-266,569 | `abc_builder_new/free/set_api/set_file_version/add_string/add_class/add_foreign_class/add_global_class/add_literal_array` (h:562-577) | `ItemContainer::GetOrCreate*` lpf/file_item_container.h:48-81 |
| 24 | Builder: fields, methods, protos (incl. reference types) | encode.rs:300-481 | `abc_builder_create_proto{,_ex}`, `abc_builder_class_add_field{,_ex}`, `abc_builder_class_add_method_with_proto`, `abc_builder_add_foreign_{field,method}` (h:580-655,802-805) | `ClassItem::AddField/AddMethod` lpf/file_items.h:1031-1038, `GetOrCreateProtoItem` file_item_container.h:75, `ForeignFieldItem/ForeignMethodItem` via `CreateItem` :84 |
| 25 | Builder: literal array items (all tags + module data + request phase) | encode.rs:582-721 | `abc_builder_literal_array_add_{u8,u16,u32,u64,bool,string,method,literalarray,module_data,module_request_phase}` (h:589-635) | `LiteralArrayItem::AddItems` lpf/file_items.h (staging flush file_bridge.cpp:3293); module blob layout validated against module_data_accessor-inl.h:25 |
| 26 | Builder: field values, class/method config, try-catch | encode.rs:282-553 | `abc_builder_field_set_value_{i32,i64,f32,f64,literalarray}`, `abc_builder_class_set_*`, `abc_builder_method_set_*`, `abc_builder_create_code`, `abc_builder_code_add_try_block`, `abc_builder_method_set_code` (h:658-712) | `FieldItem::SetValue` lpf/file_items.h:550, `MethodItem::SetCode/SetDebugInfo/SetFunctionKind` :763-871, `CodeItem::AddTryBlock`, `GetOrCreateIdValueItem` file_item_container.h:68 |
| 27 | Builder: debug info + LNP program emission | encode.rs:756-854 | `abc_builder_create_lnp`, `abc_builder_lnp_emit_{end,advance_pc,advance_line,column,start_local,start_local_extended,end_local,set_file,set_source_code}`, `abc_builder_create_debug_info`, `abc_builder_debug_add_param` (h:715-734) | `LineNumberProgramItem::Emit*` lpf/file_items.h:618-644, `DebugInfoItem::AddParameter/SetLineNumber` :692-708; staged-flush discipline ours (file_bridge.cpp:2459-2462,3301-3363, F-new-1) |
| 28 | Builder: annotations (scalar/array/64-bit/entity refs, all 12 attach sites, param annotations) | encode.rs:874-1027 | `abc_builder_create_annotation{,_ex}`, `abc_builder_{class,method,field}_add_*annotation*` (12 fns), `abc_builder_method_add_param{,_ex}`, `abc_builder_method_param_add_*` (4 fns), `abc_builder_method_seal_param_annotations` (h:742-799) | `AnnotationItem`/`ArrayValueItem`/`ScalarValueItem` lpf/file_items.h; `ParamAnnotationsItem` ctor lpf/file_items.cpp:424; tag↔type pin static_asserts file_bridge.cpp:48-87 |
| 29 | Builder: MethodHandle items | encode.rs:748 | `abc_builder_create_method_handle` (h:810) | `MethodHandleItem` lpf/file_items.h via `CreateItem` file_item_container.h:84 |
| 30 | Builder: dedup + finalize + layout | encode.rs:1033-1094 | `abc_builder_deduplicate`, `_deduplicate_code_and_debug_info`, `_deduplicate_annotations`, `abc_builder_finalize_with_code_ids` (h:813-815,684) | `ItemContainer::Deduplicate*` file_item_container.h:214-218, `ComputeLayout` :119, `Write` :121, `MemoryWriter` lpf/file_writer.h:111-125; API policy scoping ours (`BuilderVersionScope` file_bridge.cpp:2563) |
| 31 | Entity relocation (patch entity IDs in emitted bytecode after layout) | encode.rs:1094 + abcd-isa/src/relocation.rs:23-42 | `abc_builder_relocate_code_id` (h:678) + `AbcCodeIdUpdater` callback → `isa_update_id` (isa_bridge.h:114) | `IndexedItem::GetIndex/HasIndex` lpf/file_items.h:310-317, `MethodItem::AddIndexDependency` :779; `BytecodeInst::UpdateId` lpf/bytecode_instruction.h:253 |
| 32 | ISA opcode metadata: format/size/validity/prefix | decoder.rs:39-60, relocation.rs:23-42, bytecode.rs.erb:426-427 | `isa_get_opcode`, `isa_get_size_by_opcode`, `isa_get_size_from_bytes`, `isa_get_format`, `isa_min_prefix_opcode`, `isa_has_id` (isa_bridge.h:29-63,99) | `BytecodeInst<FAST>` lpf/bytecode_instruction.h:243-428 (`GetFormat` :401, `Size` :403-405, `GetMinPrefixOpcodeIndex` :287); validity table generated by OUR template `isa_bridge_valid_opcode.h.erb` from isa.yaml (build.rs:90-97) — guards vendor `GetFormat`'s NDEBUG-abort (isa_bridge.cpp:12-15) |
| 33 | ISA operand extraction | bytecode.rs.erb:447-454 | `isa_get_vreg`, `isa_get_imm64`, `isa_get_id`, `isa_get_imm_data` (isa_bridge.h:52-58,105) | `GetVReg`/`GetImm64`/`GetId`/`GetImmData` lpf/bytecode_instruction.h:246-261 |
| 34 | ISA classification (jump/throw/terminator/range/suspend/flags/exceptions) | bytecode.rs.erb:239-284 | `isa_is_jump_opcode`, `isa_can_throw_opcode`, `isa_is_terminator_opcode`, `isa_has_flag_opcode`, `isa_is_range_opcode`, `isa_is_return_or_throw_opcode`, `isa_is_suspend_opcode`, `isa_is_throw_ex_opcode` (isa_bridge.h:86-93) | `IsJumpInstruction`/`CanThrow`/`IsTerminator`/`HasFlag`/`IsRangeInstruction`/`IsReturnOrThrowInstruction`/`IsSuspend`/`IsThrow` lpf/bytecode_instruction.h:377-424, via `inst_from_opcode` isa_bridge.cpp:240 |
| 35 | ISA assembly (emitter with labels) | abcd-isa/src/emitter.rs:69-144 | `isa_emitter_create/destroy/create_label/bind/build/free_buf/emit` (isa_bridge.h:166-183) | `BytecodeEmitter` lpf/bytecode_emitter.h:55-95; dispatch switch generated by OUR template `isa_bridge_emit_dispatch.h.erb` (build.rs:82-88) |
| 36 | Version constants/maps (current, min, api map, incompatible set, sub-api lookup) | abcd-isa/src/version.rs:61-127; builder policy encode.rs (via `abc_builder_set_api/set_file_version`) | `isa_get_version`, `isa_get_min_version`, `isa_get_version_by_api`, `isa_get_version_by_api_sub`, `isa_is_version_compatible`, `isa_incompatible_version_count`, `isa_incompatible_version_at`, `isa_is_version_incompatible` (isa_bridge.h:137-161) | generated `file_format_version.h` (from lpf/templates/file_format_version.h.erb:36-89; `api_version_map`, `incompatibleVersion`, `GetVersionByApi`), `IsVersionLessOrEqual` lpf/file_format_version.cpp:34, `File::VERSION_SIZE` lpf/file.h:60 |
| 37 | Enum/constant surface (ACC_*, LiteralTag, ModuleTag, SourceLang, TypeId, FunctionKind, MethodHandleType) | abcd-file/src/types.rs etc. | bindgen constants (no functions): enum_bindings.rs | build.rs:207-244, generated `file_bridge_enums.h` from lpf/modifiers.h + vendor enum headers (abcd-file-sys/build.rs:283-328) |

**Gaps found: none.** Every vendor capability exercised by the Rust stack has
at least one LIVE export. No needed capability lacks a live export.

### 5.2 Reverse sweep: no path from Rust to vendor except the bridge

1. **Only two build scripts touch vendor code** (`grep -rl
   arkcompiler_runtime_core --include=build.rs .` → exactly
   `abcd-file-sys/build.rs`, `abcd-isa-sys/build.rs`). No other crate compiles
   or links vendor objects.
2. **Bindgen allowlists are function-name-scoped**: `isa_.*` functions
   (abcd-isa-sys/build.rs:191) and `abc_.*` functions
   (abcd-file-sys/build.rs:197). The second file-sys bindgen pass
   (build.rs:210-244) allowlists only *types/vars* (`ABC_ACC_.*`,
   `AbcAccessFlags`, five vendor enum classes) — it declares no functions.
   Therefore the only callable C symbols visible to Rust are the 332 bridge
   exports.
3. **No hand-written `extern "C"` blocks declare foreign symbols anywhere in
   the workspace** — every `extern "C"` match outside the sys crates is an
   `unsafe extern "C" fn` *callback definition* passed to the bridge
   (e.g. abcd-file/src/encode.rs:68 `update_code_id`, decode.rs:502,626,700,
   1705; literal.rs:174; tests). (`hermes-main/**` matches belong to an
   unrelated vendored tree that is not a workspace member — Cargo.toml:3-14.)
4. **No alternative FFI channels**: no `dynlib`/`libloading` deps, no
   `#[link_name]`, no inline asm referencing vendor symbols (grep clean).
   Rust physically cannot name a vendor C++ symbol (mangled) without a
   declaration, and none exists outside the allowlisted bindgen output.
5. **The vendor→Rust direction** is limited to the documented callback
   typedefs in file_bridge.h:43-44,157,181,185,249,255,308,390,419,501,510,
   523,536 and the `AbcCodeIdUpdater` (h:682) — all initiated by bridge calls.

Caveat (process, not code): nothing *structurally* prevents a future patch
from adding a stray extern; the guarantee is the current tree plus the
allowlist mechanism, and CI would catch a new `build.rs` vendor consumer via
the duplicate-vendor-file protection discussion (MEMORY.md #22 — currently
"leave as is").

### 5.3 Vendor files deliberately not compiled (and why that is not a gap)

abcd-file-sys/build.rs:99-104 excludes four vendor TUs:

| Excluded vendor TU | Reason (build.rs comment) | Needed functionality provided by |
|---|---|---|
| `file.cpp` | pulls in runtime machinery (pgo, ifstream) | merged implementations in file_bridge.cpp:137-299 (rows 1,9,10 above) |
| `file_reader.cpp` | upstream drift (calls `MethodParamItem::AddRuntimeAnnotation`, absent in this tree) | nothing needed — pandasm text parsing is out of product scope |
| `pgo.cpp` | runtime machinery | nothing needed |
| `method_handle_data_accessor.cpp` | "not part of the proven subset" | hand-rolled `abc_method_handle_read` (row 20) |

Vendor `IndexAccessor` (compiled? — its header is include-only; the accessor
is header-defined, lpf/index_accessor.h:25-51) is deliberately bypassed at the
bridge level (file_bridge.cpp:371-379, audit #B2) and replaced by bounded
re-derivation (row 22). Vendor `FileReader`/`pgo` capabilities are confirmed
unused by any Rust code (§5.2).

## 6. Verdict

### 6.1 Recommended action per class

| Class | Count | Action |
|---|---|---|
| DEAD isa (25 fns) | 222 cpp lines + 26 header lines | **Delete now.** No consumer, no Track-2/roadmap reference, no codegen dependency. The deleted vendor wrappers lose nothing: §5.1 rows 32-34 cover every needed ISA capability through the live opcode-based family. |
| DEAD abc (75 fns) | 526 cpp lines + 78 header lines | **Delete now**, except split families noted in §4 (index accessor keeps open/close/get_function_kind; literal keeps open/close/enumerate_vals). No residual-risk item blocks deletion; `abc_file_get_raw_data` deletion is additionally a hardening win. |
| TEST-ONLY (6 fns) | 38 cpp lines | **Keep.** They pin audit regression tests (#A8 checksum, #B3 empty proto, #16 foreign names, review #3/#4). Deleting them saves ~41 lines but forces rewriting 8 sys tests and loses the pins. If the maintainer prefers a pure surface, move the pins to `abc_builder_finalize_with_code_ids` + live equivalents and delete — low value either way. |
| CFG-GATED | 0 | n/a (no features exist) |
| Merged File impls + stubs (file_bridge.cpp:137-309) | ~170 lines | **Keep** (linker-required). Optional follow-up: `nm`-level dead-stub sweep to shrink the stub list — explicitly *unverified* here. |
| Shim headers | ~470 lines both crates | **Keep** (compile-time). |

### 6.2 Totals

- **Deletable now: 100 functions, ≈ 852 source lines** (748 `.cpp` + 104 `.h`
  declarations), plus an estimated ~40-60 lines of now-orphaned header doc
  comments — call it **≈ 0.9 k lines of bridge C++**.
  - abcd-isa-sys: 25 fns, 222 cpp + 26 hdr = **248 lines** (isa_bridge.cpp
    shrinks 672 → ~450; isa_bridge.h 188 → ~150).
  - abcd-file-sys: 75 fns, 526 cpp + 78 hdr = **604 lines** (file_bridge.cpp
    4089 → ~3563; file_bridge.h 823 → ~720).
- After deletion the bridge surface is **226 live exports** (34 isa + 192
  file) + 6 test-pinned = 232 declarations.
- Deletion is mechanically simple: every dead export is a self-contained
  `extern "C"` function, none is called from other bridge code (verified: no
  dead symbol appears more than once in its `.cpp` — definition only), and the
  bindgen allowlists regenerate bindings automatically.

### 6.3 Effect on the bridge coverage number

Baseline (design/test-quality-evaluation.md §4.1, llvm-cov lines): bridge C++
58.88% (2 227/3 782) CI-only, 59.89% corpus-inclusive. Dead code is by
construction uncovered, so removing ≈ 852 uncovered lines:

- CI-only: 2 227 / (3 782 − 852) ≈ **76.0%**
- Corpus-inclusive: ≈ 2 265 / 2 930 ≈ **77.3%**

(Estimate assumes the coverage denominator counts the same lines the source
parse counts; llvm-cov's line metric may differ by a few percent — flagged as
approximate. Keeping the 6 TEST-ONLY functions costs nothing: they are
covered by CI tests.)

### 6.4 The completeness answer to the maintainer's question

- **How much bridge C++ could be deleted:** 100 of 332 exports (30.1%),
  ≈ 0.9 k lines (~14% of the 6 216-line bridge/shim tree; ~30% of the two
  bridge `.cpp` files' export-bearing code), at low risk, with no consumer
  changes outside deleting dead declarations.
- **Is every necessary vendor capability already exported through the live
  bridge:** **Yes — proven in both directions.** §5.1 maps all 37 needed
  capability groups to live exports with vendor file:line; §5.2 proves the
  bridge is the only channel (allowlist-scoped bindgen, no stray externs, no
  other build.rs vendor consumer). The four excluded vendor TUs and the
  bypassed `IndexAccessor` are deliberate, documented, and fully substituted
  (§5.3). **Zero missing capabilities found.**

---

*Evidence limitations (explicitly flagged):* (1) classification rests on
source-level grep of all tracked Rust/ERB files — object-level `nm`
confirmation was not performed; (2) untracked-but-present files would be
missed (`git status` shows only `.vscode/` and the two submodule pointers as
dirty); (3) the historical 108/324 list was never itemized, so the drift
breakdown in §3.1 is family-level inference; (4) the linker-required stub set
in file_bridge.cpp:137-309 was not minimized by `nm` reachability.

## Orchestrator verification (2026-09-25, before landing)

Independently re-verified by the orchestrator:

- **Export counts**: header parse gives 59 `isa_*` + 273 `abc_*` = 332 — exact.
- **Classification spot-checks**: 8 claimed-DEAD symbols (`isa_get_size`,
  `isa_format_instruction`, `abc_file_get_raw_data`, `abc_method_get_name`,
  `abc_literal_count`, `abc_builder_literal_array_add_f32`,
  `abc_resolve_lnp_index`, `abc_debug_get_method_list`) — zero Rust/ERB
  references each (git grep over tracked files) — exact. 3 claimed-LIVE
  (`isa_get_format`, `abc_file_open`, `abc_module_open`) — referenced as
  claimed. All 6 TEST-ONLY references resolve to `abcd-file-sys/src/lib.rs`'s
  single `#[cfg(test)]` module (opens at lib.rs:139) or `*/tests/` — exact.
- **Mechanism claims**: build.rs EXCLUDED list = the 4 TUs named
  (abcd-file-sys/build.rs:99-104); bindgen allowlists `isa_.*`/`abc_.*`
  (abcd-isa-sys/build.rs:191-193, abcd-file-sys/build.rs:197-199); zero
  `[features]` in any workspace Cargo.toml — all exact.
- **Deletion table arithmetic**: 100 rows; isa 25 fns / 222 lines and abc
  75 fns / 526 lines re-summed from the tables — internally exact.
  *Boundary convention off-by-one:* spot-checked spans run one line longer
  in the actual source (e.g. `isa_get_size` is isa_bridge.cpp:50–**56** = 7
  lines where the table says 50–55 = 6; `abc_file_get_index_header` ends at
  701, not 700) — the tables stop at the catch-closing brace, not the
  function-closing one. The real deletable total is therefore slightly
  LARGER than the ≈852 estimate (order +100 lines). Direction-safe: the
  estimate is conservative; treat ≈852 as a floor, ≈0.9–1.0k lines as the
  honest range.
- **Not re-verified** (accepted as flagged): the §5.1 vendor file:line
  citations (37 rows — sampled rows 1, 20, 22, 32 checked out), the nm-level
  residuals the report itself flags.
