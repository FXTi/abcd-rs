# OpenHarmony Application Containers (`abcd-hap`)

`abcd-hap` is a pure-Rust, zero-C container reader for OpenHarmony and HarmonyOS NEXT application packages (`.hap`, `.hsp`, `.app`, `.hqf`), extracting bytecode payloads and manifest metadata directly from in-memory byte slices (`&[u8]`).

---

## 1. Design Constraints

- **Zero C / Native Dependencies**: Depends exclusively on `miniz_oxide` (pure-Rust DEFLATE) and `thiserror`, keeping cross-compilation trivial across 64-bit, 32-bit, Windows MSVC, and musl targets.
- **Zero-Copy Borrowed Fast Path**: Stored (`METHOD_STORED = 0`) entries in top-level `.hap`/`.hsp`/`.hqf` archives return `EntryData::Borrowed(&'a [u8])` slicing directly into the caller's input buffer, and `EntryMeta<'a>::name` borrows valid UTF-8 central-directory names as `Cow::Borrowed(&'a str)`. Deflated (`METHOD_DEFLATE = 8`) entries and inner `.hap`/`.hsp` payloads unpacked from `.app` bundles return `EntryData::Owned(Vec<u8>)`.
- **Adversarial Input Hardening**: Enforces strict checked bounds, pure-Rust IEEE 802.3 CRC-32 verification, configurable decompression `Limits` (per-entry, total-extraction, and RFC 1951 `1032×` DEFLATE ratio pre-checks), bounded EOCD candidate scanning, and explicit iterative container unpacking (zero call-stack recursion; maximum `.app` → `.hap`/`.hsp` depth `MAX_CONTAINER_DEPTH = 2`).

---

## 2. Container Formats & `.abc` Discovery

OpenHarmony packages are restricted PKZIP archives produced by upstream `developtools_packing_tool` (often carrying an appended APK/HAP v2/v3 code-signing block between the last local entry and the central directory):

| Kind | Extension | Manifest | `.abc` Entry Layouts |
| :--- | :--- | :--- | :--- |
| **Stage Ability / Shared Library** | `.hap`, `.hsp` | `module.json` | `ets/modules.abc` (merged bundle) or per-ability `ets/<Ability>/<Name>.abc` |
| **FA Legacy Ability** | `.hap` | `config.json` | `assets/js/<module>/*.abc` |
| **Quick Fix Patch** | `.hqf` | `patch.json` | `ets/*.abc` |
| **App Pack Bundle** | `.app` | `pack.info` + nested `.hap`/`.hsp` | Each nested `.hap`/`.hsp` archive unpacked iteratively in central-directory order |

### Enumeration Contract (`abc_modules` / `abc_modules_with_limits`)
1. Within a single module container (`Container::Module`), `ets/modules.abc` is emitted **first** when present, followed by all remaining `.abc` entries (allocation-free ASCII case-insensitive `.abc` suffix match) in central-directory order.
2. Every extracted `AbcModule<'a>` carries its `entry_name`, `container_path` provenance chain (for `.app` bundles), `EntryData<'a>`, `Compression` metadata, and associated manifest JSON (`module_json` from `module.json` / `config.json`, plus `patch_json` from `patch.json`) when present.
3. Inside `Container::App`, resource-only or native-only nested `.hap`/`.hsp` archives that contain zero `.abc` entries are skipped cleanly (`Error::NoAbcEntry` is returned only when the entire container yields zero `.abc` modules across all nested packages, whereas structural corruption or CRC errors propagate immediately).

---

## 3. ZIP Parsing & Security Invariants

1. **Signing-Block Safe & DoS-Bounded EOCD Discovery**: Scans backward up to the `65,535`-byte ZIP comment ceiling for position-consistent `PK\x05\x06` candidates (`pos + 22 + comment_len == len`), pre-filters non-empty central directories in `O(1)` by requiring `PK\x01\x02` at `cd_offset`, and caps full central-directory walk attempts so crafted EOCD floods cannot trigger quadratic scans.
2. **Authoritative Local Header Offsets**: Uses the central directory for entry discovery, compression method, CRC-32, and sizes, then validates each entry's `PK\x03\x04` local header variable-length filename/extra fields to compute the exact payload range.
3. **Integrity & Decompression Bomb Defenses**: Rejects multi-disk (`Error::MultiDisk`), ZIP64 (`Error::Zip64`), encrypted (`Error::Encrypted`), and unsupported compression (`Error::UnsupportedMethod`) entries; enforces `Limits` (`Error::EntryTooLarge`) and RFC 1951 DEFLATE ratio bounds before allocating; verifies inflated byte length against the central directory (`Error::Inflate`); and verifies IEEE CRC-32 on both `STORED` and `DEFLATE` reads (`Error::CrcMismatch`).
4. **Zip-Slip Prevention**: `abcd-hap` operates purely in memory and never touches the host filesystem; downstream file-writing consumers (`abcd-cli`) sanitize module/entry names before constructing output paths.
