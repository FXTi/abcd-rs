# OpenHarmony Application Containers (`abcd-hap`)

`abcd-hap` is a pure-Rust, zero-C container reader for OpenHarmony and HarmonyOS NEXT application packages (`.hap`, `.hsp`, `.app`, `.hqf`), extracting bytecode payloads and manifest metadata directly from in-memory byte slices (`&[u8]`).

---

## 1. Design Constraints

- **Zero C / Native Dependencies**: Depends exclusively on `miniz_oxide` (pure-Rust Deflate) and `thiserror`, keeping cross-compilation trivial across 64-bit, 32-bit, Windows MSVC, and musl targets.
- **Zero-Copy Borrowed Fast Path**: Stored (`method = 0`) entries in top-level `.hap`/`.hsp`/`.hqf` archives return `Payload::Borrowed(&'a [u8])` slicing directly into the caller's input buffer; deflated (`method = 8`) entries and inner `.hap`/`.hsp` entries unpacked from `.app` bundles return `Payload::Owned(Vec<u8>)`.
- **Adversarial Input Hardening**: Enforces strict bounds, decompression size checks, path sanitization, and bounded container nesting (zero recursion; maximum `.app` → `.hap`/`.hsp` depth of `2`).

---

## 2. Container Formats & `.abc` Discovery

OpenHarmony packages are standard PKZIP archives produced by upstream `developtools_packing_tool` (often carrying an appended APK/HAP v2/v3 code-signing block between the last local entry / central directory and the EOCD record):

| Kind | Extension | Manifest | `.abc` Entry Layouts |
| :--- | :--- | :--- | :--- |
| **Stage Ability / Shared Library** | `.hap`, `.hsp` | `module.json` | `ets/modules.abc` (merged bundle) or per-ability `ets/<Ability>/<Name>.abc` |
| **FA Legacy Ability** | `.hap` | `config.json` | `assets/js/<module>/*.abc` |
| **Quick Fix Patch** | `.hqf` | `patch.json` | `ets/*.abc` |
| **App Pack Bundle** | `.app` | `pack.info` + nested `.hap`/`.hsp` | Each nested `.hap`/`.hsp` archive unpacked and enumerated in central-directory order |

### Enumeration Contract (`abc_modules` / `unpack`)
1. Within a single module container, `ets/modules.abc` (case-insensitive `.abc` suffix check) is emitted **first** when present, followed by all remaining `.abc` entries in central-directory order.
2. Every extracted `AbcModule<'a>` carries its `entry_name`, `provenance` chain (for `.app` bundles), `Payload<'a>`, and associated manifest JSON (`module.json`, `config.json`, or `patch.json`) when present.
3. Archives containing zero `.abc` entries (e.g., pure resource packs) return `Err(Error::NoAbcEntry)`.

---

## 3. ZIP Parsing & Security Invariants

1. **Signing-Block Safe EOCD Discovery**: Scans backward up to the `65,535`-byte ZIP comment ceiling for the `PK\x05\x06` signature and validates that the candidate EOCD's central-directory `[cd_offset .. cd_offset + cd_size]` span fits inside the buffer and starts with `PK\x01\x02` (defeating fake `PK\x05\x06` bytes inside comments).
2. **Authoritative Local Header Offsets**: Uses the central directory for entry discovery and sizes, then validates each entry's `PK\x03\x04` local header variable-length filename/extra fields to compute the exact payload slice.
3. **Decompression Bomb & Truncation Checks**: Rejects ZIP64 (`Error::Zip64Unsupported`), encrypted entries, unsupported compression methods (`Error::UnsupportedMethod`), CRC-32 mismatches (`Error::CrcMismatch`), and inflated byte counts that diverge from the declared uncompressed size (`Error::SizeMismatch`).
4. **Zip-Slip Prevention**: Consumers (`abcd-cli extract`, `abcd-decompile --split-modules`) sanitize all archive entry names and `module.json` module names, rejecting `/`, `\`, `..`, drive prefixes, and control characters before touching the host filesystem.
