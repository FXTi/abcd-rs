//! Synthetic fixture builders for abcd-cli tests.
//!
//! Zero binary fixtures: the mini ZIP writer below produces STORED-only
//! archives (the restricted container dialect abcd-hap reads), and
//! [`tiny_abc`] synthesizes a minimal valid .abc through
//! `abcd_file::Builder` (precedent: tests/lift-decompile/n74_*.rs).
#![allow(dead_code)]

use std::path::PathBuf;

use abcd_file::{AccessFlags, Builder, CodeEntity, Type};

// ---------------------------------------------------------------------------
// Mini ZIP writer (STORED entries only — ~50 lines by design)
// ---------------------------------------------------------------------------

fn crc32(data: &[u8]) -> u32 {
    let mut crc = 0xFFFF_FFFFu32;
    for &b in data {
        crc ^= u32::from(b);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xEDB8_8320 & (crc & 1).wrapping_neg());
        }
    }
    !crc
}

fn w16(out: &mut Vec<u8>, v: u16) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn w32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

/// Build a STORED-only ZIP archive from (name, data) pairs.
pub fn zip(entries: &[(&str, &[u8])]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut local_offsets = Vec::new();
    for (name, data) in entries {
        local_offsets.push(out.len() as u32);
        w32(&mut out, 0x0403_4b50); // local file header
        w16(&mut out, 20); // version needed
        w16(&mut out, 0); // flags
        w16(&mut out, 0); // method: STORED
        w16(&mut out, 0); // mod time
        w16(&mut out, 0); // mod date
        w32(&mut out, crc32(data));
        w32(&mut out, data.len() as u32); // compressed size
        w32(&mut out, data.len() as u32); // uncompressed size
        w16(&mut out, name.len() as u16);
        w16(&mut out, 0); // extra len
        out.extend_from_slice(name.as_bytes());
        out.extend_from_slice(data);
    }
    let cd_offset = out.len() as u32;
    for ((name, data), local) in entries.iter().zip(&local_offsets) {
        w32(&mut out, 0x0201_4b50); // central directory entry
        w16(&mut out, 20); // version made by
        w16(&mut out, 20); // version needed
        w16(&mut out, 0); // flags
        w16(&mut out, 0); // method: STORED
        w16(&mut out, 0); // mod time
        w16(&mut out, 0); // mod date
        w32(&mut out, crc32(data));
        w32(&mut out, data.len() as u32);
        w32(&mut out, data.len() as u32);
        w16(&mut out, name.len() as u16);
        w16(&mut out, 0); // extra len
        w16(&mut out, 0); // comment len
        w16(&mut out, 0); // disk start
        w16(&mut out, 0); // internal attrs
        w32(&mut out, 0); // external attrs
        w32(&mut out, *local);
        out.extend_from_slice(name.as_bytes());
    }
    let cd_size = out.len() as u32 - cd_offset;
    w32(&mut out, 0x0605_4b50); // end of central directory
    w16(&mut out, 0);
    w16(&mut out, 0);
    w16(&mut out, entries.len() as u16);
    w16(&mut out, entries.len() as u16);
    w32(&mut out, cd_size);
    w32(&mut out, cd_offset);
    w16(&mut out, 0); // comment len
    out
}

// ---------------------------------------------------------------------------
// Container builders
// ---------------------------------------------------------------------------

/// Stage-model module manifest carrying the given module name.
pub fn module_json(name: &str) -> Vec<u8> {
    format!(r#"{{"app":{{"bundleName":"com.example.t"}},"module":{{"name":"{name}"}}}}"#)
        .into_bytes()
}

/// A `.hap`-shaped archive: `module.json` + `ets/modules.abc`.
pub fn hap(module_name: &str, abc: &[u8]) -> Vec<u8> {
    zip(&[
        ("module.json", &module_json(module_name)),
        ("ets/modules.abc", abc),
    ])
}

/// A `.hap` without a manifest (name falls back to provenance).
pub fn hap_no_manifest(abc: &[u8]) -> Vec<u8> {
    zip(&[("ets/modules.abc", abc)])
}

/// An `.app`-shaped archive: nested haps as top-level entries.
pub fn app(nested: &[(&str, Vec<u8>)]) -> Vec<u8> {
    let entries: Vec<(&str, &[u8])> = nested.iter().map(|(n, b)| (*n, b.as_slice())).collect();
    zip(&entries)
}

// ---------------------------------------------------------------------------
// Synthetic .abc
// ---------------------------------------------------------------------------

/// Minimal valid .abc: 12.x file, global class, one static method
/// `func_main_0() { return; }` (the real entry-point name, so the
/// decompiler's `--call-entry` path is exercisable).
pub fn tiny_abc() -> Vec<u8> {
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = abcd_isa::encode(&[abcd_isa::Bytecode::Return]).unwrap();
    b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 0);
    b.deduplicate();
    b.finalize().expect("tiny_abc must finalize")
}

/// Decode-ok / lift-fail fixture: `f() { return this.key; }` via the
/// `ldthisbyname` opcode. The `this-by-*` family is IC-fused `this`
/// property access that es2panda never emits, and the lifter refuses it
/// loudly (`LiftError::UnsupportedThisByAccess`, N51 ruling — precedent:
/// abcd-lift/tests/lift_this_by_unsupported.rs). The file itself decodes
/// cleanly, so CLI commands reach their lift stage and must map the
/// failure to a tool error.
pub fn lift_fail_abc() -> Vec<u8> {
    use abcd_isa::{Bytecode, EntityId, Imm};
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let placeholder = EntityId(u16::MAX as u32);
    let (code, offsets) = abcd_isa::encode(&[
        Bytecode::Ldthisbyname(Imm(0), placeholder), // 0: acc = this.key
        Bytecode::Returnundefined,                   // 1
    ])
    .unwrap();
    let m = b.class_add_method(cls, "f", proto, AccessFlags::STATIC, &code, 1, 0);
    let key = b.add_string("key");
    b.relocate_code_id(m, offsets[0], 0, CodeEntity::String(key))
        .unwrap();
    b.deduplicate();
    b.finalize().expect("lift_fail_abc must finalize")
}

/// `func_main_0() { return 1 + 2; }` — a constant-foldable body, so the
/// abcd-opt pipeline reports a change (the `optimized_changed` stat and
/// the dispatch layer's ", optimized" summary tag).
pub fn foldable_abc() -> Vec<u8> {
    use abcd_isa::{Bytecode, Imm, Reg};
    let mut b = Builder::new();
    b.set_api(12, "");
    let cls = b.add_global_class();
    let proto = b.create_proto(Type::Void, &[]);
    let (code, _offsets) = abcd_isa::encode(&[
        Bytecode::Ldai(Imm(1)),         // 0: acc = 1
        Bytecode::Sta(Reg(0)),          // 1: v0 = 1
        Bytecode::Ldai(Imm(2)),         // 2: acc = 2
        Bytecode::Add2(Imm(0), Reg(0)), // 3: acc = 2 + v0
        Bytecode::Return,               // 4: return acc
    ])
    .unwrap();
    b.class_add_method(cls, "func_main_0", proto, AccessFlags::STATIC, &code, 4, 3);
    b.deduplicate();
    b.finalize().expect("foldable_abc must finalize")
}

// ---------------------------------------------------------------------------
// Scratch directories
// ---------------------------------------------------------------------------

/// Fresh per-test scratch directory under the system temp dir.
pub fn tempdir(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("abcd-cli-test-{}-{tag}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}
