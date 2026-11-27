//! Low-level raw C99 FFI bindings for the vendored C++ ArkCompiler ISA oracle (`24.0.0.0`).
//!
//! Pure-Rust production ISA decoding, encoding, entity relocation, and version
//! queries live in `abcd-isa` (`#![forbid(unsafe_code)]`), which links this
//! crate solely under `[dev-dependencies]` as an exhaustive differential test
//! oracle.
//!
//! # Quick start
//!
//! ```
//! let mut cur = [0u8; 4];
//! // SAFETY: `cur` is a valid 4-byte stack buffer.
//! unsafe { abcd_isa_sys::isa_get_version(cur.as_mut_ptr()) };
//! assert_eq!(cur, [24, 0, 0, 0]);
//! ```

#![cfg_attr(not(test), deny(clippy::unwrap_used))]

#[allow(
    non_upper_case_globals,
    non_camel_case_types,
    non_snake_case,
    dead_code,
    unused_parens,
    clippy::all,
    clippy::undocumented_unsafe_blocks,
    clippy::allow_attributes_without_reason,
    reason = "pre-generated C FFI bindings emitted by scripts/vendor-gen.py"
)]
mod generated {
    include!("generated/bindings.rs");
}

pub use generated::*;

#[cfg(test)]
#[expect(
    clippy::undocumented_unsafe_blocks,
    reason = "raw FFI smoke tests exercise generated unsafe extern C exports directly"
)]
mod tests {
    use super::*;

    #[test]
    fn emitter_build_reports_unbound_labels_and_null_guards() {
        unsafe {
            assert_eq!(isa_get_opcode(std::ptr::null()), u16::MAX);
            assert_eq!(isa_get_size_from_bytes(std::ptr::null()), 0);
            isa_get_version(std::ptr::null_mut());
            isa_get_min_version(std::ptr::null_mut());
            assert_eq!(isa_get_version_by_api(12, std::ptr::null_mut()), 1);
            assert_eq!(isa_is_version_compatible(std::ptr::null()), 0);
            assert_eq!(isa_is_version_incompatible(std::ptr::null()), 0);
            assert_eq!(isa_emitter_create_label(std::ptr::null_mut()), u32::MAX);
            assert_eq!(isa_emitter_bind(std::ptr::null_mut(), 0), -1);

            let e = isa_emitter_create();
            assert!(!e.is_null());
            let label = isa_emitter_create_label(e);
            assert_ne!(label, u32::MAX);

            // Emit `jmp <label>` (opcode 0x4d = 77) and deliberately never bind it.
            let jmp_op = isa_get_opcode([0x4du8, 0x00].as_ptr());
            assert_eq!(isa_is_jump_opcode(jmp_op), 1);
            let args = [i64::from(label)];
            let rc = isa_emitter_emit(e, jmp_op, args.as_ptr(), args.len());
            assert_eq!(rc, ISA_EMIT_OK as i32, "emit must succeed");

            let mut buf = std::ptr::dangling_mut::<u8>();
            let mut len = 77usize;
            let rc = isa_emitter_build(e, &mut buf, &mut len);
            assert_eq!(
                rc, ISA_BUILD_UNBOUND_LABELS as i32,
                "an unbound label must report ISA_BUILD_UNBOUND_LABELS"
            );
            assert!(buf.is_null(), "failed build must null the buffer");
            assert_eq!(len, 0, "failed build must zero the length");
            isa_emitter_destroy(e);
        }
    }

    #[test]
    fn emitter_build_bound_program_roundtrip() {
        unsafe {
            let e = isa_emitter_create();
            assert!(!e.is_null());
            let ret_undef_op = isa_get_opcode([0x65u8].as_ptr());
            assert_eq!(isa_is_terminator_opcode(ret_undef_op), 1);
            assert_eq!(
                isa_emitter_emit(e, ret_undef_op, std::ptr::null(), 0),
                ISA_EMIT_OK as i32
            );
            let mut buf = std::ptr::null_mut::<u8>();
            let mut len = 0usize;
            assert_eq!(
                isa_emitter_build(e, &mut buf, &mut len),
                ISA_BUILD_OK as i32
            );
            assert!(!buf.is_null());
            assert_eq!(len, 1);
            isa_emitter_free_buf(buf);
            isa_emitter_destroy(e);
        }
    }

    #[test]
    fn version_exports_answer_queries() {
        unsafe {
            let mut cur = [0u8; 4];
            isa_get_version(cur.as_mut_ptr());
            assert_ne!(cur, [0, 0, 0, 0]);
            let mut min = [0u8; 4];
            isa_get_min_version(min.as_mut_ptr());
            assert!(min <= cur);

            assert_eq!(isa_is_version_compatible(cur.as_ptr()), 1);
            assert_eq!(
                isa_is_version_compatible([0xFF, 0xFF, 0xFF, 0xFF].as_ptr()),
                0
            );

            let mut out = [0u8; 4];
            assert_eq!(isa_get_version_by_api(12, out.as_mut_ptr()), 0);
            assert_ne!(out, [0, 0, 0, 0]);
            assert_eq!(isa_get_version_by_api(250, out.as_mut_ptr()), 1);
            assert_eq!(
                isa_get_version_by_api_sub(12, c"beta1".as_ptr(), out.as_mut_ptr()),
                0
            );

            let count = isa_incompatible_version_count();
            let mut probe = [0xAAu8; 4];
            isa_incompatible_version_at(count, probe.as_mut_ptr());
            assert_eq!(probe, [0xAA; 4]);
            for i in 0..count {
                let mut v = [0u8; 4];
                isa_incompatible_version_at(i, v.as_mut_ptr());
                assert_eq!(isa_is_version_incompatible(v.as_ptr()), 1);
            }
        }
    }
}
