//! Malformed-offset catch matrix for the file bridge's FFI guards, plus the
//! builder-side invalid-handle guard negatives (c-COV W11).
//!
//! Mechanism: abcd-file-sys/build.rs defines SUPPORT_KNOWN_EXCEPTION, so the
//! vendored bounds checks (`File::GetSpanFromId`, `helpers::Read*`,
//! `Resolve*Index`) THROW on malformed offsets, and every bridge export wraps
//! its body in `try { ... } catch (...) { return <sentinel>; }`. Each test
//! drives one or more of those catch guards (or the explicit guard returns
//! above them) through the raw FFI and asserts the exact error sentinel.
//! Every test also pins a positive contrast on the same accessor family, so
//! the sentinel is never confused with a legitimate value; the test
//! completing at all proves no exception escapes across the FFI boundary.
//!
//! Crafts that need item internals start from one builder-produced "rich"
//! fixture (class with an interface, an annotated field with an initial
//! value, and an annotated method with code and debug info); offsets are
//! discovered through the bridge's own enumerate exports and patched in a
//! copy of the bytes before re-opening.

use abcd_file_sys::*;
use std::ffi::c_void;

// ---------------------------------------------------------------------------
// Byte-level helpers
// ---------------------------------------------------------------------------

fn u32_at(data: &[u8], pos: usize) -> u32 {
    u32::from_le_bytes(data[pos..pos + 4].try_into().unwrap())
}

fn write_u32(data: &mut [u8], pos: usize, v: u32) {
    data[pos..pos + 4].copy_from_slice(&v.to_le_bytes());
}

/// Decode a ULEB128 at `pos`; returns (value, next position).
fn uleb128(data: &[u8], mut pos: usize) -> (u32, usize) {
    let mut result = 0u32;
    let mut shift = 0;
    loop {
        let byte = data[pos];
        pos += 1;
        result |= u32::from(byte & 0x7f) << shift;
        if byte & 0x80 == 0 {
            break;
        }
        shift += 7;
    }
    (result, pos)
}

/// Minimal openable file: 60-byte header + 4 filler bytes (so offset 64
/// addresses the appended payload), then `extra`. Declared file_size is the
/// buffer length.
fn minimal_file(extra: &[u8]) -> Vec<u8> {
    let mut data: Vec<u8> = Vec::new();
    data.extend_from_slice(b"PANDA\0\0\0"); // magic (8)
    data.extend_from_slice(&0u32.to_le_bytes()); // checksum
    data.extend_from_slice(&[12, 0, 2, 0]); // version
    data.extend_from_slice(&0u32.to_le_bytes()); // file_size (patched below)
    for _ in 0..10 {
        data.extend_from_slice(&0u32.to_le_bytes()); // foreign..index header fields
    }
    data.extend_from_slice(&[0u8; 4]); // filler -> payload starts at 64
    data.extend_from_slice(extra);
    let size = data.len() as u32;
    data[16..20].copy_from_slice(&size.to_le_bytes());
    data
}

unsafe fn open(data: &[u8]) -> *mut AbcFileHandle {
    let f = unsafe { abc_file_open(data.as_ptr(), data.len()) };
    assert!(!f.is_null(), "craft must remain openable");
    f
}

// ---------------------------------------------------------------------------
// Rich fixture (builder-produced)
// ---------------------------------------------------------------------------

/// Build the rich fixture: global class implementing a foreign interface,
/// one annotated field with an initial value, and one annotated method with
/// code, a source language, a typed parameter, and full debug info (source
/// file/code, line and column tables, one local variable, one parameter).
unsafe fn build_rich() -> Vec<u8> {
    unsafe {
        let b = abc_builder_new();
        assert!(!b.is_null());
        // API 9: the 12.x builder output drops method proto references
        // (proto_idx = INVALID_INDEX_16 — the pre-existing quirk
        // proto_queries.rs works around the same way), and this fixture's
        // proto contrasts need a real proto item.
        abc_builder_set_api(b, 9, c"".as_ptr());
        let cls = abc_builder_add_global_class(b);
        assert_ne!(cls, u32::MAX);
        let iface = abc_builder_add_foreign_class(b, c"LIface;".as_ptr());
        assert_ne!(iface, u32::MAX);
        abc_builder_class_add_interface(b, cls, iface);

        let ann_cls = abc_builder_add_class(b, c"LAnno;".as_ptr());
        let elem_name = abc_builder_add_string(b, c"value".as_ptr());
        let elem = AbcAnnotationElemDefEx {
            name_string_handle: elem_name,
            tag: b'7' as std::ffi::c_char,
            is_array: 0,
            scalar_value: 111,
            scalar_value_64: 0,
            array_values: std::ptr::null(),
            array_count: 0,
        };
        let cls_ann = abc_builder_create_annotation_ex(b, ann_cls, &elem, 1);
        assert_ne!(cls_ann, u32::MAX);
        abc_builder_class_add_annotation(b, cls, cls_ann);

        let fld = abc_builder_class_add_field(b, cls, c"fx".as_ptr(), Type_TypeId_I32, 1);
        assert_ne!(fld, u32::MAX);
        abc_builder_field_set_value_i32(b, fld, 42);
        let fx_ann = abc_builder_create_annotation_ex(b, ann_cls, &elem, 1);
        abc_builder_field_add_annotation(b, fld, fx_ann);

        let rec = abc_builder_add_foreign_class(b, c"LRec;".as_ptr());
        let params = [AbcProtoParam {
            type_id: Type_TypeId_REFERENCE,
            class_handle: rec,
        }];
        let proto = abc_builder_create_proto_ex(b, Type_TypeId_TAGGED, 0, params.as_ptr(), 1);
        assert_ne!(proto, u32::MAX);
        let code: [u8; 1] = [0x65]; // returnundefined
        let m = abc_builder_class_add_method_with_proto(
            b,
            cls,
            c"mmethod".as_ptr(),
            proto,
            1, // ACC_PUBLIC
            code.as_ptr(),
            1,
            1,
            1,
        );
        assert_ne!(m, u32::MAX);
        abc_builder_method_set_source_lang(b, m, SourceLang_ECMASCRIPT);
        assert_eq!(abc_builder_method_add_param(b, m, Type_TypeId_TAGGED), 0);
        let m_ann = abc_builder_create_annotation_ex(b, ann_cls, &elem, 1);
        abc_builder_method_add_annotation(b, m, m_ann);

        let lnp = abc_builder_create_lnp(b);
        let debug = abc_builder_create_debug_info(b, lnp, 100);
        assert_ne!(debug, u32::MAX);
        let src = abc_builder_add_string(b, c"m.js".as_ptr());
        let src_code = abc_builder_add_string(b, c"function m() {}".as_ptr());
        let local_name = abc_builder_add_string(b, c"x".as_ptr());
        let local_type = abc_builder_add_string(b, c"i32".as_ptr());
        let param_name = abc_builder_add_string(b, c"p0".as_ptr());
        abc_builder_lnp_emit_set_file(b, lnp, debug, src);
        abc_builder_lnp_emit_set_source_code(b, lnp, debug, src_code);
        abc_builder_lnp_emit_advance_pc(b, lnp, debug, 0);
        abc_builder_lnp_emit_advance_line(b, lnp, debug, 5);
        abc_builder_lnp_emit_column(b, lnp, debug, 0, 7);
        abc_builder_lnp_emit_start_local(b, lnp, debug, 0, local_name, local_type);
        abc_builder_lnp_emit_end_local(b, lnp, 0);
        abc_builder_debug_add_param(b, debug, param_name);
        abc_builder_lnp_emit_end(b, lnp);
        abc_builder_method_set_debug_info(b, m, debug);

        let mut out_len = 0u32;
        let ptr = abc_builder_finalize(b, &mut out_len);
        assert!(!ptr.is_null(), "rich fixture must finalize");
        let data = std::slice::from_raw_parts(ptr, out_len as usize).to_vec();
        abc_builder_free(b);
        data
    }
}

// ---------------------------------------------------------------------------
// Item walkers (vendored layouts, mirroring the data accessors)
// ---------------------------------------------------------------------------

/// Offset of the class item whose inline descriptor equals `name`
/// (class item = StringItem(descriptor) + fields).
fn class_off_by_name(data: &[u8], name: &str) -> usize {
    let class_idx_off = u32_at(data, 32) as usize;
    let num_classes = u32_at(data, 28) as usize;
    for i in 0..num_classes {
        let off = u32_at(data, class_idx_off + 4 * i) as usize;
        let (_, p) = uleb128(data, off);
        let end = p + name.len();
        if &data[p..end] == name.as_bytes() && data[end] == 0 {
            return off;
        }
    }
    panic!("class {name} not found");
}

/// Class item layout (class_data_accessor.cpp ctor):
/// `[uleb utf16_len][MUTF-8 name][NUL][u32 super][uleb flags]
///  [uleb num_fields][uleb num_methods]([0x01][uleb n][u16 x n interfaces])*
///  <tagged section>`
/// Returns `(tagged_start, interfaces_u16_pos)`.
fn class_tag_section(data: &[u8], class_off: usize) -> (usize, Option<usize>) {
    let mut pos = class_off;
    let (_, p) = uleb128(data, pos);
    pos = p;
    while data[pos] != 0 {
        pos += 1;
    }
    pos += 1; // NUL
    pos += 4; // super_class_off
    let (_, p) = uleb128(data, pos);
    pos = p; // access_flags
    let (_, p) = uleb128(data, pos);
    pos = p; // num_fields
    let (_, p) = uleb128(data, pos);
    pos = p; // num_methods
    let mut ifaces = None;
    // Ctor tag loop: only INTERFACES (0x01) sits below SOURCE_LANG (0x02).
    while data[pos] != 0 && data[pos] < 2 {
        pos += 1;
        let (num_ifaces, p) = uleb128(data, pos);
        pos = p;
        ifaces = Some(pos);
        pos += 2 * num_ifaces as usize;
    }
    (pos, ifaces)
}

/// Cut the file at `cut`, fixing the declared file size. Accessors opened on
/// the truncated file still resolve their fixed headers (index sections and
/// item headers precede the cut); the lazy tagged walks hit the truncated
/// value and throw into the catch guards.
fn truncate_at(data: &[u8], cut: usize) -> Vec<u8> {
    let mut out = data[..cut].to_vec();
    write_u32(&mut out, 16, cut as u32);
    out
}

/// Method item: `[u16 class_idx][u16 proto_idx][u32 name_off][uleb flags]
/// <tagged>`.
fn method_tagged_start(data: &[u8], method_off: usize) -> usize {
    let (_, p) = uleb128(data, method_off + 8);
    p
}

/// Field item: `[u16 class_idx][u16 type_idx][u32 name_off][uleb flags]
/// <tagged>`.
fn field_tagged_start(data: &[u8], field_off: usize) -> usize {
    let (_, p) = uleb128(data, field_off + 8);
    p
}

unsafe extern "C" fn collect_u32(off: u32, ctx: *mut c_void) {
    unsafe { (*(ctx as *mut Vec<u32>)).push(off) };
}

/// Method and field item offsets of one class, discovered through the
/// bridge's own enumerate exports.
unsafe fn class_members(f: *const AbcFileHandle, class_off: u32) -> (Vec<u32>, Vec<u32>) {
    unsafe {
        let ca = abc_class_open(f, class_off);
        assert!(!ca.is_null());
        let mut methods: Vec<u32> = Vec::new();
        abc_class_enumerate_methods(
            ca,
            Some(collect_u32),
            &mut methods as *mut Vec<u32> as *mut c_void,
        );
        let mut fields: Vec<u32> = Vec::new();
        abc_class_enumerate_fields(
            ca,
            Some(collect_u32),
            &mut fields as *mut Vec<u32> as *mut c_void,
        );
        abc_class_close(ca);
        (methods, fields)
    }
}

/// Run `body` with (data, class_off, method_off, field_off) of the rich
/// fixture. The method/field offsets are looked up once through the bridge.
fn with_rich(body: impl Fn(&[u8], usize, u32, u32)) {
    let data = unsafe { build_rich() };
    // The class index table is descriptor-sorted: LAnno; precedes
    // L_GLOBAL;, so the fixture's member-owning class is looked up by name.
    let class_off = class_off_by_name(&data, "L_GLOBAL;");
    let (methods, fields) = unsafe {
        let f = open(&data);
        let members = class_members(f, class_off as u32);
        abc_file_close(f);
        members
    };
    assert_eq!(methods.len(), 1, "rich fixture has one method");
    assert_eq!(fields.len(), 1, "rich fixture has one field");
    body(&data, class_off, methods[0], fields[0]);
}

// ---------------------------------------------------------------------------
// Proto family
// ---------------------------------------------------------------------------

/// A proto accessor opened at a one-byte span: every getter re-reads the
/// shorty through the span and throws; the catch guards must return the
/// per-getter sentinel. Positive contrast on the rich fixture's
/// reference-typed proto.
#[test]
fn proto_getters_reject_truncated_span() {
    with_rich(|data, _, method_off, _| unsafe {
        let f = open(data);
        let mr = abc_method_open(f, method_off);
        assert!(!mr.is_null());
        let proto_off = abc_method_get_proto_id(mr);
        abc_method_close(mr);
        assert_ne!(proto_off, u32::MAX);

        // Positive contrast: TAGGED return, one REFERENCE arg, one ref type.
        let pa = abc_proto_open(f, proto_off);
        assert!(!pa.is_null());
        assert_eq!(abc_proto_num_args(pa), 1);
        assert_eq!(abc_proto_get_return_type(pa), Type_TypeId_TAGGED);
        assert_eq!(abc_proto_get_arg_type(pa, 0), Type_TypeId_REFERENCE);
        assert_eq!(abc_proto_get_ref_num(pa), 1);
        let rec_off = abc_proto_get_reference_type(pa, 0);
        assert_ne!(rec_off, u32::MAX);
        assert_ne!(rec_off, 0);
        let mut types: Vec<u8> = Vec::new();
        unsafe extern "C" fn collect_type(t: u8, ctx: *mut c_void) {
            unsafe { (*(ctx as *mut Vec<u8>)).push(t) };
        }
        abc_proto_enumerate_types(
            pa,
            Some(collect_type),
            &mut types as *mut Vec<u8> as *mut c_void,
        );
        assert_eq!(types, vec![Type_TypeId_TAGGED, Type_TypeId_REFERENCE]);
        abc_proto_close(pa);

        // One-byte span at EOF: every shorty read throws into the guards.
        let file_size = abc_file_size(f);
        let bad = abc_proto_open(f, file_size - 1);
        assert!(!bad.is_null(), "the proto ctor itself never dereferences");
        assert_eq!(abc_proto_num_args(bad), 0, "shorty read must fail");
        assert_eq!(abc_proto_get_return_type(bad), u8::MAX);
        assert_eq!(abc_proto_get_arg_type(bad, 0), u8::MAX);
        assert_eq!(abc_proto_get_reference_type(bad, 0), u32::MAX);
        assert_eq!(abc_proto_get_ref_num(bad), 0);
        let mut got: Vec<u8> = Vec::new();
        abc_proto_enumerate_types(
            bad,
            Some(collect_type),
            &mut got as *mut Vec<u8> as *mut c_void,
        );
        assert!(got.is_empty(), "a failing enumeration delivers nothing");
        abc_proto_close(bad);
        abc_file_close(f);
    });
}

// ---------------------------------------------------------------------------
// Class family
// ---------------------------------------------------------------------------

/// abc_class_open past the declared file size must fail with nullptr
/// (GetSpanFromId throws into the catch guard).
#[test]
fn class_open_rejects_out_of_file_offset() {
    let data = minimal_file(&[0u8; 8]);
    unsafe {
        let f = open(&data);
        assert!(abc_class_open(f, 0xFFFF_FF00).is_null());
        assert!(abc_method_open(f, 0xFFFF_FF00).is_null());
        assert!(abc_code_open(f, 0xFFFF_FF00).is_null());
        assert!(abc_field_open(f, 0xFFFF_FF00).is_null());
        abc_file_close(f);
    }
}

/// A truncated class tagged value (a matching tag byte whose u32/byte value
/// is cut off at EOF) throws on every lazy tag walk — source lang, source
/// file, all four annotation enumerations, and the field/method
/// enumerations that bottom out in the same walk — while the eagerly cached
/// getters keep answering. Covers the class-family catch guards.
#[test]
fn class_lazy_getters_reject_truncated_tag_value() {
    with_rich(|data, class_off, _, _| {
        let (tag_start, _) = class_tag_section(data, class_off);
        // The rich fixture's first class tag is ANNOTATION (0x04).
        assert_eq!(data[tag_start], 0x04);
        unsafe extern "C" fn count_cb(_off: u32, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        // (trap tag byte, bytes of its value to keep before the cut).
        // 0x04 also fails the field/method enumerations via the skip chain.
        for trap in [0x04u8, 0x03, 0x05, 0x06, 0x07] {
            let mut craft = data.to_vec();
            craft[tag_start] = trap;
            let craft = truncate_at(&craft, tag_start + 3);
            unsafe {
                let f = open(&craft);
                let ca = abc_class_open(f, class_off as u32);
                assert!(!ca.is_null(), "trap {trap:#x}: ctor stops before the tags");
                // Eagerly cached getters are unaffected (contrast).
                assert_eq!(abc_class_access_flags(ca), 0);
                assert_ne!(abc_class_get_class_id(ca), u32::MAX);
                assert_eq!(abc_class_get_ifaces_number(ca), 1);
                let mut hits = 0usize;
                let ctx = &mut hits as *mut usize as *mut c_void;
                match trap {
                    0x03 => abc_class_enumerate_runtime_annotations(ca, Some(count_cb), ctx),
                    0x05 => abc_class_enumerate_runtime_type_annotations(ca, Some(count_cb), ctx),
                    0x06 => abc_class_enumerate_type_annotations(ca, Some(count_cb), ctx),
                    0x07 => assert_eq!(abc_class_source_file_off(ca), u32::MAX),
                    _ => {
                        abc_class_enumerate_annotations(ca, Some(count_cb), ctx);
                        let mut members: Vec<u32> = Vec::new();
                        let mctx = &mut members as *mut Vec<u32> as *mut c_void;
                        abc_class_enumerate_methods(ca, Some(collect_u32), mctx);
                        abc_class_enumerate_fields(ca, Some(collect_u32), mctx);
                        assert!(members.is_empty(), "member walks hit the same trap");
                    }
                }
                assert_eq!(hits, 0, "trap {trap:#x}: a failing walk delivers nothing");
                abc_class_close(ca);
                abc_file_close(f);
            }
        }
        // SOURCE_LANG (0x02) carries a one-byte value: cut right after the
        // tag byte itself.
        let mut craft = data.to_vec();
        craft[tag_start] = 0x02;
        let craft = truncate_at(&craft, tag_start + 1);
        unsafe {
            let f = open(&craft);
            let ca = abc_class_open(f, class_off as u32);
            assert!(!ca.is_null());
            assert_eq!(abc_class_get_source_lang(ca), u8::MAX);
            abc_class_close(ca);
            abc_file_close(f);
        }
    });
}

/// A corrupted index header (its class_idx_off points past the declared
/// file size) makes the vendored `GetClassIndex` throw
/// `INVALID_INDEX_HEADER` on `abc_class_get_interface_id`; the cached
/// interface count still answers. (An out-of-range index VALUE alone does
/// not throw: `ResolveClassIndex` returns an empty EntityId for it — the
/// header consistency check is what reaches the catch guard.)
#[test]
fn class_interface_id_rejects_corrupt_index_header() {
    with_rich(|data, class_off, _, _| {
        let idx_sec = u32_at(data, 56) as usize;
        let mut patched = data.to_vec();
        // IndexHeader layout: start(+0) end(+4) class_idx_size(+8)
        // class_idx_off(+12).
        write_u32(&mut patched, idx_sec + 12, 0xFFFF_FF00);
        unsafe {
            let f = open(&patched);
            let ca = abc_class_open(f, class_off as u32);
            assert!(!ca.is_null(), "the class item itself is intact");
            assert_eq!(abc_class_get_ifaces_number(ca), 1, "count is cached");
            assert_eq!(
                abc_class_get_interface_id(ca, 0),
                u32::MAX,
                "the inconsistent index header must fail the resolve"
            );
            abc_class_close(ca);
            abc_file_close(f);
        }
        // Positive contrast on the unpatched fixture.
        unsafe {
            let f = open(data);
            let ca = abc_class_open(f, class_off as u32);
            assert!(!ca.is_null());
            let id = abc_class_get_interface_id(ca, 0);
            assert_ne!(id, u32::MAX);
            assert_ne!(id, 0);
            abc_class_close(ca);
            abc_file_close(f);
        }
    });
}

// ---------------------------------------------------------------------------
// Method family
// ---------------------------------------------------------------------------

/// Truncated method tagged values: code/debug-info/source-lang getters and
/// all annotation/param-annotation enumerations throw into their catch
/// guards when their own tag's value is cut off at EOF; the ctor-cached
/// getters keep answering. The rich method's tagged section is
/// `[0x01 CODE u32][0x02 SOURCE_LANG u8][0x05 DEBUG_INFO u32]
/// [0x06 ANNOTATION u32][0x00]`.
#[test]
fn method_lazy_getters_reject_truncated_tag_value() {
    with_rich(|data, _, method_off, _| {
        let t0 = method_tagged_start(data, method_off as usize);
        // Pin the expected tagged layout.
        assert_eq!(data[t0], 0x01, "CODE");
        assert_eq!(data[t0 + 5], 0x02, "SOURCE_LANG");
        assert_eq!(data[t0 + 7], 0x05, "DEBUG_INFO");
        assert_eq!(data[t0 + 12], 0x06, "ANNOTATION");
        assert_eq!(data[t0 + 17], 0x00, "NOTHING");

        unsafe extern "C" fn count_cb(_off: u32, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        let run = |craft: &[u8], check: &dyn Fn(*mut AbcMethodAccessor)| {
            unsafe {
                let f = open(craft);
                let ma = abc_method_open(f, method_off);
                assert!(!ma.is_null(), "the ctor reads only the fixed header");
                // Cached getters (contrast).
                assert_eq!(abc_method_access_flags(ma), 1);
                assert_eq!(abc_method_get_method_id(ma), method_off);
                assert_eq!(abc_method_has_valid_proto(ma), 1);
                check(ma);
                abc_method_close(ma);
                abc_file_close(f);
            }
        };

        // CODE value cut to two bytes.
        run(&truncate_at(data, t0 + 3), &|ma| unsafe {
            assert_eq!(abc_method_code_off(ma), u32::MAX);
        });
        // SOURCE_LANG tag with no value byte at all.
        run(&truncate_at(data, t0 + 6), &|ma| unsafe {
            assert_eq!(abc_method_get_source_lang(ma), u8::MAX);
        });
        // DEBUG_INFO value cut.
        run(&truncate_at(data, t0 + 10), &|ma| unsafe {
            assert_eq!(abc_method_debug_info_off(ma), u32::MAX);
        });
        // RUNTIME_ANNOTATION trap where DEBUG_INFO sits (its chain position
        // is right after SOURCE_LANG).
        let mut craft = data.to_vec();
        craft[t0 + 7] = 0x03;
        run(&truncate_at(&craft, t0 + 10), &|ma| unsafe {
            let mut hits = 0usize;
            abc_method_enumerate_runtime_annotations(
                ma,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
        // RUNTIME_PARAM_ANNOTATION trap at the same chain position.
        let mut craft = data.to_vec();
        craft[t0 + 7] = 0x04;
        run(&truncate_at(&craft, t0 + 10), &|ma| unsafe {
            assert_eq!(abc_method_get_runtime_param_annotation_id(ma), u32::MAX);
        });
        // ANNOTATION value cut (compile-time bucket).
        run(&truncate_at(data, t0 + 15), &|ma| unsafe {
            let mut hits = 0usize;
            abc_method_enumerate_annotations(
                ma,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
        // PARAM_ANNOTATION trap where ANNOTATION sits.
        let mut craft = data.to_vec();
        craft[t0 + 12] = 0x07;
        run(&truncate_at(&craft, t0 + 15), &|ma| unsafe {
            assert_eq!(abc_method_get_param_annotation_id(ma), u32::MAX);
        });
        // TYPE_ANNOTATION trap.
        let mut craft = data.to_vec();
        craft[t0 + 12] = 0x08;
        run(&truncate_at(&craft, t0 + 15), &|ma| unsafe {
            let mut hits = 0usize;
            abc_method_enumerate_type_annotations(
                ma,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
        // RUNTIME_TYPE_ANNOTATION trap.
        let mut craft = data.to_vec();
        craft[t0 + 12] = 0x09;
        run(&truncate_at(&craft, t0 + 15), &|ma| unsafe {
            let mut hits = 0usize;
            abc_method_enumerate_runtime_type_annotations(
                ma,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
    });
}

// ---------------------------------------------------------------------------
// Field family
// ---------------------------------------------------------------------------

/// Truncated field tagged values: the four initial-value readers and the
/// four annotation enumerations throw into their catch guards when their
/// own tag's value is cut off at EOF; cached getters keep answering. The
/// rich field's tagged section is `[0x01 INT_VALUE sleb][0x04 ANNOTATION
/// u32][0x00]` (field_set_value_i32 stages an INTEGER ScalarValueItem).
#[test]
fn field_lazy_getters_reject_truncated_tag_value() {
    with_rich(|data, _, _, field_off| {
        let t0 = field_tagged_start(data, field_off as usize);
        assert_eq!(data[t0], 0x01, "INT_VALUE");
        assert_eq!(data[t0 + 1], 0x2a, "sleb(42)");
        assert_eq!(data[t0 + 2], 0x04, "ANNOTATION");
        assert_eq!(data[t0 + 7], 0x00, "NOTHING");

        unsafe extern "C" fn count_cb(_off: u32, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        let run = |craft: &[u8], check: &dyn Fn(*mut AbcFieldAccessor)| {
            unsafe {
                let f = open(craft);
                let fa = abc_field_open(f, field_off);
                assert!(!fa.is_null());
                // Cached getters (contrast).
                assert_eq!(abc_field_access_flags(fa), 1);
                assert_ne!(abc_field_name_off(fa), u32::MAX);
                assert_eq!(abc_field_get_field_id(fa), field_off);
                check(fa);
                abc_field_close(fa);
                abc_file_close(f);
            }
        };

        // INT_VALUE payload cut right after the tag byte: the sleb payload
        // span is empty and every value reader throws into its catch guard.
        run(&truncate_at(data, t0 + 1), &|fa| unsafe {
            let mut out32 = 0i32;
            let mut out64 = 0i64;
            let mut outf32 = 0f32;
            let mut outf64 = 0f64;
            assert_eq!(abc_field_get_value_i32(fa, &mut out32), 0);
            assert_eq!(abc_field_get_value_i64(fa, &mut out64), 0);
            assert_eq!(abc_field_get_value_f32(fa, &mut outf32), 0);
            assert_eq!(abc_field_get_value_f64(fa, &mut outf64), 0);
        });
        // ANNOTATION value cut to two bytes.
        run(&truncate_at(data, t0 + 5), &|fa| unsafe {
            let mut hits = 0usize;
            abc_field_enumerate_annotations(
                fa,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
        // RUNTIME_ANNOTATION trap where ANNOTATION sits. (The field's
        // TYPE/RUNTIME_TYPE buckets are not trappable: the vendored
        // FieldDataAccessor matches FieldTag::ANNOTATION for those
        // enumerations too — an upstream quirk — so a 0x05/0x06 record is
        // silently skipped, never read, and their catch guards are
        // unreachable-by-construction residual.)
        let mut craft = data.to_vec();
        craft[t0 + 2] = 0x03;
        run(&truncate_at(&craft, t0 + 5), &|fa| unsafe {
            let mut hits = 0usize;
            abc_field_enumerate_runtime_annotations(
                fa,
                Some(count_cb),
                &mut hits as *mut usize as *mut c_void,
            );
            assert_eq!(hits, 0);
        });
        // Positive contrast: the uncut field reads back 42.
        unsafe {
            let f = open(data);
            let fa = abc_field_open(f, field_off);
            assert!(!fa.is_null());
            let mut v = 0i32;
            assert_eq!(abc_field_get_value_i32(fa, &mut v), 1);
            assert_eq!(v, 42);
            abc_field_close(fa);
            abc_file_close(f);
        }
    });
}

// ---------------------------------------------------------------------------
// Module / module-request-phase / annotation / method-handle families
// ---------------------------------------------------------------------------

/// A module blob whose first section count runs the record walk out of the
/// span: `EnumerateModuleRecord` throws into the catch guard. The same blob
/// (zero requests) drives the `abc_module_request_off` index guard.
#[test]
fn module_enumerate_rejects_inflated_section_count() {
    // Blob at 64 (module_data_accessor.cpp ctor layout):
    // [u32 literalnum][u32 num_requests = 0][u32 regular_import_num = 0x1000]
    // followed by fewer bytes than one record entry needs.
    let blob = [
        0x00, 0x00, 0x00, 0x00, // literalnum
        0x00, 0x00, 0x00, 0x00, // num_requests
        0x00, 0x10, 0x00, 0x00, // regular_import_num
        0xAA, 0xBB, // truncated first entry
    ];
    let data = minimal_file(&blob);
    unsafe {
        let f = open(&data);
        let ma = abc_module_open(f, 64);
        assert!(!ma.is_null(), "the ctor reads only the request prefix");
        assert_eq!(abc_module_num_requests(ma), 0);
        assert_eq!(
            abc_module_request_off(ma, 0),
            u32::MAX,
            "index past the request table must fail"
        );
        let mut records = 0usize;
        unsafe extern "C" fn count_record(
            _t: u8,
            _e: u32,
            _r: u32,
            _i: u32,
            _l: u32,
            ctx: *mut c_void,
        ) {
            unsafe { *(ctx as *mut usize) += 1 };
        }
        abc_module_enumerate_records(
            ma,
            Some(count_record),
            &mut records as *mut usize as *mut c_void,
        );
        assert_eq!(records, 0, "the walk throws on the truncated entry");
        abc_module_close(ma);
        abc_file_close(f);
    }
}

/// The module-request-phase reader: null callback, a truncated flag run,
/// and an out-of-file offset each fail with -1; a well-formed blob returns
/// its flag count.
#[test]
fn module_request_phase_read_guards() {
    unsafe {
        let f = open(&minimal_file(&[0x02, 0x00, 0x00, 0x00, 0x01]));
        // Null callback.
        assert_eq!(
            abc_module_request_phase_read(f, 64, None, std::ptr::null_mut()),
            -1
        );
        unsafe extern "C" fn count_flag(_f: u8, ctx: *mut c_void) {
            unsafe { *(ctx as *mut usize) += 1 };
        }
        // Declared count 2 but only one flag byte: the short run fails.
        let mut flags = 0usize;
        assert_eq!(
            abc_module_request_phase_read(
                f,
                64,
                Some(count_flag),
                &mut flags as *mut usize as *mut c_void,
            ),
            -1
        );
        assert_eq!(flags, 1, "the first flag is delivered before the gap");
        // Out-of-file offset: GetSpanFromId throws into the guard.
        assert_eq!(
            abc_module_request_phase_read(f, 0xFFFF_FF00, Some(count_flag), std::ptr::null_mut()),
            -1
        );
        abc_file_close(f);

        // Positive control: two flags.
        let g = open(&minimal_file(&[0x02, 0x00, 0x00, 0x00, 0x01, 0x00]));
        let mut got = 0usize;
        assert_eq!(
            abc_module_request_phase_read(
                g,
                64,
                Some(count_flag),
                &mut got as *mut usize as *mut c_void,
            ),
            2
        );
        assert_eq!(got, 2);
        abc_file_close(g);
    }
}

/// Annotation element index guards: idx past the element count fails with
/// -1 on all five per-index getters.
#[test]
fn annotation_getters_reject_out_of_range_index() {
    // Locate the class annotation through the bridge.
    let data = unsafe { build_rich() };
    unsafe {
        let f = open(&data);
        let ca = abc_class_open(f, class_off_by_name(&data, "L_GLOBAL;") as u32);
        assert!(!ca.is_null());
        let mut anns: Vec<u32> = Vec::new();
        unsafe extern "C" fn collect_ann(off: u32, ctx: *mut c_void) -> i32 {
            unsafe { (*(ctx as *mut Vec<u32>)).push(off) };
            0
        }
        abc_class_enumerate_annotations(
            ca,
            Some(collect_ann),
            &mut anns as *mut Vec<u32> as *mut c_void,
        );
        abc_class_close(ca);
        assert_eq!(anns.len(), 1);
        let aa = abc_annotation_open(f, anns[0]);
        assert!(!aa.is_null());
        assert_eq!(abc_annotation_count(aa), 1);
        assert_ne!(abc_annotation_class_off(aa), u32::MAX);

        let mut elem = AbcAnnotationElem {
            name_off: 0,
            tag: 0,
            value: 0,
        };
        assert_eq!(abc_annotation_get_element(aa, 1, &mut elem), -1);
        let mut arr = AbcAnnotationArrayVal {
            count: 0,
            entity_off: 0,
        };
        assert_eq!(abc_annotation_get_array_element(aa, 1, &mut arr), -1);
        let mut v64 = 0i64;
        assert_eq!(abc_annotation_get_value_i64(aa, 1, &mut v64), -1);
        let mut u64v = 0u64;
        assert_eq!(abc_annotation_get_value_u64(aa, 1, &mut u64v), -1);
        let mut f64v = 0f64;
        assert_eq!(abc_annotation_get_value_f64(aa, 1, &mut f64v), -1);
        // Positive contrast at idx 0.
        assert_eq!(abc_annotation_get_element(aa, 0, &mut elem), 0);
        assert_eq!(elem.tag, b'7');
        assert_eq!(elem.value, 111);
        abc_annotation_close(aa);
        abc_file_close(f);
    }
}

/// `abc_annotation_array_read`: an unterminated ULEB count fails with -1; a
/// payload ending mid-element returns the partial read count.
#[test]
fn annotation_array_read_truncation_guards() {
    unsafe {
        // Five continuation bytes where the ULEB count should be.
        let f = open(&minimal_file(&[0x80, 0x80, 0x80, 0x80, 0x80]));
        let mut buf = [0u64; 2];
        assert_eq!(
            abc_annotation_array_read(f, 64, 4, 2, buf.as_mut_ptr(), 2),
            -1
        );
        abc_file_close(f);

        // count = 2, element_size 4, but only one element's bytes remain.
        let g = open(&minimal_file(&[0x02, 0x2A, 0x00, 0x00, 0x00]));
        assert_eq!(
            abc_annotation_array_read(g, 64, 4, 2, buf.as_mut_ptr(), 2),
            1,
            "the partial read returns the completed element count"
        );
        assert_eq!(buf[0], 42);
        abc_file_close(g);
    }
}

/// `abc_method_handle_read`: an out-of-file offset throws into the catch
/// guard; a six-byte span with an unterminated ULEB entity offset fails
/// through the explicit !ok guard.
#[test]
fn method_handle_read_guards() {
    unsafe {
        // [type = 0x04][0x80 x5 unterminated ULEB]
        let data = minimal_file(&[0x04, 0x80, 0x80, 0x80, 0x80, 0x80]);
        let f = open(&data);
        let (mut ty, mut ent) = (0u8, 0u32);
        assert_eq!(abc_method_handle_read(f, 64, &mut ty, &mut ent), -1);
        assert_eq!(
            abc_method_handle_read(f, 0xFFFF_FF00, &mut ty, &mut ent),
            -1
        );
        abc_file_close(f);
        // Positive control: [type = 0x04][uleb 0x2A].
        let g = open(&minimal_file(&[0x04, 0x2A, 0, 0, 0, 0]));
        assert_eq!(abc_method_handle_read(g, 64, &mut ty, &mut ent), 0);
        assert_eq!((ty, ent), (4, 0x2A));
        abc_file_close(g);
    }
}

// ---------------------------------------------------------------------------
// Debug info / index / resolve / string / foreign / file-level guards
// ---------------------------------------------------------------------------

/// Debug-info table callbacks can stop the enumeration early by returning
/// non-zero: exactly one entry is delivered per table.
#[test]
fn debug_table_callbacks_stop_early() {
    with_rich(|data, _, method_off, _| unsafe {
        let f = open(data);
        let d = abc_debug_info_open(f);
        assert!(!d.is_null());

        unsafe extern "C" fn stop_after_one<T>(_e: *const T, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            1
        }
        let mut lines = 0usize;
        abc_debug_get_line_table(
            d,
            method_off,
            Some(stop_after_one::<AbcLineEntry>),
            &mut lines as *mut usize as *mut c_void,
        );
        assert_eq!(lines, 1, "line table stops after the first entry");
        let mut cols = 0usize;
        abc_debug_get_column_table(
            d,
            method_off,
            Some(stop_after_one::<AbcColumnEntry>),
            &mut cols as *mut usize as *mut c_void,
        );
        assert_eq!(cols, 1);
        let mut vars = 0usize;
        abc_debug_get_local_vars(
            d,
            method_off,
            Some(stop_after_one::<AbcLocalVarInfo>),
            &mut vars as *mut usize as *mut c_void,
        );
        assert_eq!(vars, 1);
        let mut params = 0usize;
        abc_debug_get_parameter_info(
            d,
            method_off,
            Some(stop_after_one::<AbcParamInfo>),
            &mut params as *mut usize as *mut c_void,
        );
        assert_eq!(params, 1);

        // Positive content contrast.
        let file = abc_debug_get_source_file(d, method_off);
        assert!(!file.is_null());
        assert_eq!(std::ffi::CStr::from_ptr(file).to_bytes(), b"m.js");
        abc_debug_info_close(d);
        abc_file_close(f);
    });
}

/// The index accessor's lazy function-kind read constructs a fresh method
/// accessor: a garbage method offset throws into the catch guard, while a
/// real method answers 0 (FunctionKind::NONE).
#[test]
fn index_function_kind_rejects_garbage_method() {
    with_rich(|data, _, method_off, _| unsafe {
        let f = open(data);
        let good = abc_index_open(f, method_off);
        assert!(!good.is_null(), "the index ctor is a plain struct");
        assert_eq!(abc_index_get_function_kind(good), 0);
        abc_index_close(good);
        let bad = abc_index_open(f, 0xFFFF_FF00);
        assert!(!bad.is_null());
        assert_eq!(abc_index_get_function_kind(bad), u8::MAX);
        abc_index_close(bad);
        abc_file_close(f);
    });
}

/// The `Resolve*Index` exports throw when the entity is not covered by any
/// index section (offset 4 lands inside the file header).
#[test]
fn resolve_index_exports_reject_non_index_entity() {
    let data = minimal_file(&[0u8; 8]);
    unsafe {
        let f = open(&data);
        assert_eq!(abc_resolve_class_index(f, 4, 0), u32::MAX);
        assert_eq!(abc_resolve_offset_by_index(f, 4, 0), u32::MAX);
        abc_file_close(f);
    }
}

/// `abc_file_get_class_id`: an absent class name returns UINT32_MAX (the
/// vendor's not-found EntityId), a present name resolves.
#[test]
fn get_class_id_absent_name_lookup() {
    let data = unsafe { build_rich() };
    unsafe {
        let f = open(&data);
        assert_eq!(abc_file_get_class_id(f, c"LAbsent;".as_ptr()), u32::MAX);
        let off = abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr());
        assert_ne!(off, u32::MAX);
        assert_eq!(off as usize, class_off_by_name(&data, "L_GLOBAL;"));
        abc_file_close(f);

        // A class whose inline name string is unreadable: the linear scan's
        // GetStringData throws into the catch guard. The first table entry
        // (descriptor-sorted) is mangled with an unterminated ULEB tag.
        let mut mangled = data.to_vec();
        let first_off = u32_at(&mangled, u32_at(&mangled, 32) as usize) as usize;
        mangled[first_off..first_off + 5].copy_from_slice(&[0x80; 5]);
        let g = open(&mangled);
        assert_eq!(abc_file_get_class_id(g, c"LWhatever;".as_ptr()), u32::MAX);
        abc_file_close(g);
    }
}

/// String getters: small destination buffers fail through the explicit
/// guards; a string item whose ULEB tag cannot be read throws into the
/// catch guard.
#[test]
fn string_getter_buffer_guards() {
    with_rich(|data, _, method_off, _| unsafe {
        // "mmethod" string item: [uleb (7 << 1) | 1]["mmethod"][NUL].
        let mut pat = vec![0x0Fu8];
        pat.extend_from_slice(b"mmethod");
        pat.push(0);
        let hits: Vec<usize> = data
            .windows(pat.len())
            .enumerate()
            .filter(|(_, w)| *w == pat.as_slice())
            .map(|(i, _)| i)
            .collect();
        assert_eq!(hits.len(), 1, "the method name string item is unique");
        let str_off = hits[0] as u32;

        let f = open(data);
        // Raw-byte view: query then a small fill clamps the copy.
        let len = abc_file_get_string(f, str_off, std::ptr::null_mut(), 0);
        assert_eq!(len, 7);
        let mut buf = [0u8; 4];
        let copied = abc_file_get_string(f, str_off, buf.as_mut_ptr().cast(), buf.len());
        assert_eq!(copied, 3, "copy clamps to buf_len - 1");
        assert_eq!(&buf, b"mme\0");
        // UTF-16 view: a too-small destination is rejected before writing.
        let units = abc_file_get_string_utf16(f, str_off, std::ptr::null_mut(), 0);
        assert_eq!(units, 7);
        let mut u16buf = [0u16; 3];
        assert_eq!(
            abc_file_get_string_utf16(f, str_off, u16buf.as_mut_ptr(), u16buf.len()),
            usize::MAX,
            "buf_len < utf16_length must fail"
        );
        assert_eq!(u16buf, [0u16; 3], "a rejected fill writes nothing");

        // Method-name UTF-16 view: same small-buffer guard.
        let ma = abc_method_open(f, method_off);
        assert!(!ma.is_null());
        assert_eq!(
            abc_method_get_name_utf16(ma, u16buf.as_mut_ptr(), u16buf.len()),
            0
        );
        abc_method_close(ma);
        abc_file_close(f);

        // Corrupt the name string's NUL terminator: the bounded conversion
        // fails both the file-level and the method-level reads.
        let mut corrupted = data.to_vec();
        corrupted[hits[0] + pat.len() - 1] = 0xE1;
        let g = open(&corrupted);
        assert_eq!(
            abc_file_get_string_utf16(g, str_off, std::ptr::null_mut(), 0),
            usize::MAX
        );
        let mb = abc_method_open(g, method_off);
        assert!(!mb.is_null());
        assert_eq!(
            abc_method_get_name_utf16(mb, std::ptr::null_mut(), 0),
            0,
            "an unterminated name item must fail the query"
        );
        // The fill path with an adequately sized buffer fails the same
        // bounded conversion (it may write partial units before the
        // exact-count check fails — only the error return is contractual).
        let mut wide = [0u16; 16];
        assert_eq!(
            abc_method_get_name_utf16(mb, wide.as_mut_ptr(), wide.len()),
            0,
            "an unterminated name item must fail the fill"
        );
        abc_method_close(mb);
        abc_file_close(g);

        // An item whose ULEB tag runs off the span throws into the guard.
        let mut tail = data.to_vec();
        let last = tail.len() - 1;
        tail[last] = 0x80;
        let h = open(&tail);
        assert_eq!(
            abc_file_get_string(
                h,
                (tail.len() - 1) as u32,
                buf.as_mut_ptr().cast(),
                buf.len()
            ),
            0
        );
        abc_file_close(h);
    });
}

/// A foreign item whose name field would cross the declared file size fails
/// the EOF guard (hostile header: foreign region ending two bytes before
/// EOF).
#[test]
fn foreign_item_name_off_eof_guard() {
    let mut data = minimal_file(&[0u8; 8]);
    let file_size = data.len() as u32;
    // foreign_off = file_size - 2, foreign_size = 4: the "item" at
    // file_size - 2 is inside the region, but item+4+4 > file_size.
    write_u32(&mut data, 20, file_size - 2);
    write_u32(&mut data, 24, 4);
    unsafe {
        let f = open(&data);
        assert_eq!(abc_foreign_item_name_off(f, file_size - 2), u32::MAX);
        // Outside the region entirely: the membership guard.
        assert_eq!(abc_foreign_item_name_off(f, 4), u32::MAX);
        abc_file_close(f);
    }
}

/// File-level index guards: class/literal-array indices past their tables
/// return UINT32_MAX.
#[test]
fn file_level_index_guards() {
    let data = unsafe { build_rich() };
    unsafe {
        let f = open(&data);
        assert_eq!(abc_file_class_offset(f, 9999), u32::MAX);
        assert_eq!(abc_file_literalarray_offset(f, 9999), u32::MAX);
        assert_ne!(abc_file_class_offset(f, 0), u32::MAX);
        abc_file_close(f);
    }
}

/// `abc_param_annotations_enumerate`: a span too short for the count field
/// fails with -1; a callback returning non-zero stops the enumeration early
/// with success.
#[test]
fn param_annotations_enumerate_guards() {
    unsafe {
        // Short span (2 bytes) at the tail of the file.
        let f = open(&minimal_file(&[0u8; 2]));
        let short = abc_file_size(f) - 2;
        unsafe extern "C" fn noop(_p: u32, _o: u32, _c: *mut c_void) -> i32 {
            0
        }
        assert_eq!(
            abc_param_annotations_enumerate(f, short, Some(noop), std::ptr::null_mut()),
            -1
        );
        abc_file_close(f);

        // Valid ParamAnnotationsItem, early-stopping callback.
        let b = abc_builder_new();
        abc_builder_set_api(b, 12, c"beta1".as_ptr());
        let cls = abc_builder_add_global_class(b);
        let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED, std::ptr::null(), 0);
        let code: [u8; 1] = [0x65];
        let m = abc_builder_class_add_method_with_proto(
            b,
            cls,
            c"f".as_ptr(),
            proto,
            1,
            code.as_ptr(),
            1,
            1,
            0,
        );
        assert_ne!(m, u32::MAX);
        assert_eq!(abc_builder_method_add_param(b, m, Type_TypeId_TAGGED), 0);
        let ann_cls = abc_builder_add_class(b, c"LAnn;".as_ptr());
        let name = abc_builder_add_string(b, c"value".as_ptr());
        let elems = [AbcAnnotationElemDef {
            name_string_handle: name,
            tag: b'6' as std::ffi::c_char,
            value: 7,
        }];
        let ann = abc_builder_create_annotation(b, ann_cls, elems.as_ptr(), 1);
        abc_builder_method_param_add_annotation(b, m, 0, ann);
        assert_eq!(abc_builder_method_seal_param_annotations(b, m, 0), 1);
        let mut out_len = 0u32;
        let ptr = abc_builder_finalize(b, &mut out_len);
        assert!(!ptr.is_null());
        let data = std::slice::from_raw_parts(ptr, out_len as usize).to_vec();
        abc_builder_free(b);

        let g = open(&data);
        let class_off = abc_file_get_class_id(g, c"L_GLOBAL;".as_ptr());
        let ca = abc_class_open(g, class_off);
        assert!(!ca.is_null());
        let mut methods: Vec<u32> = Vec::new();
        abc_class_enumerate_methods(
            ca,
            Some(collect_u32),
            &mut methods as *mut Vec<u32> as *mut c_void,
        );
        abc_class_close(ca);
        let ma = abc_method_open(g, methods[0]);
        let item_off = abc_method_get_param_annotation_id(ma);
        abc_method_close(ma);
        assert_ne!(item_off, u32::MAX);

        let mut calls = 0usize;
        unsafe extern "C" fn stop(_p: u32, _o: u32, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            1
        }
        assert_eq!(
            abc_param_annotations_enumerate(
                g,
                item_off,
                Some(stop),
                &mut calls as *mut usize as *mut c_void,
            ),
            0,
            "early stop is a successful termination"
        );
        assert_eq!(calls, 1, "exactly one entry is delivered");
        abc_file_close(g);
    }
}

// ---------------------------------------------------------------------------
// Tolerant literal-array enumerator truncation guards
// ---------------------------------------------------------------------------

/// Every truncation guard of the tolerant literal-array walk: the array
/// offset within four bytes of EOF, and each tag family whose payload ends
/// mid-item. Each craft must deliver zero values (never abort, never
/// over-read). The one-byte tags 0x00/0x01/0x08/0x19/0xFF use the read_u8
/// guard; the multi-byte tags use their width guards.
#[test]
fn literal_enumerate_truncation_guards() {
    // (payload after the u32 count, count) — the span always ends exactly
    // after the payload.
    let crafts: &[(&[u8], u32)] = &[
        (&[], 1),                          // count present, no tag byte at all
        (&[0x00], 1),                      // INTEGER_8 tag, no payload byte
        (&[0x01], 1),                      // BOOL tag, no payload byte
        (&[0x02, 0x01, 0x02], 1),          // INTEGER tag, 3 of 4 payload bytes
        (&[0x03, 0x01, 0x02], 1),          // FLOAT tag, short payload
        (&[0x04, 1, 2, 3, 4, 5, 6, 7], 1), // DOUBLE tag, 7 of 8 bytes
        (&[0x05, 0x01, 0x02], 1),          // STRING-family tag, short payload
        (&[0x08], 1),                      // ACCESSOR tag, no payload byte
        (&[0x09, 0x01], 1),                // METHODAFFILIATE tag, 1 of 2 bytes
    ];
    unsafe extern "C" fn count_val(_v: *const AbcLiteralVal, ctx: *mut c_void) {
        unsafe { *(ctx as *mut usize) += 1 };
    }
    for (payload, count) in crafts {
        let mut body = Vec::new();
        body.extend_from_slice(&count.to_le_bytes());
        body.extend_from_slice(payload);
        let data = minimal_file(&body);
        unsafe {
            let f = open(&data);
            let la = abc_literal_open(f, 64);
            assert!(!la.is_null(), "literal accessor opens on any live span");
            let mut seen = 0usize;
            abc_literal_enumerate_vals(
                la,
                64,
                Some(count_val),
                &mut seen as *mut usize as *mut c_void,
            );
            assert_eq!(
                seen, 0,
                "truncated payload {payload:?} must deliver nothing"
            );
            abc_literal_close(la);
            abc_file_close(f);
        }
    }
    // The array offset itself within four bytes of EOF: span < count width.
    let data = minimal_file(&[0u8; 2]);
    unsafe {
        let f = open(&data);
        let la = abc_literal_open(f, 64);
        assert!(!la.is_null());
        let mut seen = 0usize;
        let short = abc_file_size(f) - 2;
        abc_literal_enumerate_vals(
            la,
            short,
            Some(count_val),
            &mut seen as *mut usize as *mut c_void,
        );
        assert_eq!(seen, 0);
        abc_literal_close(la);
        abc_file_close(f);
    }
    // Positive control: [count = 2][INTEGER 42] delivers one value.
    let mut body = Vec::new();
    body.extend_from_slice(&2u32.to_le_bytes());
    body.push(0x02);
    body.extend_from_slice(&42u32.to_le_bytes());
    let data = minimal_file(&body);
    unsafe {
        let f = open(&data);
        let la = abc_literal_open(f, 64);
        assert!(!la.is_null());
        let mut seen: Vec<(u8, u32)> = Vec::new();
        unsafe extern "C" fn collect_val(v: *const AbcLiteralVal, ctx: *mut c_void) {
            unsafe {
                let val = &*v;
                (*(ctx as *mut Vec<(u8, u32)>)).push((val.tag, val.data.u32_val));
            }
        }
        abc_literal_enumerate_vals(
            la,
            64,
            Some(collect_val),
            &mut seen as *mut Vec<(u8, u32)> as *mut c_void,
        );
        assert_eq!(seen, vec![(0x02, 42)]);
        abc_literal_close(la);
        abc_file_close(f);
    }
}

// ---------------------------------------------------------------------------
// Builder guard negatives
//
// Every builder export validates its handles before touching the vendor
// item tables (`if (handle >= b->Xs.size()) return ...;`). The tests below
// drive each guard with an out-of-range handle and then pin the
// corresponding positive path, so a rejected call is observed as "the valid
// entity kept its prior state" and a dropped guard would crash the test
// process outright.
// ---------------------------------------------------------------------------

/// A builder with the handles the guard tests need, freed on drop.
struct GuardBuilder {
    b: *mut AbcBuilder,
    cls: u32,
    proto: u32,
    method: u32,
    field: u32,
    ann: u32,
    lit: u32,
    code: u32,
    lnp: u32,
    debug: u32,
    string: u32,
    foreign_cls: u32,
    foreign_field: u32,
    foreign_method: u32,
}

impl GuardBuilder {
    fn new() -> Self {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());
            abc_builder_set_api(b, 12, c"beta1".as_ptr());
            let cls = abc_builder_add_global_class(b);
            assert_ne!(cls, u32::MAX);
            let proto = abc_builder_create_proto(b, Type_TypeId_TAGGED, std::ptr::null(), 0);
            assert_ne!(proto, u32::MAX);
            let code_bytes: [u8; 1] = [0x65];
            let method = abc_builder_class_add_method_with_proto(
                b,
                cls,
                c"f".as_ptr(),
                proto,
                1,
                code_bytes.as_ptr(),
                1,
                1,
                0,
            );
            assert_ne!(method, u32::MAX);
            let field = abc_builder_class_add_field(b, cls, c"fx".as_ptr(), Type_TypeId_I32, 1);
            assert_ne!(field, u32::MAX);
            let ann_cls = abc_builder_add_class(b, c"LAnn;".as_ptr());
            let name = abc_builder_add_string(b, c"value".as_ptr());
            let elems = [AbcAnnotationElemDef {
                name_string_handle: name,
                tag: b'6' as std::ffi::c_char,
                value: 7,
            }];
            let ann = abc_builder_create_annotation(b, ann_cls, elems.as_ptr(), 1);
            assert_ne!(ann, u32::MAX);
            let lit = abc_builder_add_literal_array(b, c"s".as_ptr());
            assert_ne!(lit, u32::MAX);
            let code = abc_builder_create_code(b, 1, 0, code_bytes.as_ptr(), 1);
            assert_ne!(code, u32::MAX);
            let lnp = abc_builder_create_lnp(b);
            assert_ne!(lnp, u32::MAX);
            let debug = abc_builder_create_debug_info(b, lnp, 1);
            assert_ne!(debug, u32::MAX);
            let string = abc_builder_add_string(b, c"f.js".as_ptr());
            assert_ne!(string, u32::MAX);
            let foreign_cls = abc_builder_add_foreign_class(b, c"LForeign;".as_ptr());
            assert_ne!(foreign_cls, u32::MAX);
            let foreign_field =
                abc_builder_add_foreign_field(b, foreign_cls, c"ff".as_ptr(), Type_TypeId_I32);
            assert_ne!(foreign_field, u32::MAX);
            let foreign_method =
                abc_builder_add_foreign_method(b, foreign_cls, c"fm".as_ptr(), proto, 1);
            assert_ne!(foreign_method, u32::MAX);
            Self {
                b,
                cls,
                proto,
                method,
                field,
                ann,
                lit,
                code,
                lnp,
                debug,
                string,
                foreign_cls,
                foreign_field,
                foreign_method,
            }
        }
    }

    /// Finalize and open the produced file.
    unsafe fn finalize_open(&self) -> (*mut AbcFileHandle, Vec<u8>) {
        unsafe {
            let mut out_len = 0u32;
            let ptr = abc_builder_finalize(self.b, &mut out_len);
            assert!(!ptr.is_null(), "fixture must finalize");
            let data = std::slice::from_raw_parts(ptr, out_len as usize).to_vec();
            (open(&data), data)
        }
    }
}

impl Drop for GuardBuilder {
    fn drop(&mut self) {
        unsafe { abc_builder_free(self.b) };
    }
}

/// First method/field item offsets of the fixture's global class, looked up
/// through the bridge after finalize.
unsafe fn fixture_members(f: *const AbcFileHandle) -> (u32, u32) {
    unsafe {
        let class_off = abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr());
        assert_ne!(class_off, u32::MAX);
        let (methods, fields) = class_members(f, class_off);
        assert_eq!(methods.len(), 1);
        assert_eq!(fields.len(), 1);
        (methods[0], fields[0])
    }
}

/// Class-configuration handle guards: super class, interface, source file,
/// and the field/method adders.
#[test]
fn builder_class_config_guards() {
    let g = GuardBuilder::new();
    unsafe {
        // Out-of-range class handles and unresolvable targets are rejected.
        abc_builder_class_set_super_class(g.b, u32::MAX, g.cls);
        abc_builder_class_set_super_class(g.b, g.cls, 0x7777);
        abc_builder_class_add_interface(g.b, u32::MAX, g.cls);
        abc_builder_class_add_interface(g.b, g.cls, 0x7777);
        abc_builder_class_set_source_file(g.b, u32::MAX, g.string);
        abc_builder_class_set_source_file(g.b, g.cls, u32::MAX);
        assert_eq!(
            abc_builder_class_add_field(g.b, u32::MAX, c"g".as_ptr(), Type_TypeId_I32, 1),
            u32::MAX
        );
        assert_eq!(
            abc_builder_class_add_field_ex(g.b, u32::MAX, c"g".as_ptr(), Type_TypeId_I32, 0, 1),
            u32::MAX
        );
        // REFERENCE type with an unresolvable class handle has no type item.
        assert_eq!(
            abc_builder_class_add_field_ex(
                g.b,
                g.cls,
                c"g".as_ptr(),
                Type_TypeId_REFERENCE,
                0x7777,
                1,
            ),
            u32::MAX
        );
        assert_eq!(
            abc_builder_class_add_method_with_proto(
                g.b,
                u32::MAX,
                c"g".as_ptr(),
                g.proto,
                1,
                std::ptr::null(),
                0,
                0,
                0,
            ),
            u32::MAX
        );
        assert_eq!(
            abc_builder_class_add_method_with_proto(
                g.b,
                g.cls,
                c"g".as_ptr(),
                u32::MAX,
                1,
                std::ptr::null(),
                0,
                0,
                0,
            ),
            u32::MAX
        );
        // The class never picked up the rejected configuration.
        let (f, _) = g.finalize_open();
        let class_off = abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr());
        let ca = abc_class_open(f, class_off);
        assert!(!ca.is_null());
        assert_eq!(abc_class_super_class_off(ca), 0, "no super class staged");
        assert_eq!(abc_class_get_ifaces_number(ca), 0, "no interface staged");
        assert_eq!(abc_class_source_file_off(ca), u32::MAX, "no source file");
        abc_class_close(ca);
        abc_file_close(f);
    }
}

/// Positive contrast for the class-configuration wrappers (same calls with
/// valid handles land in the produced file).
#[test]
fn builder_class_config_positive_contrast() {
    let g = GuardBuilder::new();
    unsafe {
        abc_builder_class_set_super_class(g.b, g.cls, g.foreign_cls);
        abc_builder_class_add_interface(g.b, g.cls, g.foreign_cls);
        abc_builder_class_set_source_file(g.b, g.cls, g.string);
        let (f, _) = g.finalize_open();
        let class_off = abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr());
        let ca = abc_class_open(f, class_off);
        assert!(!ca.is_null());
        assert_ne!(abc_class_super_class_off(ca), 0);
        assert_eq!(abc_class_get_ifaces_number(ca), 1);
        assert_ne!(abc_class_source_file_off(ca), u32::MAX);
        abc_class_close(ca);
        abc_file_close(f);
    }
}

/// Method/field configuration handle guards: debug info, initial values,
/// method code, and try blocks.
#[test]
fn builder_method_field_config_guards() {
    let g = GuardBuilder::new();
    unsafe {
        abc_builder_method_set_debug_info(g.b, u32::MAX, g.debug);
        abc_builder_method_set_debug_info(g.b, g.method, u32::MAX);
        // The good attach lands; the bad ones did nothing.
        abc_builder_lnp_emit_set_file(g.b, g.lnp, g.debug, g.string);
        abc_builder_lnp_emit_end(g.b, g.lnp);
        abc_builder_method_set_debug_info(g.b, g.method, g.debug);

        abc_builder_field_set_value_i32(g.b, u32::MAX, 1);
        abc_builder_field_set_value_i64(g.b, u32::MAX, 1);
        abc_builder_field_set_value_f32(g.b, u32::MAX, 1.0);
        abc_builder_field_set_value_f64(g.b, u32::MAX, 1.0);
        abc_builder_field_set_value_i32(g.b, g.field, 42);

        // Try block on an unknown code item is dropped.
        let catches = [AbcCatchBlockDef {
            type_class_handle: u32::MAX,
            handler_pc: 0,
            code_size: 1,
        }];
        abc_builder_code_add_try_block(g.b, u32::MAX, 0, 1, catches.as_ptr(), 1);
        // set_code with unknown handles is dropped.
        abc_builder_method_set_code(g.b, u32::MAX, g.code);
        abc_builder_method_set_code(g.b, g.method, u32::MAX);

        let (f, _) = g.finalize_open();
        let (method_off, field_off) = fixture_members(f);
        let ma = abc_method_open(f, method_off);
        assert!(!ma.is_null());
        assert_ne!(abc_method_debug_info_off(ma), u32::MAX);
        // The inline code from method creation survived the rejected
        // set_code calls.
        let code_off = abc_method_code_off(ma);
        assert_ne!(code_off, u32::MAX);
        abc_method_close(ma);
        let code_a = abc_code_open(f, code_off);
        assert!(!code_a.is_null());
        assert_eq!(abc_code_code_size(code_a), 1);
        // No try block was staged onto the standalone code item.
        let mut tries = 0usize;
        unsafe extern "C" fn count_try(
            _t: *const AbcTryBlockInfo,
            _c: *const AbcCatchBlockInfo,
            ctx: *mut c_void,
        ) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        abc_code_enumerate_try_blocks_full(
            code_a,
            Some(count_try),
            &mut tries as *mut usize as *mut c_void,
        );
        assert_eq!(tries, 0);
        abc_code_close(code_a);
        let fa = abc_field_open(f, field_off);
        assert!(!fa.is_null());
        let mut v = 0i32;
        assert_eq!(abc_field_get_value_i32(fa, &mut v), 1);
        assert_eq!(v, 42);
        abc_field_close(fa);
        abc_file_close(f);
    }
}

/// The direct (post-set_code) try-block path with an unresolvable catch
/// type: `ResolveClassHandle` returns null and the catch block is built
/// with a null type (decodes as catch-all), never rejected, never crashing.
#[test]
fn builder_try_block_direct_path_unresolvable_catch_type() {
    let g = GuardBuilder::new();
    unsafe {
        abc_builder_method_set_code(g.b, g.method, g.code);
        let catches = [
            AbcCatchBlockDef {
                type_class_handle: 0x7777, // resolves to nothing
                handler_pc: 0,
                code_size: 1,
            },
            AbcCatchBlockDef {
                type_class_handle: g.foreign_cls,
                handler_pc: 0,
                code_size: 1,
            },
        ];
        abc_builder_code_add_try_block(g.b, g.code, 0, 1, catches.as_ptr(), 2);
        let (f, _) = g.finalize_open();
        let (method_off, _) = fixture_members(f);
        let ma = abc_method_open(f, method_off);
        let code_off = abc_method_code_off(ma);
        abc_method_close(ma);
        assert_ne!(code_off, u32::MAX);
        let code_a = abc_code_open(f, code_off);
        assert!(!code_a.is_null());
        let mut seen: Vec<u32> = Vec::new();
        unsafe extern "C" fn collect_try(
            t: *const AbcTryBlockInfo,
            c: *const AbcCatchBlockInfo,
            ctx: *mut c_void,
        ) -> i32 {
            unsafe {
                let info = &*t;
                let blocks = std::slice::from_raw_parts(c, info.num_catches as usize);
                let out = &mut *(ctx as *mut Vec<u32>);
                for blk in blocks {
                    out.push(blk.type_idx);
                }
            }
            0
        }
        abc_code_enumerate_try_blocks_full(
            code_a,
            Some(collect_try),
            &mut seen as *mut Vec<u32> as *mut c_void,
        );
        abc_code_close(code_a);
        assert_eq!(seen.len(), 2, "both catches were built directly");
        assert_eq!(seen[0], u32::MAX, "unresolvable type decodes catch-all");
        assert_ne!(seen[1], u32::MAX, "the foreign type got an index");
        abc_file_close(f);
    }
}

/// Annotation attach handle guards (12 exports): unknown targets and unknown
/// annotation handles are rejected; the one valid attach lands.
#[test]
fn builder_annotation_attach_guards() {
    let g = GuardBuilder::new();
    unsafe {
        // Class attach exports.
        abc_builder_class_add_annotation(g.b, u32::MAX, g.ann);
        abc_builder_class_add_annotation(g.b, g.cls, u32::MAX);
        abc_builder_class_add_runtime_annotation(g.b, u32::MAX, g.ann);
        abc_builder_class_add_runtime_annotation(g.b, g.cls, u32::MAX);
        abc_builder_class_add_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_class_add_type_annotation(g.b, g.cls, u32::MAX);
        abc_builder_class_add_runtime_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_class_add_runtime_type_annotation(g.b, g.cls, u32::MAX);
        // Method attach exports.
        abc_builder_method_add_annotation(g.b, u32::MAX, g.ann);
        abc_builder_method_add_annotation(g.b, g.method, u32::MAX);
        abc_builder_method_add_runtime_annotation(g.b, u32::MAX, g.ann);
        abc_builder_method_add_runtime_annotation(g.b, g.method, u32::MAX);
        abc_builder_method_add_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_method_add_type_annotation(g.b, g.method, u32::MAX);
        abc_builder_method_add_runtime_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_method_add_runtime_type_annotation(g.b, g.method, u32::MAX);
        // Field attach exports.
        abc_builder_field_add_annotation(g.b, u32::MAX, g.ann);
        abc_builder_field_add_annotation(g.b, g.field, u32::MAX);
        abc_builder_field_add_runtime_annotation(g.b, u32::MAX, g.ann);
        abc_builder_field_add_runtime_annotation(g.b, g.field, u32::MAX);
        abc_builder_field_add_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_field_add_type_annotation(g.b, g.field, u32::MAX);
        abc_builder_field_add_runtime_type_annotation(g.b, u32::MAX, g.ann);
        abc_builder_field_add_runtime_type_annotation(g.b, g.field, u32::MAX);
        // One valid attach per target.
        abc_builder_class_add_annotation(g.b, g.cls, g.ann);
        abc_builder_method_add_annotation(g.b, g.method, g.ann);
        abc_builder_field_add_annotation(g.b, g.field, g.ann);

        let (f, _) = g.finalize_open();
        let class_off = abc_file_get_class_id(f, c"L_GLOBAL;".as_ptr());
        let (method_off, field_off) = fixture_members(f);
        unsafe extern "C" fn count_ann(_o: u32, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        let count_class_anns = |a: *mut AbcClassAccessor, kind: u8| {
            let mut n = 0usize;
            let ctx = &mut n as *mut usize as *mut c_void;
            match kind {
                0 => abc_class_enumerate_annotations(a, Some(count_ann), ctx),
                _ => abc_class_enumerate_runtime_annotations(a, Some(count_ann), ctx),
            }
            n
        };
        let ca = abc_class_open(f, class_off);
        assert_eq!(count_class_anns(ca, 0), 1, "exactly the valid class attach");
        assert_eq!(
            count_class_anns(ca, 1),
            0,
            "rejected runtime attaches staged nothing"
        );
        abc_class_close(ca);
        let mut n = 0usize;
        let ctx = &mut n as *mut usize as *mut c_void;
        let ma = abc_method_open(f, method_off);
        abc_method_enumerate_annotations(ma, Some(count_ann), ctx);
        abc_method_close(ma);
        assert_eq!(n, 1);
        n = 0;
        let fa = abc_field_open(f, field_off);
        abc_field_enumerate_annotations(fa, Some(count_ann), ctx);
        abc_field_close(fa);
        assert_eq!(n, 1);
        abc_file_close(f);
    }
}

/// Parameter-annotation handle guards: unknown method/parameter handles are
/// rejected; the valid staging seals and enumerates.
#[test]
fn builder_param_annotation_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(
            abc_builder_method_add_param(g.b, u32::MAX, Type_TypeId_TAGGED),
            u32::MAX
        );
        assert_eq!(
            abc_builder_method_add_param(g.b, g.method, Type_TypeId_TAGGED),
            0
        );
        // Unknown method, unknown param index (only param 0 exists).
        abc_builder_method_param_add_annotation(g.b, u32::MAX, 0, g.ann);
        abc_builder_method_param_add_annotation(g.b, g.method, 9, g.ann);
        abc_builder_method_param_add_runtime_annotation(g.b, u32::MAX, 0, g.ann);
        abc_builder_method_param_add_runtime_annotation(g.b, g.method, 9, g.ann);
        abc_builder_method_param_add_type_annotation(g.b, u32::MAX, 0, g.ann);
        abc_builder_method_param_add_type_annotation(g.b, g.method, 9, g.ann);
        abc_builder_method_param_add_runtime_type_annotation(g.b, u32::MAX, 0, g.ann);
        abc_builder_method_param_add_runtime_type_annotation(g.b, g.method, 9, g.ann);
        // The valid staging seals into the compile-time item.
        abc_builder_method_param_add_annotation(g.b, g.method, 0, g.ann);
        assert_eq!(
            abc_builder_method_seal_param_annotations(g.b, g.method, 0),
            1
        );

        let (f, _) = g.finalize_open();
        let (method_off, _) = fixture_members(f);
        let ma = abc_method_open(f, method_off);
        let item = abc_method_get_param_annotation_id(ma);
        abc_method_close(ma);
        assert_ne!(item, u32::MAX);
        let mut entries: Vec<(u32, u32)> = Vec::new();
        unsafe extern "C" fn collect_entry(p: u32, o: u32, ctx: *mut c_void) -> i32 {
            unsafe { (*(ctx as *mut Vec<(u32, u32)>)).push((p, o)) };
            0
        }
        assert_eq!(
            abc_param_annotations_enumerate(
                f,
                item,
                Some(collect_entry),
                &mut entries as *mut Vec<(u32, u32)> as *mut c_void,
            ),
            0
        );
        assert_eq!(entries.len(), 1, "only the valid staging was sealed");
        assert_eq!(entries[0].0, 0);
        abc_file_close(f);
    }
}

/// Literal-array staging handle guards: unknown arrays/entities are
/// rejected; the valid items enumerate.
#[test]
fn builder_literal_staging_guards() {
    let g = GuardBuilder::new();
    unsafe {
        abc_builder_literal_array_add_u8(g.b, u32::MAX, 1);
        abc_builder_literal_array_add_u16(g.b, u32::MAX, 1);
        abc_builder_literal_array_add_u32(g.b, u32::MAX, 1);
        abc_builder_literal_array_add_u64(g.b, u32::MAX, 1);
        abc_builder_literal_array_add_bool(g.b, u32::MAX, 1);
        abc_builder_literal_array_add_string(g.b, u32::MAX, g.string);
        abc_builder_literal_array_add_string(g.b, g.lit, u32::MAX);
        abc_builder_literal_array_add_method(g.b, u32::MAX, g.method);
        abc_builder_literal_array_add_method(g.b, g.lit, u32::MAX);
        abc_builder_literal_array_add_literalarray(g.b, u32::MAX, g.lit);
        abc_builder_literal_array_add_literalarray(g.b, g.lit, u32::MAX);
        // Valid staging: three well-formed [tag][value] literals. The raw
        // exports are item-level primitives (the safe conveniences pair a
        // tag item with a value item per literal, encode.rs
        // literal_array_add_bool); both bool value arms (0 and non-0).
        abc_builder_literal_array_add_u8(g.b, g.lit, 0x01); // BOOL tag
        abc_builder_literal_array_add_bool(g.b, g.lit, 0);
        abc_builder_literal_array_add_u8(g.b, g.lit, 0x01); // BOOL tag
        abc_builder_literal_array_add_bool(g.b, g.lit, 7);
        abc_builder_literal_array_add_u8(g.b, g.lit, 0x05); // STRING tag
        abc_builder_literal_array_add_string(g.b, g.lit, g.string);

        let (f, data) = g.finalize_open();
        let lit_idx_off = u32_at(&data, 48) as usize;
        let array_off = u32_at(&data, lit_idx_off);
        let la = abc_literal_open(f, array_off);
        assert!(!la.is_null());
        let mut seen = 0usize;
        unsafe extern "C" fn count_val(_v: *const AbcLiteralVal, ctx: *mut c_void) {
            unsafe { *(ctx as *mut usize) += 1 };
        }
        abc_literal_enumerate_vals(
            la,
            array_off,
            Some(count_val),
            &mut seen as *mut usize as *mut c_void,
        );
        assert_eq!(seen, 3, "exactly the valid items were staged");
        abc_literal_close(la);
        abc_file_close(f);
    }
}

/// Module-data staging guards: null arrays with nonzero counts and missing
/// required names per record tag fail with -1.
#[test]
fn builder_module_data_guards() {
    let g = GuardBuilder::new();
    unsafe {
        let s = abc_builder_add_string(g.b, c"dep".as_ptr());
        // Null request/record arrays with nonzero counts.
        assert_eq!(
            abc_builder_literal_array_add_module_data(
                g.b,
                g.lit,
                std::ptr::null(),
                1,
                std::ptr::null(),
                0,
            ),
            -1
        );
        assert_eq!(
            abc_builder_literal_array_add_module_data(
                g.b,
                g.lit,
                std::ptr::null(),
                0,
                std::ptr::null(),
                1,
            ),
            -1
        );
        let ok = AbcModuleRecordDef {
            tag: ModuleTag_STAR_EXPORT,
            export_name_handle: u32::MAX,
            module_request_idx: 0,
            import_name_handle: u32::MAX,
            local_name_handle: u32::MAX,
        };
        // Regular import without the import name.
        let rec = AbcModuleRecordDef {
            tag: ModuleTag_REGULAR_IMPORT,
            local_name_handle: s,
            ..ok
        };
        assert_eq!(
            abc_builder_literal_array_add_module_data(
                g.b,
                g.lit,
                [s].as_ptr(),
                1,
                [rec].as_ptr(),
                1,
            ),
            -1
        );
        // Local export without local / export names.
        for rec in [
            AbcModuleRecordDef {
                tag: ModuleTag_LOCAL_EXPORT,
                export_name_handle: s,
                ..ok
            },
            AbcModuleRecordDef {
                tag: ModuleTag_LOCAL_EXPORT,
                local_name_handle: s,
                ..ok
            },
        ] {
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    g.b,
                    g.lit,
                    [s].as_ptr(),
                    1,
                    [rec].as_ptr(),
                    1,
                ),
                -1
            );
        }
        // Indirect export without export / import names.
        for rec in [
            AbcModuleRecordDef {
                tag: ModuleTag_INDIRECT_EXPORT,
                import_name_handle: s,
                ..ok
            },
            AbcModuleRecordDef {
                tag: ModuleTag_INDIRECT_EXPORT,
                export_name_handle: s,
                ..ok
            },
        ] {
            assert_eq!(
                abc_builder_literal_array_add_module_data(
                    g.b,
                    g.lit,
                    [s].as_ptr(),
                    1,
                    [rec].as_ptr(),
                    1,
                ),
                -1
            );
        }
        // Module-request-phase: null flags with a nonzero count.
        assert_eq!(
            abc_builder_literal_array_add_module_request_phase(g.b, g.lit, std::ptr::null(), 1,),
            -1
        );
        // Positive contrast: the valid module data stages and finalizes.
        assert_eq!(
            abc_builder_literal_array_add_module_data(
                g.b,
                g.lit,
                [s].as_ptr(),
                1,
                [ok].as_ptr(),
                1,
            ),
            0
        );
        assert_eq!(
            abc_builder_literal_array_add_module_request_phase(g.b, g.lit, [1u8].as_ptr(), 1),
            0
        );
        let (f, _) = g.finalize_open();
        abc_file_close(f);
    }
}

/// LNP/debug handle guards: unknown lnp/debug/string handles are rejected at
/// stage time; the valid ops land in the debug tables.
#[test]
fn builder_lnp_debug_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(abc_builder_create_debug_info(g.b, u32::MAX, 1), u32::MAX);
        abc_builder_debug_add_param(g.b, u32::MAX, g.string);
        abc_builder_debug_add_param(g.b, g.debug, u32::MAX);
        abc_builder_lnp_emit_end(g.b, u32::MAX);
        abc_builder_lnp_emit_advance_pc(g.b, u32::MAX, g.debug, 0);
        abc_builder_lnp_emit_advance_pc(g.b, g.lnp, u32::MAX, 0);
        abc_builder_lnp_emit_advance_line(g.b, u32::MAX, g.debug, 1);
        abc_builder_lnp_emit_advance_line(g.b, g.lnp, u32::MAX, 1);
        abc_builder_lnp_emit_column(g.b, u32::MAX, g.debug, 0, 1);
        abc_builder_lnp_emit_column(g.b, g.lnp, u32::MAX, 0, 1);
        abc_builder_lnp_emit_start_local(g.b, u32::MAX, g.debug, 0, g.string, g.string);
        abc_builder_lnp_emit_start_local(g.b, g.lnp, u32::MAX, 0, g.string, g.string);
        abc_builder_lnp_emit_start_local_extended(
            g.b,
            u32::MAX,
            g.debug,
            0,
            g.string,
            g.string,
            g.string,
        );
        abc_builder_lnp_emit_start_local_extended(
            g.b,
            g.lnp,
            u32::MAX,
            0,
            g.string,
            g.string,
            g.string,
        );
        abc_builder_lnp_emit_end_local(g.b, u32::MAX, 0);
        abc_builder_lnp_emit_set_file(g.b, u32::MAX, g.debug, g.string);
        abc_builder_lnp_emit_set_file(g.b, g.lnp, u32::MAX, g.string);
        abc_builder_lnp_emit_set_file(g.b, g.lnp, g.debug, u32::MAX);
        abc_builder_lnp_emit_set_source_code(g.b, u32::MAX, g.debug, g.string);
        abc_builder_lnp_emit_set_source_code(g.b, g.lnp, u32::MAX, g.string);
        abc_builder_lnp_emit_set_source_code(g.b, g.lnp, g.debug, u32::MAX);
        // (The start_local(_extended) STRING handles are deliberately NOT
        // exercised with out-of-range values: staging accepts them, but the
        // flush would pass nullptr to the vendored EmitStartLocal, which
        // dereferences it — those flush ternary arms are accepted residual.)
        // Valid ops.
        abc_builder_lnp_emit_set_file(g.b, g.lnp, g.debug, g.string);
        abc_builder_lnp_emit_advance_pc(g.b, g.lnp, g.debug, 0);
        abc_builder_lnp_emit_advance_line(g.b, g.lnp, g.debug, 3);
        abc_builder_lnp_emit_end(g.b, g.lnp);
        abc_builder_debug_add_param(g.b, g.debug, g.string);
        abc_builder_method_set_debug_info(g.b, g.method, g.debug);

        let (f, _) = g.finalize_open();
        let (method_off, _) = fixture_members(f);
        let d = abc_debug_info_open(f);
        assert!(!d.is_null());
        let file = abc_debug_get_source_file(d, method_off);
        assert!(!file.is_null());
        assert_eq!(std::ffi::CStr::from_ptr(file).to_bytes(), b"f.js");
        let mut lines = 0usize;
        unsafe extern "C" fn count_entry<T>(_e: *const T, ctx: *mut c_void) -> i32 {
            unsafe { *(ctx as *mut usize) += 1 };
            0
        }
        abc_debug_get_line_table(
            d,
            method_off,
            Some(count_entry::<AbcLineEntry>),
            &mut lines as *mut usize as *mut c_void,
        );
        assert_eq!(lines, 1, "exactly the valid advance-line op landed");
        let mut params = 0usize;
        abc_debug_get_parameter_info(
            d,
            method_off,
            Some(count_entry::<AbcParamInfo>),
            &mut params as *mut usize as *mut c_void,
        );
        assert_eq!(params, 1);
        abc_debug_info_close(d);
        abc_file_close(f);
    }
}

/// `create_annotation_ex` edge arms: the R/S/U 64-bit array component types
/// and the `resolve_entity_by_tag` unresolved-handle breaks with their
/// raw-scalar fallbacks.
#[test]
fn builder_annotation_ex_edge_arms() {
    let g = GuardBuilder::new();
    unsafe {
        // 64-bit scalar array component types (tags R/S/U): each builds an
        // ArrayValueItem of the matching 8-byte component type.
        let name = abc_builder_add_string(g.b, c"v".as_ptr());
        let values = [0x0102_0304u32, 0x0506_0708];
        for tag in *b"RSU" {
            let elem = AbcAnnotationElemDefEx {
                name_string_handle: name,
                tag: tag as std::ffi::c_char,
                is_array: 1,
                scalar_value: 0,
                scalar_value_64: 0,
                array_values: values.as_ptr(),
                array_count: 2,
            };
            assert_ne!(
                abc_builder_create_annotation_ex(g.b, g.cls, &elem, 1),
                u32::MAX,
                "tag {} array must build",
                tag as char
            );
        }
        // Unresolvable entity handles per tag family: scalar entity refs
        // fall back to raw scalars; entity arrays fall back per element.
        let mut elems: Vec<AbcAnnotationElemDefEx> = Vec::new();
        for tag in *b"CDEFGJ#" {
            elems.push(AbcAnnotationElemDefEx {
                name_string_handle: name,
                tag: tag as std::ffi::c_char,
                is_array: 3,
                scalar_value: 0x7777,
                scalar_value_64: 0,
                array_values: std::ptr::null(),
                array_count: 0,
            });
        }
        // A scalar tag outside the entity switch ('7' = plain U32) takes
        // the default arm and falls back to a raw scalar as well.
        elems.push(AbcAnnotationElemDefEx {
            name_string_handle: name,
            tag: b'7' as std::ffi::c_char,
            is_array: 3,
            scalar_value: 0x7777,
            scalar_value_64: 0,
            array_values: std::ptr::null(),
            array_count: 0,
        });
        for tag in *b"VWXYZ@" {
            elems.push(AbcAnnotationElemDefEx {
                name_string_handle: name,
                tag: tag as std::ffi::c_char,
                is_array: 4,
                scalar_value: 0,
                scalar_value_64: 0,
                array_values: [0x7777u32].as_ptr(),
                array_count: 1,
            });
        }
        assert_ne!(
            abc_builder_create_annotation_ex(g.b, g.cls, elems.as_ptr(), elems.len() as u32),
            u32::MAX,
            "unresolvable handles fall back, never reject"
        );
        // Unknown class handle is still rejected.
        assert_eq!(
            abc_builder_create_annotation_ex(g.b, u32::MAX, &elems[0], 1),
            u32::MAX
        );
        assert_eq!(
            abc_builder_create_annotation(g.b, u32::MAX, std::ptr::null(), 0),
            u32::MAX
        );
        // The R/S/U arrays make the file structurally inconsistent (the
        // vendored ArrayValueItem sizes 8-byte components but the 32-bit
        // builder ABI writes 4-byte items, so the item stream desyncs):
        // finalize must still produce bytes — the coverage is in the build
        // calls themselves — but the result is deliberately never decoded
        // here (the model path reports UnsupportedAnnotationArrayType
        // instead, phase05_fixes.rs).
        let mut out_len = 0u32;
        let ptr = abc_builder_finalize(g.b, &mut out_len);
        assert!(!ptr.is_null(), "the R/S/U build must still finalize");
    }
}

/// Foreign item and method-handle guards: unknown class/proto handles are
/// rejected; the foreign entity arms of `create_method_handle` resolve;
/// unresolvable entities return UINT32_MAX.
#[test]
fn builder_foreign_and_method_handle_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(
            abc_builder_add_foreign_field(g.b, u32::MAX, c"g".as_ptr(), Type_TypeId_I32),
            u32::MAX
        );
        assert_eq!(
            abc_builder_add_foreign_field(g.b, 0x7777, c"g".as_ptr(), Type_TypeId_I32),
            u32::MAX
        );
        assert_eq!(
            abc_builder_add_foreign_method(g.b, u32::MAX, c"g".as_ptr(), g.proto, 1),
            u32::MAX
        );
        assert_eq!(
            abc_builder_add_foreign_method(g.b, g.foreign_cls, c"g".as_ptr(), u32::MAX, 1),
            u32::MAX
        );

        // Field ops (types 0-3) over a foreign field and a regular field.
        let mh_ff = abc_builder_create_method_handle(g.b, 2, g.foreign_field);
        assert_ne!(mh_ff, u32::MAX);
        let mh_rf = abc_builder_create_method_handle(g.b, 0, g.field);
        assert_ne!(mh_rf, u32::MAX);
        // Method ops (4-8) over a foreign method and a regular method.
        let mh_fm = abc_builder_create_method_handle(g.b, 5, g.foreign_method);
        assert_ne!(mh_fm, u32::MAX);
        let mh_rm = abc_builder_create_method_handle(g.b, 4, g.method);
        assert_ne!(mh_rm, u32::MAX);
        assert_ne!(mh_ff, mh_rf);
        assert_ne!(mh_fm, mh_rm);
        // Out-of-range entities on both tagging conventions.
        assert_eq!(
            abc_builder_create_method_handle(g.b, 2, 0x8000_0005),
            u32::MAX,
            "foreign index out of range"
        );
        assert_eq!(
            abc_builder_create_method_handle(g.b, 2, 0x7777),
            u32::MAX,
            "regular field index out of range"
        );
        assert_eq!(abc_builder_create_method_handle(g.b, 5, 0x7777), u32::MAX);
        let (f, _) = g.finalize_open();
        abc_file_close(f);
    }
}

/// Code-relocation guards: unknown method/kind/target are rejected (0), the
/// foreign-field and foreign-method arms accept (1), and a null updater
/// fails the finalize.
#[test]
fn builder_relocate_and_finalize_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(
            abc_builder_relocate_code_id(
                g.b,
                u32::MAX,
                0,
                0,
                AbcCodeEntityKind_ABC_CODE_STRING,
                g.string,
            ),
            0,
            "unknown method"
        );
        assert_eq!(
            abc_builder_relocate_code_id(g.b, g.method, 0, 0, 99, g.string),
            0,
            "unknown entity kind"
        );
        assert_eq!(
            abc_builder_relocate_code_id(
                g.b,
                g.method,
                0,
                0,
                AbcCodeEntityKind_ABC_CODE_STRING,
                0x7777,
            ),
            0,
            "unresolvable target"
        );
        // Foreign field and foreign method arms accept.
        assert_eq!(
            abc_builder_relocate_code_id(
                g.b,
                g.method,
                0,
                0,
                AbcCodeEntityKind_ABC_CODE_FIELD,
                g.foreign_field,
            ),
            1
        );
        assert_eq!(
            abc_builder_relocate_code_id(
                g.b,
                g.method,
                0,
                0,
                AbcCodeEntityKind_ABC_CODE_METHOD,
                g.foreign_method,
            ),
            1
        );
        // A null updater fails the relocation-aware finalize.
        let mut out_len = 0u32;
        let ptr = abc_builder_finalize_with_code_ids(g.b, &mut out_len, None);
        assert!(ptr.is_null(), "finalize requires an updater");
        // A real updater lets the same builder finalize (the safe
        // Builder::finalize drives exactly this path); both registered
        // relocations are delivered to it.
        unsafe extern "C" fn count_update(
            _code: *mut u8,
            _size: usize,
            _byte_offset: u32,
            _operand: u32,
            _new_id: u32,
        ) -> i32 {
            UPDATE_CALLS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            1
        }
        UPDATE_CALLS.store(0, std::sync::atomic::Ordering::SeqCst);
        let ptr = abc_builder_finalize_with_code_ids(g.b, &mut out_len, Some(count_update));
        assert!(!ptr.is_null(), "finalize with an updater must succeed");
        assert_eq!(
            UPDATE_CALLS.load(std::sync::atomic::Ordering::SeqCst),
            2,
            "both relocations were delivered to the updater"
        );
        let data = std::slice::from_raw_parts(ptr, out_len as usize).to_vec();
        let f = open(&data);
        abc_file_close(f);
    }
}

// Updater invocations seen by `count_update` (tests serialize on the builder).
static UPDATE_CALLS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// `abc_builder_set_file_version` guards: null arguments and unknown tuples
/// return 0; a mapped tuple selects the API and returns 1.
#[test]
fn builder_set_file_version_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(
            abc_builder_set_file_version(std::ptr::null_mut(), [12, 0, 2, 0].as_ptr()),
            0
        );
        assert_eq!(abc_builder_set_file_version(g.b, std::ptr::null()), 0);
        assert_eq!(abc_builder_set_file_version(g.b, [12, 0, 5, 0].as_ptr()), 0);
        assert_eq!(abc_builder_set_file_version(g.b, [12, 0, 2, 0].as_ptr()), 1);
        let (f, data) = g.finalize_open();
        assert_eq!(&data[12..16], &[12, 0, 2, 0], "the selected version lands");
        abc_file_close(f);
    }
}

/// `create_proto_ex` type-resolution guards: a REFERENCE return type or
/// parameter type with an unresolvable class handle returns UINT32_MAX.
#[test]
fn builder_create_proto_ex_guards() {
    let g = GuardBuilder::new();
    unsafe {
        assert_eq!(
            abc_builder_create_proto_ex(g.b, Type_TypeId_REFERENCE, 0x7777, std::ptr::null(), 0),
            u32::MAX,
            "bad return class"
        );
        let params = [AbcProtoParam {
            type_id: Type_TypeId_REFERENCE,
            class_handle: 0x7777,
        }];
        assert_eq!(
            abc_builder_create_proto_ex(g.b, Type_TypeId_TAGGED, 0, params.as_ptr(), 1),
            u32::MAX,
            "bad parameter class"
        );
        // Positive contrast: the same calls with a valid foreign class.
        let good = [AbcProtoParam {
            type_id: Type_TypeId_REFERENCE,
            class_handle: g.foreign_cls,
        }];
        assert_ne!(
            abc_builder_create_proto_ex(
                g.b,
                Type_TypeId_REFERENCE,
                g.foreign_cls,
                good.as_ptr(),
                1
            ),
            u32::MAX
        );
        let (f, _) = g.finalize_open();
        abc_file_close(f);
    }
}
