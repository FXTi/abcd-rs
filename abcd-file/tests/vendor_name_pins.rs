//! V-I1 pins (q-P3, 2026-09-25): the vendor-name strings hardcoded in
//! `decode.rs` must track the vendor's own constants. The bridge exports
//! the vendor values (`abc_vendor_*`); a vendor rename breaks the bridge
//! build (constant name), a vendor value change fails here.
//!
//! The fourth name (`L_ESModuleRecord;`) has no referenceable vendor
//! constant (in-cone constant is private, collect_util.h:40; the public
//! abc2program one is outside the CI sparse cone) — it stays behaviorally
//! pinned by the module-record tests, documented at the constant.

use abcd_file_sys as sys;
use std::ffi::CStr;

fn cstr(raw: *const std::os::raw::c_char) -> String {
    // SAFETY: the bridge returns pointers to process-lifetime static
    // std::strings, always NUL-terminated.
    unsafe { CStr::from_ptr(raw) }.to_str().unwrap().to_owned()
}

#[test]
fn type_summary_offset_field_matches_vendor() {
    assert_eq!(
        abcd_file::TYPE_SUMMARY_OFFSET_FIELD,
        cstr(unsafe { sys::abc_vendor_type_summary_field_name() }),
        "vendor renamed typeSummaryOffset (ark::TYPE_SUMMARY_FIELD_NAME)"
    );
}

#[test]
fn module_request_phase_field_matches_vendor() {
    assert_eq!(
        abcd_file::MODULE_REQUEST_PHASE_FIELD,
        cstr(unsafe { sys::abc_vendor_module_request_phase_idx() }),
        "vendor renamed moduleRequestPhaseIdx (ark::MODULE_REQUEST_PAHSE_IDX)"
    );
}

#[test]
fn scope_names_record_descriptor_matches_vendor() {
    // Our constant is the descriptor form: "L" + vendor record name + ";".
    let vendor = cstr(unsafe { sys::abc_vendor_scope_names_record() });
    assert_eq!(
        abcd_file::ES_SCOPE_NAMES_RECORD_DESCRIPTOR,
        format!("L{vendor};"),
        "vendor renamed _ESScopeNamesRecord (ark::SCOPE_NAME_RECORD)"
    );
}
