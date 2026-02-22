//! ABC file format version utilities.

use abcd_isa::Version;

/// Check if the given version includes literal arrays in the header.
pub fn has_literal_array_in_header(ver: &Version) -> bool {
    unsafe { abcd_file_sys::abc_contains_literal_array_in_header(ver.as_bytes().as_ptr()) != 0 }
}
