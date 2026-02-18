#![allow(
    non_upper_case_globals,
    non_camel_case_types,
    non_snake_case,
    dead_code
)]

include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builder_roundtrip() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());

            // Set API version
            let sub_api = b"beta1\0";
            abc_builder_set_api(b, 12, sub_api.as_ptr() as *const std::ffi::c_char);

            // Create a class with one method
            let cls_desc = b"L_GLOBAL;\0";
            let cls = abc_builder_add_class(b, cls_desc.as_ptr() as *const std::ffi::c_char);
            assert_ne!(cls, u32::MAX);

            let method_name = b"func_main_0\0";
            // Minimal bytecode: just a return instruction (0xa0 = returnundefined)
            let code: [u8; 1] = [0xa0];
            // Create a TAGGED proto (0x0d) with no params, then add method
            let proto = abc_builder_create_proto(b, 0x0d, std::ptr::null(), 0);
            let m = abc_builder_class_add_method_with_proto(
                b,
                cls,
                method_name.as_ptr() as *const std::ffi::c_char,
                proto,
                0x0001, // ACC_PUBLIC
                code.as_ptr(),
                code.len() as u32,
                1, // num_vregs
                0, // num_args
            );
            assert_ne!(m, u32::MAX);

            // Finalize
            let mut out_len: u32 = 0;
            let ptr = abc_builder_finalize(b, &mut out_len);
            assert!(!ptr.is_null(), "builder finalize should succeed");
            assert!(out_len > 0, "output should be non-empty");

            // Verify the output is a valid ABC file by opening it
            let data = std::slice::from_raw_parts(ptr, out_len as usize);
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null(), "should open the built ABC file");

            let num_classes = abc_file_num_classes(f);
            assert!(num_classes > 0, "built file should have classes");

            abc_file_close(f);
            abc_builder_free(b);
        }
    }
}
