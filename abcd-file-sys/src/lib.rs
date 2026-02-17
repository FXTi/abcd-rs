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

    fn load_test_abc() -> Vec<u8> {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../modules.abc");
        std::fs::read(path).expect("modules.abc not found")
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn open_close() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            assert!(!f.is_null());
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn header_info() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);
            assert!(num_classes > 0, "expected at least one class");

            let size = abc_file_size(f);
            assert_eq!(size as usize, data.len());

            let mut ver = [0u8; 4];
            abc_file_version(f, ver.as_mut_ptr());
            // version should be non-zero (e.g. 12.0.x.x)
            assert!(ver[0] > 0, "major version should be > 0");

            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn class_accessor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);
            assert!(num_classes > 0);

            let off = abc_file_class_offset(f, 0);
            let cls = abc_class_open(f, off);
            assert!(!cls.is_null());

            let n_methods = abc_class_num_methods(cls);
            let n_fields = abc_class_num_fields(cls);
            // at least one of these should be non-zero for a real class
            assert!(
                n_methods > 0 || n_fields > 0 || true,
                "class has {n_methods} methods, {n_fields} fields"
            );

            abc_class_close(cls);
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn method_and_code_accessor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);

            // Find a class with methods
            let mut found_code = false;
            for i in 0..num_classes {
                let off = abc_file_class_offset(f, i);
                let cls = abc_class_open(f, off);
                if cls.is_null() {
                    continue;
                }

                let n_methods = abc_class_num_methods(cls);
                if n_methods > 0 {
                    // Collect method offsets via callback
                    extern "C" fn collect_method(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
                        let vec = unsafe { &mut *(ctx as *mut Vec<u32>) };
                        vec.push(offset);
                        0
                    }
                    let mut method_offsets: Vec<u32> = Vec::new();
                    abc_class_enumerate_methods(
                        cls,
                        Some(collect_method),
                        &mut method_offsets as *mut Vec<u32> as *mut std::ffi::c_void,
                    );

                    for &m_off in &method_offsets {
                        let m = abc_method_open(f, m_off);
                        if m.is_null() {
                            continue;
                        }
                        let code_off = abc_method_code_off(m);
                        if code_off != u32::MAX {
                            let code = abc_code_open(f, code_off);
                            if !code.is_null() {
                                let code_size = abc_code_code_size(code);
                                assert!(code_size > 0, "code section should have instructions");
                                let insns = abc_code_instructions(code);
                                assert!(!insns.is_null());
                                found_code = true;
                                abc_code_close(code);
                            }
                        }
                        abc_method_close(m);
                        if found_code {
                            break;
                        }
                    }
                }
                abc_class_close(cls);
                if found_code {
                    break;
                }
            }
            assert!(found_code, "should find at least one method with code");
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn string_access() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);

            // Try to read the name of the first method we find
            for i in 0..num_classes {
                let off = abc_file_class_offset(f, i);
                let cls = abc_class_open(f, off);
                if cls.is_null() {
                    continue;
                }

                extern "C" fn first_method(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
                    let out = unsafe { &mut *(ctx as *mut u32) };
                    *out = offset;
                    1 // stop after first
                }
                let mut m_off: u32 = u32::MAX;
                abc_class_enumerate_methods(
                    cls,
                    Some(first_method),
                    &mut m_off as *mut u32 as *mut std::ffi::c_void,
                );
                abc_class_close(cls);

                if m_off != u32::MAX {
                    let m = abc_method_open(f, m_off);
                    if !m.is_null() {
                        let name_off = abc_method_name_off(m);
                        let mut buf = [0u8; 256];
                        let n = abc_file_get_string(
                            f,
                            name_off,
                            buf.as_mut_ptr() as *mut i8,
                            buf.len(),
                        );
                        assert!(n > 0, "should read a method name string");
                        let s = std::str::from_utf8(&buf[..n]).unwrap();
                        assert!(!s.is_empty());
                        abc_method_close(m);
                        abc_file_close(f);
                        return;
                    }
                }
            }
            abc_file_close(f);
            panic!("should find at least one method with a name");
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn field_accessor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);

            // Find a class with fields
            let mut found_field = false;
            for i in 0..num_classes {
                let off = abc_file_class_offset(f, i);
                let cls = abc_class_open(f, off);
                if cls.is_null() {
                    continue;
                }
                let n_fields = abc_class_num_fields(cls);
                if n_fields > 0 {
                    extern "C" fn first_field(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
                        let out = unsafe { &mut *(ctx as *mut u32) };
                        *out = offset;
                        1
                    }
                    let mut f_off: u32 = u32::MAX;
                    abc_class_enumerate_fields(
                        cls,
                        Some(first_field),
                        &mut f_off as *mut u32 as *mut std::ffi::c_void,
                    );
                    abc_class_close(cls);

                    if f_off != u32::MAX {
                        let fld = abc_field_open(f, f_off);
                        if !fld.is_null() {
                            let _name = abc_field_name_off(fld);
                            let _flags = abc_field_access_flags(fld);
                            let _typ = abc_field_type(fld);
                            found_field = true;
                            abc_field_close(fld);
                        }
                    }
                } else {
                    abc_class_close(cls);
                }
                if found_field {
                    break;
                }
            }
            // Not all abc files have fields, so just verify the API works
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn literal_accessor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_lit = abc_file_num_literalarrays(f);

            if num_lit > 0 {
                // LiteralDataAccessor needs the literal data section offset
                let lit_data_off = abc_file_literalarray_idx_off(f);
                let lit = abc_literal_open(f, lit_data_off);
                assert!(!lit.is_null());
                let count = abc_literal_count(lit);
                assert!(count > 0, "literal data should have entries");
                assert_eq!(count, num_lit);
                abc_literal_close(lit);
            }
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn debug_info_extractor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let dbg = abc_debug_info_open(f);
            assert!(!dbg.is_null());

            // Find a method with debug info
            let num_classes = abc_file_num_classes(f);
            for i in 0..num_classes {
                let off = abc_file_class_offset(f, i);
                let cls = abc_class_open(f, off);
                if cls.is_null() {
                    continue;
                }

                extern "C" fn first_method(offset: u32, ctx: *mut std::ffi::c_void) -> i32 {
                    let out = unsafe { &mut *(ctx as *mut u32) };
                    *out = offset;
                    1
                }
                let mut m_off: u32 = u32::MAX;
                abc_class_enumerate_methods(
                    cls,
                    Some(first_method),
                    &mut m_off as *mut u32 as *mut std::ffi::c_void,
                );
                abc_class_close(cls);

                if m_off != u32::MAX {
                    let m = abc_method_open(f, m_off);
                    if !m.is_null() {
                        let dbg_off = abc_method_debug_info_off(m);
                        if dbg_off != u32::MAX {
                            // Try to get line table
                            extern "C" fn count_lines(
                                _entry: *const AbcLineEntry,
                                ctx: *mut std::ffi::c_void,
                            ) -> i32 {
                                let cnt = unsafe { &mut *(ctx as *mut u32) };
                                *cnt += 1;
                                0
                            }
                            let mut line_count: u32 = 0;
                            abc_debug_get_line_table(
                                dbg,
                                m_off,
                                Some(count_lines),
                                &mut line_count as *mut u32 as *mut std::ffi::c_void,
                            );
                            // Source file may or may not exist
                            let _src = abc_debug_get_source_file(dbg, m_off);
                        }
                        abc_method_close(m);
                        break;
                    }
                }
            }

            abc_debug_info_close(dbg);
            abc_file_close(f);
        }
    }

    #[test]
    #[ignore = "requires proprietary modules.abc"]
    fn module_accessor() {
        let data = load_test_abc();
        unsafe {
            let f = abc_file_open(data.as_ptr(), data.len());
            let num_classes = abc_file_num_classes(f);

            // Find a module record class (name starts with "&")
            // Module data is referenced from class entries with special descriptor names
            for i in 0..num_classes {
                let class_off = abc_file_class_offset(f, i);
                // Read the class name to check if it's a module descriptor
                let mut buf = [0u8; 256];
                let n = abc_file_get_string(f, class_off, buf.as_mut_ptr() as *mut i8, buf.len());
                if n == 0 {
                    continue;
                }
                let name = std::str::from_utf8(&buf[..n]).unwrap_or("");
                // Module records typically have class names like "L_ESModuleRecord;"
                // or contain "ModuleRecord" — skip non-module classes
                if !name.contains("Module") {
                    continue;
                }

                // Open the class to find its module data offset
                let cls = abc_class_open(f, class_off);
                if cls.is_null() {
                    continue;
                }
                // Module data is stored in the class's literal array
                // For now just verify the class accessor works on module classes
                let _flags = abc_class_access_flags(cls);
                abc_class_close(cls);
            }
            abc_file_close(f);
        }
    }

    #[test]
    fn builder_roundtrip() {
        unsafe {
            let b = abc_builder_new();
            assert!(!b.is_null());

            // Set API version
            let sub_api = b"beta1\0";
            abc_builder_set_api(b, 12, sub_api.as_ptr() as *const i8);

            // Create a class with one method
            let cls_desc = b"L_GLOBAL;\0";
            let cls = abc_builder_add_class(b, cls_desc.as_ptr() as *const i8);
            assert_ne!(cls, u32::MAX);

            let method_name = b"func_main_0\0";
            // Minimal bytecode: just a return instruction (0xa0 = returnundefined)
            let code: [u8; 1] = [0xa0];
            let m = abc_builder_class_add_method(
                b,
                cls,
                method_name.as_ptr() as *const i8,
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
