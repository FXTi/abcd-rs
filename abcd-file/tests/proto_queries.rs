use abcd_file::{AccessFlags, Builder, Type, decode};
use abcd_file_sys as sys;
use std::ffi::c_void;

unsafe extern "C" fn collect_type(raw: u8, ctx: *mut c_void) {
    // SAFETY: synchronous enumeration below passes a live Vec<u8>.
    unsafe { &mut *ctx.cast::<Vec<u8>>() }.push(raw);
}

#[test]
fn proto_queries_preserve_arguments_in_any_order() {
    let mut builder = Builder::new();
    builder.set_api(9, "");
    let class = builder.add_global_class();
    let args = [Type::I32, Type::F64, Type::Bool, Type::I64, Type::U8];
    let proto = builder.create_proto(Type::Tagged, &args);
    let (code, _) = abcd_isa::encode(&[abcd_isa::Bytecode::Returnundefined]).unwrap();
    builder.class_add_method(
        class,
        "f",
        proto,
        AccessFlags::STATIC,
        &code,
        0,
        args.len() as u32,
    );
    let bytes = builder.finalize().unwrap();
    let file = decode(&bytes).unwrap();
    let method = file.all_methods().next().unwrap().1;
    assert_eq!(method.arg_types, args);

    // SAFETY: bytes and all nested accessor owners outlive the queries; all
    // handles are checked and closed after use.
    unsafe {
        let file_handle = sys::abc_file_open(bytes.as_ptr(), bytes.len());
        assert!(!file_handle.is_null());
        let method_handle = sys::abc_method_open(file_handle, method.offset);
        assert!(!method_handle.is_null());
        let proto = sys::abc_proto_open(file_handle, sys::abc_method_get_proto_id(method_handle));
        assert!(!proto.is_null());
        for _ in 0..3 {
            // GetRefNum lazily enumerates the accessor on its first call.
            assert_eq!(sys::abc_proto_get_ref_num(proto), 0);
            assert_eq!(sys::abc_proto_num_args(proto), args.len() as u32);
            let mut types = Vec::<u8>::new();
            sys::abc_proto_enumerate_types(
                proto,
                Some(collect_type),
                (&mut types as *mut Vec<u8>).cast(),
            );
            let expected = [
                sys::Type_TypeId_TAGGED,
                sys::Type_TypeId_I32,
                sys::Type_TypeId_F64,
                sys::Type_TypeId_U1,
                sys::Type_TypeId_I64,
                sys::Type_TypeId_U8,
            ];
            assert_eq!(types, expected);
            assert_eq!(sys::abc_proto_num_args(proto), args.len() as u32);
            assert_eq!(sys::abc_proto_get_arg_type(proto, 1), sys::Type_TypeId_F64);
        }
        sys::abc_proto_close(proto);
        sys::abc_method_close(method_handle);
        sys::abc_file_close(file_handle);
    }
}
