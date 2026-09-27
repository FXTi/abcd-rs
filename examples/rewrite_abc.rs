//! N72-C4 hand-reduction helper: decode → lift → verify → lower → encode
//! a single .abc (the exact `rewrite_fixture` v2lift pipeline from
//! tests/lift-lower/rewrite_pipeline.rs) so a rewritten candidate can be
//! run under the docker ark_js_vm oracle.
//!
//! Usage: cargo run --release --example rewrite_abc -- <in.abc> <out.abc>

use abcd_file::File;
use abcd_ir::{verify_module, FuncId, Module};
use abcd_lift::lift_file;
use abcd_lower::{lower_function_with_options, to_method_body, LowerOptions};

fn front_end(path: &std::path::Path) -> Result<(File, Module), String> {
    let data = std::fs::read(path).map_err(|e| format!("read: {e}"))?;
    let file = abcd_file::decode(&data).map_err(|e| format!("decode: {e}"))?;
    let module = lift_file(&file).map_err(|e| format!("lift: {e}"))?;
    let report = verify_module(&module);
    if !report.is_ok() {
        return Err(format!("verify: {:?}", report.errors));
    }
    Ok((file, module))
}

fn rewrite(module: &Module, file: &File) -> Result<Vec<u8>, String> {
    let mut bodies = Vec::new();
    for index in 0..module.functions.len() {
        let func_id = FuncId::new(index as u32);
        let func = module.func(func_id).expect("function-table index");
        if func.blocks.is_empty() {
            bodies.push(None);
            continue;
        }
        let name = module.sym.resolve(func.name).unwrap_or("?").to_string();
        let lowered = lower_function_with_options(module, func_id, LowerOptions::default())
            .map_err(|e| format!("lower {name}: {e}"))?;
        let body = to_method_body(module, func_id, &lowered, file)
            .map_err(|e| format!("to_method_body {name}: {e}"))?;
        bodies.push(Some(body));
    }

    let mut rebuilt = file.clone();
    let mut cursor = bodies.into_iter();
    for class in rebuilt.classes.values_mut() {
        for method in &mut class.methods {
            let body = cursor.next().expect("one slot per method");
            if method.body.is_some() {
                method.body = Some(body.expect("a lowered body for every method that had one"));
            }
        }
    }
    assert!(cursor.next().is_none());

    abcd_file::encode(&rebuilt).map_err(|e| format!("encode: {e}"))
}

fn main() {
    let mut args = std::env::args().skip(1);
    let input = args.next().expect("input .abc path");
    let output = args.next().expect("output .abc path");
    let (file, module) = front_end(std::path::Path::new(&input)).expect("front_end");
    let encoded = rewrite(&module, &file).expect("rewrite");
    std::fs::write(&output, encoded).expect("write output");
    eprintln!("rewrote {input} -> {output}");
}
