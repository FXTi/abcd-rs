use std::env;
use std::fs;
use std::io::Write;
use std::path::Path;

fn main() {
    let out_dir = env::var("OUT_DIR").unwrap();
    let bindings_path = env::var("DEP_ISA_BRIDGE_BINDINGS_RS").expect(
        "DEP_ISA_BRIDGE_BINDINGS_RS not set — abcd-isa-sys must have links = \"isa_bridge\"",
    );

    let bindings = fs::read_to_string(&bindings_path).expect("failed to read bindings.rs");

    let mut out = Vec::new();
    writeln!(
        out,
        "// Auto-generated safe Emitter methods from abcd-isa-sys bindings."
    )
    .unwrap();
    writeln!(out, "// Do not edit manually.").unwrap();
    writeln!(out).unwrap();
    writeln!(out, "impl Emitter {{").unwrap();

    for line in bindings.lines() {
        let trimmed = line.trim();
        // Match: pub fn isa_emit_xxx(...)
        if !trimmed.starts_with("pub fn isa_emit_") {
            continue;
        }
        // Extract: isa_emit_xxx(params)
        let Some(fn_start) = trimmed.find("isa_emit_") else {
            continue;
        };
        let Some(paren_open) = trimmed.find('(') else {
            continue;
        };
        let Some(paren_close) = trimmed.rfind(')') else {
            continue;
        };

        let ffi_name = &trimmed[fn_start..paren_open];
        let rust_name_raw = &ffi_name["isa_emit_".len()..];

        // Escape Rust reserved keywords
        let rust_name = match rust_name_raw {
            "return" | "typeof" | "throw" | "try" | "yield" | "async" | "await" | "move"
            | "type" | "mod" | "in" | "if" | "else" | "loop" | "while" | "for" | "match"
            | "break" | "continue" | "fn" | "let" | "const" | "static" | "struct" | "enum"
            | "trait" | "impl" | "self" | "super" | "crate" | "pub" | "use" | "as" | "ref"
            | "mut" | "where" | "unsafe" | "extern" | "true" | "false" | "abstract" | "become"
            | "box" | "do" | "final" | "macro" | "override" | "priv" | "virtual" => {
                format!("r#{rust_name_raw}")
            }
            _ => rust_name_raw.to_string(),
        };
        let params_str = &trimmed[paren_open + 1..paren_close];

        // Parse parameters, skip the first one (e: *mut IsaEmitter)
        let params: Vec<&str> = params_str.split(',').map(|s| s.trim()).collect();
        if params.is_empty() {
            continue;
        }

        // Build method signature and call args
        let mut method_params = Vec::new();
        let mut call_args = Vec::new();
        let mut has_label = false;

        for param in params.iter().skip(1) {
            // param looks like "imm: u8" or "label_id: u32" or "v1: u8"
            let parts: Vec<&str> = param.splitn(2, ':').map(|s| s.trim()).collect();
            if parts.len() != 2 {
                continue;
            }
            let name = parts[0];
            let ty = parts[1];

            if name == "label_id" {
                method_params.push("label: Label".to_string());
                call_args.push("label.0".to_string());
                has_label = true;
            } else {
                method_params.push(format!("{name}: {ty}"));
                call_args.push(name.to_string());
            }
        }

        let method_params_str = if method_params.is_empty() {
            String::new()
        } else {
            format!(", {}", method_params.join(", "))
        };

        let call_args_str = if call_args.is_empty() {
            String::new()
        } else {
            format!(", {}", call_args.join(", "))
        };

        // Emit doc comment with mnemonic
        let mnemonic = rust_name.replace('_', ".");
        if has_label {
            writeln!(
                out,
                "/// Emit `{mnemonic}` instruction (jump target: [`Label`])."
            )
            .unwrap();
        } else {
            writeln!(out, "/// Emit `{mnemonic}` instruction.").unwrap();
        }
        writeln!(
            out,
            "pub fn {rust_name}(&mut self{method_params_str}) {{ unsafe {{ ffi::{ffi_name}(self.ptr{call_args_str}) }} }}"
        )
        .unwrap();
        writeln!(out).unwrap();
    }

    writeln!(out, "}}").unwrap();

    let out_path = Path::new(&out_dir).join("emitter_methods.rs");
    fs::write(&out_path, out).expect("failed to write emitter_methods.rs");

    // --- Generate flag_constants.rs (OpcodeFlags + Exceptions constants) ---
    let mut flags: Vec<(String, String)> = Vec::new(); // (rust_name, ffi_const_name)
    let mut exceptions: Vec<(String, String)> = Vec::new();

    for line in bindings.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("pub const ISA_FLAG_") {
            if let Some(colon) = rest.find(':') {
                let suffix = &rest[..colon];
                let ffi_name = format!("ISA_FLAG_{suffix}");
                flags.push((suffix.to_string(), ffi_name));
            }
        } else if let Some(rest) = trimmed.strip_prefix("pub const ISA_EXC_") {
            if let Some(colon) = rest.find(':') {
                let suffix = &rest[..colon];
                let ffi_name = format!("ISA_EXC_{suffix}");
                let rust_name = suffix.strip_prefix("X_").unwrap_or(suffix);
                exceptions.push((rust_name.to_string(), ffi_name));
            }
        }
    }

    flags.sort_by(|a, b| a.0.cmp(&b.0));
    flags.dedup_by(|a, b| a.0 == b.0);
    exceptions.sort_by(|a, b| a.0.cmp(&b.0));
    exceptions.dedup_by(|a, b| a.0 == b.0);

    let mut fc = Vec::new();
    writeln!(
        fc,
        "// Auto-generated from abcd-isa-sys bindings. Do not edit."
    )
    .unwrap();
    writeln!(fc).unwrap();
    writeln!(fc, "impl OpcodeFlags {{").unwrap();
    for (rust_name, ffi_name) in &flags {
        if rust_name == "THROW" {
            writeln!(
                fc,
                "    /// Synthetic flag: instruction's primary role is to throw (bit 31)."
            )
            .unwrap();
        }
        writeln!(
            fc,
            "    pub const {rust_name}: Self = Self(ffi::{ffi_name});"
        )
        .unwrap();
    }
    writeln!(fc, "}}").unwrap();
    writeln!(fc).unwrap();
    writeln!(fc, "impl Exceptions {{").unwrap();
    for (rust_name, ffi_name) in &exceptions {
        writeln!(
            fc,
            "    pub const {rust_name}: Self = Self(ffi::{ffi_name});"
        )
        .unwrap();
    }
    writeln!(fc, "}}").unwrap();

    let fc_path = Path::new(&out_dir).join("flag_constants.rs");
    fs::write(&fc_path, fc).expect("failed to write flag_constants.rs");

    // --- Generate roundtrip_tests.rs (test dispatch for every emitter method) ---
    let mut rt = Vec::new();
    writeln!(
        rt,
        "// Auto-generated roundtrip test dispatch from abcd-isa-sys bindings."
    )
    .unwrap();
    writeln!(rt, "// Do not edit manually.").unwrap();
    writeln!(rt).unwrap();
    writeln!(
        rt,
        "/// Emit one instruction via the named mnemonic with zero/default operands,"
    )
    .unwrap();
    writeln!(
        rt,
        "/// build, decode, and return the decoded mnemonic string."
    )
    .unwrap();
    writeln!(rt, "fn roundtrip_one(mnemonic: &str) -> Option<String> {{").unwrap();
    writeln!(rt, "    use abcd_isa::{{Emitter, Inst}};").unwrap();
    writeln!(rt, "    let mut e = Emitter::new();").unwrap();
    writeln!(rt, "    match mnemonic {{").unwrap();

    for line in bindings.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with("pub fn isa_emit_") {
            continue;
        }
        let Some(fn_start) = trimmed.find("isa_emit_") else {
            continue;
        };
        let Some(paren_open) = trimmed.find('(') else {
            continue;
        };
        let Some(paren_close) = trimmed.rfind(')') else {
            continue;
        };

        let ffi_name = &trimmed[fn_start..paren_open];
        let rust_name_raw = &ffi_name["isa_emit_".len()..];

        // Mnemonic: underscores become dots (matching the ISA convention)
        let mnemonic = rust_name_raw.replace('_', ".");

        let rust_name = match rust_name_raw {
            "return" | "typeof" | "throw" | "try" | "yield" | "async" | "await" | "move"
            | "type" | "mod" | "in" | "if" | "else" | "loop" | "while" | "for" | "match"
            | "break" | "continue" | "fn" | "let" | "const" | "static" | "struct" | "enum"
            | "trait" | "impl" | "self" | "super" | "crate" | "pub" | "use" | "as" | "ref"
            | "mut" | "where" | "unsafe" | "extern" | "true" | "false" | "abstract" | "become"
            | "box" | "do" | "final" | "macro" | "override" | "priv" | "virtual" => {
                format!("r#{rust_name_raw}")
            }
            _ => rust_name_raw.to_string(),
        };

        let params_str = &trimmed[paren_open + 1..paren_close];
        let params: Vec<&str> = params_str.split(',').map(|s| s.trim()).collect();

        // Build call arguments with default values (skip first param which is the emitter ptr)
        let mut call_args = Vec::new();
        let mut has_label = false;
        for param in params.iter().skip(1) {
            let parts: Vec<&str> = param.splitn(2, ':').map(|s| s.trim()).collect();
            if parts.len() != 2 {
                continue;
            }
            let name = parts[0];
            let ty = parts[1];
            if name == "label_id" {
                has_label = true;
                call_args.push("label".to_string());
            } else {
                // Default value: 0 cast to the appropriate type
                call_args.push(format!("0{ty}"));
            }
        }

        // For label instructions, we need to create and bind a label
        if has_label {
            let args_str = call_args.join(", ");
            writeln!(
                rt,
                "        \"{mnemonic}\" => {{ let label = e.label(); e.{rust_name}({args_str}); e.bind(label); }},"
            )
            .unwrap();
        } else if call_args.is_empty() {
            writeln!(rt, "        \"{mnemonic}\" => {{ e.{rust_name}(); }},").unwrap();
        } else {
            let args_str = call_args.join(", ");
            writeln!(
                rt,
                "        \"{mnemonic}\" => {{ e.{rust_name}({args_str}); }},"
            )
            .unwrap();
        }
    }

    writeln!(rt, "        _ => return None,").unwrap();
    writeln!(rt, "    }}").unwrap();
    writeln!(rt, "    // Append a terminator so the emitter can finalize").unwrap();
    writeln!(rt, "    e.returnundefined();").unwrap();
    writeln!(rt, "    let bytecode = e.build().ok()?;").unwrap();
    writeln!(rt, "    let inst = Inst::decode(&bytecode)?;").unwrap();
    writeln!(rt, "    Some(inst.info().mnemonic().to_string())").unwrap();
    writeln!(rt, "}}").unwrap();
    writeln!(rt).unwrap();

    let rt_path = Path::new(&out_dir).join("roundtrip_tests.rs");
    fs::write(&rt_path, rt).expect("failed to write roundtrip_tests.rs");

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={bindings_path}");
    println!("cargo:rerun-if-env-changed=DEP_ISA_BRIDGE_BINDINGS_RS");
}
