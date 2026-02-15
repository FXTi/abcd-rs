use clap::{Parser, Subcommand};
use std::fs;
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "abcd-rs", about = "ArkCompiler ABC bytecode decompiler")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Disassemble an ABC file to human-readable bytecode listing
    Disasm {
        /// Path to the .abc file
        input: PathBuf,
    },
    /// Show ABC file header and metadata
    Info {
        /// Path to the .abc file
        input: PathBuf,
    },
    /// Decompile an ABC file to JavaScript
    Decompile {
        /// Path to the .abc file
        input: PathBuf,
        /// Output directory (default: stdout)
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match cli.command {
        Commands::Disasm { input } => cmd_disasm(&input),
        Commands::Info { input } => cmd_info(&input),
        Commands::Decompile { input, output } => cmd_decompile(&input, output.as_deref()),
    }
}

// === StringResolver implementation for AbcFile ===

struct AbcResolver<'a> {
    abc: &'a abcd_parser::AbcFile,
}

impl<'a> abcd_decompiler::expr_recovery::StringResolver for AbcResolver<'a> {
    fn resolve_string(&self, method_off: u32, entity_id: u32) -> Option<String> {
        let off = self.abc.index_section().resolve_offset_by_index(
            self.abc.data(),
            method_off,
            entity_id as u16,
        )?;
        self.abc.get_string(off).ok()
    }

    fn resolve_offset(&self, method_off: u32, entity_id: u32) -> Option<u32> {
        self.abc.index_section().resolve_offset_by_index(
            self.abc.data(),
            method_off,
            entity_id as u16,
        )
    }

    fn resolve_literal_array(
        &self,
        method_off: u32,
        entity_id: u32,
    ) -> Option<abcd_parser::literal::LiteralArray> {
        let off = self.abc.index_section().resolve_offset_by_index(
            self.abc.data(),
            method_off,
            entity_id as u16,
        )?;
        abcd_parser::literal::LiteralArray::parse(self.abc.data(), off).ok()
    }

    fn get_string_at_offset(&self, offset: u32) -> Option<String> {
        self.abc.get_string(offset).ok()
    }

    fn resolve_method_name(&self, method_off: u32, entity_id: u32) -> Option<String> {
        let off = self.abc.index_section().resolve_offset_by_index(
            self.abc.data(),
            method_off,
            entity_id as u16,
        )?;
        let method = abcd_parser::method::MethodData::parse(self.abc.data(), off).ok()?;
        if method.name.is_empty() {
            None
        } else {
            Some(method.name)
        }
    }
}

fn cmd_info(path: &PathBuf) {
    let abc = match abcd_parser::AbcFile::open(path.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let h = &abc.header;
    println!("=== ABC File Info ===");
    println!(
        "Version:          {}.{}.{}.{}",
        h.version[0], h.version[1], h.version[2], h.version[3]
    );
    println!("File size:        {} bytes", h.file_size);
    println!("Checksum:         {:#010x}", h.checksum);
    println!("Classes:          {}", h.num_classes);
    println!("Literal arrays:   {}", h.num_literalarrays);
    println!("Line num progs:   {}", h.num_lnps);
    println!("Index regions:    {}", h.num_indexes);
    println!(
        "Foreign region:   {:#x}..{:#x}",
        h.foreign_off,
        h.foreign_off + h.foreign_size
    );
}

fn cmd_disasm(path: &PathBuf) {
    let abc = match abcd_parser::AbcFile::open(path.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let h = &abc.header;
    println!("# ABC Disassembly");
    println!(
        "# Version: {}.{}.{}.{}",
        h.version[0], h.version[1], h.version[2], h.version[3]
    );
    println!(
        "# Classes: {}, Literal arrays: {}",
        h.num_classes, h.num_literalarrays
    );
    println!();

    for class_off in abc.class_offsets() {
        if abc.is_foreign(class_off) {
            continue;
        }

        let class = match abcd_parser::class::ClassData::parse(abc.data(), class_off) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("# Error parsing class at {class_off:#x}: {e}");
                continue;
            }
        };

        println!("# ============================================");
        println!("# Class: {}", class.name);
        if let Some(ref sf) = class.source_file {
            println!("# Source: {sf}");
        }
        println!(
            "# Methods: {}, Fields: {}",
            class.num_methods, class.num_fields
        );
        println!();

        for &method_off in &class.method_offsets {
            disasm_method(&abc, method_off as u32);
        }
    }
}

fn disasm_method(abc: &abcd_parser::AbcFile, method_off: u32) {
    let method = match abcd_parser::method::MethodData::parse(abc.data(), method_off) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("# Error parsing method at {method_off:#x}: {e}");
            return;
        }
    };

    println!(".function {} {{", method.name);

    let Some(code_off) = method.code_off else {
        println!("    # (no code - native or abstract)");
        println!("}}");
        println!();
        return;
    };

    let code = match abcd_parser::code::CodeData::parse(abc.data(), code_off) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("    # Error parsing code at {code_off:#x}: {e}");
            println!("}}");
            println!();
            return;
        }
    };

    println!(
        "    # vregs: {}, args: {}, code_size: {}",
        code.num_vregs,
        code.num_args,
        code.instructions.len()
    );

    let instructions = abcd_decompiler::decode_method(&code.instructions);
    for insn in &instructions {
        let operands_str: Vec<String> = insn
            .operands
            .iter()
            .map(|op| format_operand(abc, method_off, insn.offset, op))
            .collect();

        let ops = if operands_str.is_empty() {
            String::new()
        } else {
            format!(" {}", operands_str.join(", "))
        };

        println!("    {:#06x}  {}{ops}", insn.offset, insn.opcode);
    }

    for tb in &code.try_blocks {
        println!(
            "    # try [{:#x}..{:#x}]",
            tb.start_pc,
            tb.start_pc + tb.length
        );
        for cb in &tb.catch_blocks {
            if cb.type_idx == 0 {
                println!("    #   catch_all -> {:#x}", cb.handler_pc);
            } else {
                println!("    #   catch type={} -> {:#x}", cb.type_idx, cb.handler_pc);
            }
        }
    }

    println!("}}");
    println!();
}

fn format_operand(
    abc: &abcd_parser::AbcFile,
    method_off: u32,
    insn_offset: u32,
    op: &abcd_ir::instruction::Operand,
) -> String {
    match op {
        abcd_ir::instruction::Operand::Reg(r) => format!("v{r}"),
        abcd_ir::instruction::Operand::Imm(i) => format!("{i}"),
        abcd_ir::instruction::Operand::FloatImm(f) => format!("{f}"),
        abcd_ir::instruction::Operand::EntityId(id) => {
            let resolved_off =
                abc.index_section()
                    .resolve_offset_by_index(abc.data(), method_off, *id as u16);

            if let Some(off) = resolved_off {
                match abc.get_string(off) {
                    Ok(s) if !s.is_empty() => format!("\"{s}\""),
                    _ => format!("@{off:#x}"),
                }
            } else {
                format!("#{id}")
            }
        }
        abcd_ir::instruction::Operand::JumpOffset(off) => {
            let target = insn_offset as i64 + *off as i64;
            format!("-> {target:#x}")
        }
    }
}

fn cmd_decompile(path: &PathBuf, output_dir: Option<&std::path::Path>) {
    let abc = match abcd_parser::AbcFile::open(path.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let resolver = AbcResolver { abc: &abc };

    if let Some(dir) = output_dir {
        fs::create_dir_all(dir).unwrap_or_else(|e| {
            eprintln!("Error creating output directory: {e}");
            std::process::exit(1);
        });
    }

    for class_off in abc.class_offsets() {
        if abc.is_foreign(class_off) {
            continue;
        }

        let class = match abcd_parser::class::ClassData::parse(abc.data(), class_off) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("// Error parsing class at {class_off:#x}: {e}");
                continue;
            }
        };

        let mut class_output = String::new();
        let source_file = class.source_file.as_deref().unwrap_or(&class.name);

        // Try to parse module record from class fields
        let module_record = class
            .field_values
            .iter()
            .find(|(name, _)| name == "moduleRecordIdx")
            .and_then(|(_, offset)| {
                abcd_parser::module_record::ModuleRecord::parse(abc.data(), *offset).ok()
            });

        // Generate import statements
        if let Some(ref mr) = module_record {
            for imp in &mr.regular_imports {
                let module_path = mr
                    .module_requests
                    .get(imp.module_request_idx as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                if imp.import_name == "default" {
                    class_output.push_str(&format!(
                        "import {} from '{module_path}';\n",
                        imp.local_name
                    ));
                } else if imp.local_name == imp.import_name {
                    class_output.push_str(&format!(
                        "import {{ {} }} from '{module_path}';\n",
                        imp.import_name
                    ));
                } else {
                    class_output.push_str(&format!(
                        "import {{ {} as {} }} from '{module_path}';\n",
                        imp.import_name, imp.local_name
                    ));
                }
            }
            for imp in &mr.namespace_imports {
                let module_path = mr
                    .module_requests
                    .get(imp.module_request_idx as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                class_output.push_str(&format!(
                    "import * as {} from '{module_path}';\n",
                    imp.local_name
                ));
            }
            for se in &mr.star_exports {
                let module_path = mr
                    .module_requests
                    .get(se.module_request_idx as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                class_output.push_str(&format!("export * from '{module_path}';\n"));
            }
            for ie in &mr.indirect_exports {
                let module_path = mr
                    .module_requests
                    .get(ie.module_request_idx as usize)
                    .map(|s| s.as_str())
                    .unwrap_or("?");
                if ie.export_name == ie.import_name {
                    class_output.push_str(&format!(
                        "export {{ {} }} from '{module_path}';\n",
                        ie.import_name
                    ));
                } else {
                    class_output.push_str(&format!(
                        "export {{ {} as {} }} from '{module_path}';\n",
                        ie.import_name, ie.export_name
                    ));
                }
            }
            if !mr.regular_imports.is_empty()
                || !mr.namespace_imports.is_empty()
                || !mr.star_exports.is_empty()
                || !mr.indirect_exports.is_empty()
            {
                class_output.push('\n');
            }
        }

        for &method_off in &class.method_offsets {
            decompile_method_to_string(&abc, &resolver, method_off as u32, &mut class_output);
        }

        // Generate local export statements
        if let Some(ref mr) = module_record {
            if !mr.local_exports.is_empty() {
                let exports: Vec<String> = mr
                    .local_exports
                    .iter()
                    .map(|e| {
                        if e.local_name == e.export_name {
                            e.export_name.clone()
                        } else {
                            format!("{} as {}", e.local_name, e.export_name)
                        }
                    })
                    .collect();
                class_output.push_str(&format!("export {{ {} }};\n", exports.join(", ")));
            }
        }

        // Replace __module_N and __export_N placeholders with actual names
        if let Some(ref mr) = module_record {
            // Build import name mapping: __module_N → local_name from regular_imports
            for (i, imp) in mr.regular_imports.iter().enumerate() {
                let placeholder = format!("__module_{i}");
                class_output = class_output.replace(&placeholder, &imp.local_name);
            }
            // Namespace imports come after regular imports in the index
            let ns_offset = mr.regular_imports.len();
            for (i, imp) in mr.namespace_imports.iter().enumerate() {
                let placeholder = format!("__module_{}", ns_offset + i);
                class_output = class_output.replace(&placeholder, &imp.local_name);
            }
            // Local module vars: __local_module_N → local_name from local_exports
            for (i, exp) in mr.local_exports.iter().enumerate() {
                let placeholder = format!("__local_module_{i}");
                class_output = class_output.replace(&placeholder, &exp.local_name);
            }
            // Export vars: __export_N → export_name from local_exports
            for (i, exp) in mr.local_exports.iter().enumerate() {
                let placeholder = format!("__export_{i}");
                class_output = class_output.replace(&placeholder, &exp.export_name);
            }
        }

        if let Some(dir) = output_dir {
            let rel_path = class_name_to_path(source_file);
            let out_path = dir.join(&rel_path);
            if let Some(parent) = out_path.parent() {
                fs::create_dir_all(parent).unwrap_or_else(|e| {
                    eprintln!("Error creating directory {}: {e}", parent.display());
                });
            }
            // Append if file exists (multiple classes may share a source file)
            let mut existing = fs::read_to_string(&out_path).unwrap_or_default();
            existing.push_str(&class_output);
            fs::write(&out_path, existing).unwrap_or_else(|e| {
                eprintln!("Error writing {}: {e}", out_path.display());
            });
        } else {
            print!("{class_output}");
        }
    }
}

fn decompile_method_to_string(
    abc: &abcd_parser::AbcFile,
    resolver: &AbcResolver,
    method_off: u32,
    output: &mut String,
) {
    let method = match abcd_parser::method::MethodData::parse(abc.data(), method_off) {
        Ok(m) => m,
        Err(e) => {
            output.push_str(&format!(
                "// Error parsing method at {method_off:#x}: {e}\n"
            ));
            return;
        }
    };

    let Some(code_off) = method.code_off else {
        return; // Skip native/abstract methods
    };

    let code = match abcd_parser::code::CodeData::parse(abc.data(), code_off) {
        Ok(c) => c,
        Err(e) => {
            output.push_str(&format!("// Error parsing code at {code_off:#x}: {e}\n"));
            return;
        }
    };

    // Convert parser try blocks to IR try blocks
    let try_blocks: Vec<abcd_ir::instruction::TryBlockInfo> = code
        .try_blocks
        .iter()
        .map(|tb| abcd_ir::instruction::TryBlockInfo {
            start_pc: tb.start_pc,
            length: tb.length,
            catch_blocks: tb
                .catch_blocks
                .iter()
                .map(|cb| abcd_ir::instruction::CatchBlockInfo {
                    type_idx: cb.type_idx,
                    handler_pc: cb.handler_pc,
                    code_size: cb.code_size,
                })
                .collect(),
        })
        .collect();

    let js = abcd_decompiler::decompile_method(
        &code.instructions,
        &try_blocks,
        resolver,
        method_off,
        code.num_vregs,
        code.num_args,
    );

    // Detect rest parameters by scanning for copyrestargs instruction
    let decoded = abcd_decompiler::decode_method(&code.instructions);
    let rest_param_idx = decoded.iter().find_map(|insn| {
        if insn.opcode.mnemonic() == "copyrestargs" {
            Some(insn.operands.first().map_or(0, |op| match op {
                abcd_ir::instruction::Operand::Imm(v) => *v as u32,
                _ => 0,
            }))
        } else {
            None
        }
    });

    // Generate parameter list: num_args includes funcObj, newTarget, this (3 implicit)
    let user_param_count = if code.num_args > 3 {
        code.num_args - 3
    } else {
        0
    };
    let user_params = (1..=user_param_count)
        .map(|i| {
            if rest_param_idx == Some(i - 1) {
                format!("...p{i}")
            } else {
                format!("p{i}")
            }
        })
        .collect::<Vec<_>>()
        .join(", ");

    output.push_str(&format!(
        "function {}({user_params}) {{\n",
        clean_method_name(&method.name)
    ));
    for line in js.lines() {
        output.push_str(&format!("    {line}\n"));
    }
    output.push_str("}\n\n");
}

/// Parse ABC internal method names into readable names.
///
/// ABC method name patterns:
/// - `func_main_0` → module initializer
/// - `#~@0=#ClassName` → constructor
/// - `#~@0>#methodName` → instance method
/// - `#~@0>@1*#` → anonymous function (numbered)
/// - `#*#` → anonymous function
/// - `#*#^1` → anonymous function variant
fn clean_method_name(name: &str) -> String {
    // Constructor: contains `=#Name`
    if let Some(pos) = name.rfind("=#") {
        let class_name = &name[pos + 2..];
        return format!("constructor_{class_name}");
    }

    // Instance method: contains `>#name` where name doesn't start with @
    if let Some(pos) = name.rfind(">#") {
        let rest = &name[pos + 2..];
        if !rest.starts_with('@') && !rest.is_empty() {
            let method_name = rest.trim_end_matches("()");
            return sanitize_js_ident(method_name);
        }
    }

    // Anonymous: `#*#` or `#*#^N` or contains `>@N*#`
    if name == "#*#" {
        return "anonymous".to_string();
    }
    if let Some(rest) = name.strip_prefix("#*#^") {
        return format!("anonymous_{}", sanitize_js_ident(rest));
    }

    // Numbered anonymous: `>@hex*#` pattern
    if name.contains("*#") {
        // Extract the last @hex part
        if let Some(at_pos) = name.rfind('@') {
            let after_at = &name[at_pos + 1..];
            if let Some(star_pos) = after_at.find("*#") {
                let id = sanitize_js_ident(&after_at[..star_pos]);
                let suffix = &after_at[star_pos + 2..];
                if suffix.is_empty() {
                    return format!("anonymous_0x{id}");
                } else {
                    return format!("anonymous_0x{}_{}", id, sanitize_js_ident(suffix));
                }
            }
        }
    }

    // Keep as-is for func_main_0 and other recognizable names
    // Final cleanup: strip remaining prefixes and sanitize
    let cleaned = name
        .strip_prefix("#%#")
        .or_else(|| name.strip_prefix("#"))
        .unwrap_or(name);
    sanitize_js_ident(cleaned)
}

fn sanitize_js_ident(s: &str) -> String {
    s.chars()
        .map(|c| {
            if c.is_alphanumeric() || c == '_' || c == '$' {
                c
            } else {
                '_'
            }
        })
        .collect()
}

fn sanitize_filename(name: &str) -> String {
    name.replace(['\\', ':', '*', '?', '"', '<', '>', '|'], "_")
        .replace("..", "_")
        .trim_matches('_')
        .to_string()
}

/// Convert a class name like `Lcom.huawei.hmos.photos/phone_photos/ets/Application/AbilityStage;`
/// into a relative path like `com.huawei.hmos.photos/phone_photos/ets/Application/AbilityStage.js`.
fn class_name_to_path(name: &str) -> PathBuf {
    let stripped = name
        .strip_prefix('L')
        .unwrap_or(name)
        .strip_suffix(';')
        .unwrap_or(name.strip_prefix('L').unwrap_or(name));

    let parts: Vec<&str> = stripped.split('/').collect();
    if parts.len() <= 1 {
        PathBuf::from(format!("{}.js", sanitize_filename(stripped)))
    } else {
        let mut path = PathBuf::new();
        for &dir in &parts[..parts.len() - 1] {
            path.push(sanitize_filename(dir));
        }
        path.push(format!("{}.js", sanitize_filename(parts[parts.len() - 1])));
        path
    }
}
