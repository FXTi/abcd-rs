use abcd_file::EntityId;
use clap::{Parser, Subcommand};
use std::fs;
use std::path::PathBuf;

#[cfg(not(target_env = "msvc"))]
#[global_allocator]
static GLOBAL: tikv_jemallocator::Jemalloc = tikv_jemallocator::Jemalloc;

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

// === StringResolver implementation for File ===

struct AbcResolver<'a> {
    abc: &'a abcd_file::File,
}

impl<'a> abcd_decompiler::expr_recovery::StringResolver for AbcResolver<'a> {
    fn resolve_string(&self, method_off: EntityId, entity_id: EntityId) -> Option<String> {
        let off = self
            .abc
            .resolve_offset_by_index(method_off, entity_id.0 as u16)?;
        self.abc.get_string(off).ok()
    }

    fn resolve_offset(&self, method_off: EntityId, entity_id: EntityId) -> Option<EntityId> {
        self.abc
            .resolve_offset_by_index(method_off, entity_id.0 as u16)
    }

    fn resolve_literal_array(
        &self,
        method_off: EntityId,
        entity_id: EntityId,
    ) -> Option<abcd_file::literal::LiteralArray> {
        let off = self
            .abc
            .resolve_offset_by_index(method_off, entity_id.0 as u16)?;
        let literal = self
            .abc
            .literal(EntityId(self.abc.literal_array_idx_off()))
            .ok()?;
        let vals = literal.enumerate_vals(off);
        let entries = vals
            .iter()
            .map(|v| {
                let tag = v.tag.unwrap_or(abcd_file::literal::LiteralTag::TagValue);
                let value = v.to_value();
                (tag, value)
            })
            .collect();
        Some(abcd_file::literal::LiteralArray { entries })
    }

    fn get_string_at_offset(&self, offset: EntityId) -> Option<String> {
        self.abc.get_string(offset).ok()
    }

    fn resolve_method_name(&self, method_off: EntityId, entity_id: EntityId) -> Option<String> {
        let off = self
            .abc
            .resolve_offset_by_index(method_off, entity_id.0 as u16)?;
        let method = self.abc.method(off).ok()?;
        let name = self.abc.get_string(method.name_off()).ok()?;
        if name.is_empty() { None } else { Some(name) }
    }
}

fn cmd_info(path: &PathBuf) {
    let abc = match abcd_file::File::open_path(path.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let ver = abc.version();
    let checksum = abc.checksum();
    let foreign_off = abc.foreign_off();
    let foreign_size = abc.foreign_size();
    let num_lnps = abc.num_lnps();

    println!("=== ABC File Info ===");
    println!("Version:          {ver}",);
    println!("File size:        {} bytes", abc.file_size());
    println!("Checksum:         {checksum:#010x}");
    println!("Classes:          {}", abc.num_classes());
    println!("Literal arrays:   {}", abc.num_literal_arrays());
    println!("Line num progs:   {num_lnps}");
    println!("Index regions:    {}", abc.num_index_headers());
    println!(
        "Foreign region:   {foreign_off:#x}..{:#x}",
        foreign_off + foreign_size
    );
}

fn cmd_disasm(path: &PathBuf) {
    let abc = match abcd_file::File::open_path(path.as_path()) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("Error: {e}");
            std::process::exit(1);
        }
    };

    let ver = abc.version();
    println!("# ABC Disassembly");
    println!("# Version: {ver}",);
    println!(
        "# Classes: {}, Literal arrays: {}",
        abc.num_classes(),
        abc.num_literal_arrays()
    );
    println!();

    for class_off in abc.class_offsets() {
        if abc.is_external(class_off) {
            continue;
        }

        let class = match abc.class(class_off) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("# Error parsing class at {class_off}: {e}");
                continue;
            }
        };

        let class_name = abc
            .get_string(class_off)
            .unwrap_or_else(|_| format!("<{class_off}>"));
        let source_file = class
            .source_file_off()
            .and_then(|off| abc.get_string(off).ok());

        println!("# ============================================");
        println!("# Class: {class_name}");
        if let Some(ref sf) = source_file {
            println!("# Source: {sf}");
        }
        println!(
            "# Methods: {}, Fields: {}",
            class.num_methods(),
            class.num_fields()
        );
        println!();

        for method_off in class.method_offsets() {
            disasm_method(&abc, method_off);
        }
    }
}

fn disasm_method(abc: &abcd_file::File, method_off: EntityId) {
    let method = match abc.method(method_off) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("# Error parsing method at {method_off}: {e}");
            return;
        }
    };

    let method_name = abc
        .get_string(method.name_off())
        .unwrap_or_else(|_| format!("<{method_off}>"));
    println!(".function {method_name} {{");

    let Some(code_off) = method.code_off() else {
        println!("    # (no code - native or abstract)");
        println!("}}");
        println!();
        return;
    };

    let code = match abc.code(code_off) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("    # Error parsing code at {code_off}: {e}");
            println!("}}");
            println!();
            return;
        }
    };

    let instructions = code.instructions();
    println!(
        "    # vregs: {}, args: {}, code_size: {}",
        code.num_vregs(),
        code.num_args(),
        instructions.len()
    );

    let decoded = abcd_decompiler::decode_method(instructions);
    for insn in &decoded {
        println!("    {:#06x}  {}", insn.offset, insn.opcode);
    }

    for tb in &code.try_blocks() {
        println!(
            "    # try [{:#x}..{:#x}]",
            tb.start_pc,
            tb.start_pc + tb.length
        );
        for cb in &tb.catches {
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

// === Module record helpers ===

struct RegularImport {
    local_name: String,
    import_name: String,
    module_request_idx: u32,
}
struct NamespaceImport {
    local_name: String,
    module_request_idx: u32,
}
struct LocalExport {
    local_name: String,
    export_name: String,
}
struct IndirectExport {
    export_name: String,
    import_name: String,
    module_request_idx: u32,
}
struct StarExport {
    module_request_idx: u32,
}

struct ResolvedModuleRecord {
    module_requests: Vec<String>,
    regular_imports: Vec<RegularImport>,
    namespace_imports: Vec<NamespaceImport>,
    local_exports: Vec<LocalExport>,
    indirect_exports: Vec<IndirectExport>,
    star_exports: Vec<StarExport>,
}

fn resolve_module_record(
    abc: &abcd_file::File,
    module: &abcd_file::module::Module,
) -> ResolvedModuleRecord {
    let module_requests: Vec<String> = (0..module.num_requests())
        .map(|i| {
            module
                .request_off(i)
                .and_then(|off| abc.get_string(off).ok())
                .unwrap_or_default()
        })
        .collect();

    let records = module.records();
    let mut regular_imports = Vec::new();
    let mut namespace_imports = Vec::new();
    let mut local_exports = Vec::new();
    let mut indirect_exports = Vec::new();
    let mut star_exports = Vec::new();

    for r in &records {
        let s = |off: EntityId| abc.get_string(off).unwrap_or_default();
        match r.tag {
            abcd_file::ModuleTag::RegularImport => {
                regular_imports.push(RegularImport {
                    local_name: s(r.local_name_off),
                    import_name: s(r.import_name_off),
                    module_request_idx: r.module_request_idx,
                });
            }
            abcd_file::ModuleTag::NamespaceImport => {
                namespace_imports.push(NamespaceImport {
                    local_name: s(r.local_name_off),
                    module_request_idx: r.module_request_idx,
                });
            }
            abcd_file::ModuleTag::LocalExport => {
                local_exports.push(LocalExport {
                    local_name: s(r.local_name_off),
                    export_name: s(r.export_name_off),
                });
            }
            abcd_file::ModuleTag::IndirectExport => {
                indirect_exports.push(IndirectExport {
                    export_name: s(r.export_name_off),
                    import_name: s(r.import_name_off),
                    module_request_idx: r.module_request_idx,
                });
            }
            abcd_file::ModuleTag::StarExport => {
                star_exports.push(StarExport {
                    module_request_idx: r.module_request_idx,
                });
            }
            abcd_file::ModuleTag::Unknown(_) => {}
        }
    }

    ResolvedModuleRecord {
        module_requests,
        regular_imports,
        namespace_imports,
        local_exports,
        indirect_exports,
        star_exports,
    }
}

/// Try to find the "moduleRecordIdx" field value from a class.
fn find_module_record_offset(
    abc: &abcd_file::File,
    class: &abcd_file::class::Class,
) -> Option<EntityId> {
    for field_off in class.field_offsets() {
        let field = abc.field(field_off).ok()?;
        let name = abc.get_string(field.name_off()).ok()?;
        if name == "moduleRecordIdx" {
            return field.value_i32().map(|v| EntityId(v as u32));
        }
    }
    None
}

fn cmd_decompile(path: &PathBuf, output_dir: Option<&std::path::Path>) {
    let abc = match abcd_file::File::open_path(path.as_path()) {
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
        if abc.is_external(class_off) {
            continue;
        }

        let class = match abc.class(class_off) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("// Error parsing class at {class_off}: {e}");
                continue;
            }
        };

        let class_name = abc
            .get_string(class_off)
            .unwrap_or_else(|_| format!("<{class_off}>"));
        let source_file = class
            .source_file_off()
            .and_then(|off| abc.get_string(off).ok())
            .unwrap_or_else(|| class_name.clone());

        let mut class_output = String::new();

        // Try to parse module record from class fields
        let module_record = find_module_record_offset(&abc, &class)
            .and_then(|off| abc.module(off).ok())
            .map(|m| resolve_module_record(&abc, &m));

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

        for method_off in class.method_offsets() {
            decompile_method_to_string(&abc, &resolver, method_off, &mut class_output);
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
            for (i, imp) in mr.regular_imports.iter().enumerate() {
                let placeholder = format!("__module_{i}");
                class_output = class_output.replace(&placeholder, &imp.local_name);
            }
            let ns_offset = mr.regular_imports.len();
            for (i, imp) in mr.namespace_imports.iter().enumerate() {
                let placeholder = format!("__module_{}", ns_offset + i);
                class_output = class_output.replace(&placeholder, &imp.local_name);
            }
            for (i, exp) in mr.local_exports.iter().enumerate() {
                let placeholder = format!("__local_module_{i}");
                class_output = class_output.replace(&placeholder, &exp.local_name);
            }
            for (i, exp) in mr.local_exports.iter().enumerate() {
                let placeholder = format!("__export_{i}");
                class_output = class_output.replace(&placeholder, &exp.export_name);
            }
        }

        if let Some(dir) = output_dir {
            let rel_path = class_name_to_path(&source_file);
            let out_path = dir.join(&rel_path);
            if let Some(parent) = out_path.parent() {
                fs::create_dir_all(parent).unwrap_or_else(|e| {
                    eprintln!("Error creating directory {}: {e}", parent.display());
                });
            }
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
    abc: &abcd_file::File,
    resolver: &AbcResolver,
    method_off: EntityId,
    output: &mut String,
) {
    let method = match abc.method(method_off) {
        Ok(m) => m,
        Err(e) => {
            output.push_str(&format!("// Error parsing method at {method_off}: {e}\n"));
            return;
        }
    };

    let Some(code_off) = method.code_off() else {
        return; // Skip native/abstract methods
    };

    let code = match abc.code(code_off) {
        Ok(c) => c,
        Err(e) => {
            output.push_str(&format!("// Error parsing code at {code_off}: {e}\n"));
            return;
        }
    };

    let method_name = abc
        .get_string(method.name_off())
        .unwrap_or_else(|_| format!("<{method_off}>"));

    let instructions = code.instructions();

    // Convert try blocks to IR try blocks
    let try_blocks: Vec<abcd_ir::instruction::TryBlockInfo> = code
        .try_blocks()
        .iter()
        .map(|tb| abcd_ir::instruction::TryBlockInfo {
            start_pc: tb.start_pc,
            length: tb.length,
            catch_blocks: tb
                .catches
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
        instructions,
        &try_blocks,
        resolver,
        method_off,
        code.num_vregs(),
        code.num_args(),
    );

    // Detect rest parameters by scanning for copyrestargs instruction
    let decoded = abcd_decompiler::decode_method(instructions);
    let rest_param_idx = decoded.iter().find_map(|insn| {
        if insn.opcode.mnemonic() == "copyrestargs" {
            let (_, args, n) = insn.opcode.emit_args();
            Some(if n > 0 { args[0] as u32 } else { 0 })
        } else {
            None
        }
    });

    // Generate parameter list: num_args includes funcObj, newTarget, this (3 implicit)
    let user_param_count = if code.num_args() > 3 {
        code.num_args() - 3
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
        clean_method_name(&method_name)
    ));
    for line in js.lines() {
        output.push_str(&format!("    {line}\n"));
    }
    output.push_str("}\n\n");
}

/// Parse ABC internal method names into readable names.
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
