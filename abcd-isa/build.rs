use serde::Deserialize;
use std::collections::HashMap;
use std::env;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::path::PathBuf;

#[derive(Debug, Deserialize)]
struct IsaYaml {
    #[serde(default)]
    prefixes: Vec<PrefixDef>,
    groups: Vec<GroupDef>,
}

#[derive(Debug, Deserialize)]
struct PrefixDef {
    name: String,
    opcode_idx: u8,
}

#[derive(Debug, Deserialize)]
struct GroupDef {
    title: String,
    #[serde(default)]
    properties: Vec<String>,
    instructions: Vec<InstructionDef>,
}

#[derive(Debug, Deserialize)]
struct InstructionDef {
    sig: String,
    #[serde(default = "default_acc")]
    acc: String,
    opcode_idx: Vec<serde_yaml::Value>,
    format: Vec<String>,
    #[serde(default)]
    prefix: Option<String>,
    #[serde(default)]
    properties: Vec<String>,
}

fn default_acc() -> String {
    "none".to_string()
}

/// A fully resolved instruction variant (one per opcode_idx/format pair).
struct ResolvedInsn {
    mnemonic: String,
    rust_name: String,
    opcode_value: u16,
    format_name: String,
    is_prefixed: bool,
    acc_read: bool,
    acc_write: bool,
    properties: Vec<String>,
    operand_parts: Vec<OperandPart>,
}

struct OperandPart {
    name: String,
    kind: &'static str, // "Reg", "Imm", "Id"
    bit_width: usize,
    byte_offset: usize,
    /// For 4-bit operands packed in a byte: 0 = low nibble, 4 = high nibble.
    bit_offset_in_byte: usize,
    is_jump: bool,
    is_float: bool,
}

fn main() {
    let isa_path = env::var("ABC_ISA_YAML").unwrap_or_else(|_| {
        let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
        let p = PathBuf::from(&manifest_dir)
            .join("../..")
            .join("arkcompiler/runtime_core/isa/isa.yaml");
        if p.exists() {
            return p.to_string_lossy().to_string();
        }
        PathBuf::from(&manifest_dir)
            .join("../../arkcompiler/runtime_core/isa/isa.yaml")
            .to_string_lossy()
            .to_string()
    });

    println!("cargo:rerun-if-changed={isa_path}");
    println!("cargo:rerun-if-env-changed=ABC_ISA_YAML");

    let yaml_content = fs::read_to_string(&isa_path)
        .unwrap_or_else(|e| panic!("Failed to read ISA YAML at {isa_path}: {e}"));

    let isa: IsaYaml = serde_yaml::from_str(&yaml_content).expect("Failed to parse ISA YAML");

    let prefix_map: HashMap<String, u8> = isa
        .prefixes
        .iter()
        .map(|p| (p.name.clone(), p.opcode_idx))
        .collect();

    let mut resolved = Vec::new();

    for group in &isa.groups {
        for insn in &group.instructions {
            let mnemonic = insn.sig.split_whitespace().next().unwrap().to_string();

            // Merge group-level and instruction-level properties
            let mut props = group.properties.clone();
            props.extend(insn.properties.clone());

            let (acc_read, acc_write) = parse_acc(&insn.acc);

            // Determine if this is a jump instruction from the signature
            let is_jump_insn = props.contains(&"jump".to_string())
                || mnemonic.starts_with('j')
                || mnemonic == "jmp";

            // Determine if this is a float immediate instruction
            let is_float_insn = mnemonic == "fldai";

            for (i, fmt_name) in insn.format.iter().enumerate() {
                let raw_opcode = parse_opcode_value(&insn.opcode_idx[i]);
                let is_prefixed = insn.prefix.is_some() || fmt_name.starts_with("pref_");

                let opcode_value = if is_prefixed {
                    let prefix_byte = insn
                        .prefix
                        .as_ref()
                        .map(|p| *prefix_map.get(p).unwrap_or(&0))
                        .unwrap_or(0);
                    ((prefix_byte as u16) << 8) | (raw_opcode as u16)
                } else {
                    raw_opcode as u16
                };

                let rust_name = make_rust_name(&mnemonic, fmt_name);
                let operand_parts = parse_format(fmt_name, is_jump_insn, is_float_insn);

                resolved.push(ResolvedInsn {
                    mnemonic: mnemonic.clone(),
                    rust_name,
                    opcode_value,
                    format_name: fmt_name.clone(),
                    is_prefixed,
                    acc_read,
                    acc_write,
                    properties: props.clone(),
                    operand_parts,
                });
            }
        }
    }

    // Sort by opcode value for deterministic output
    resolved.sort_by_key(|r| r.opcode_value);

    let out_dir = env::var("OUT_DIR").unwrap();
    let out_path = PathBuf::from(&out_dir).join("generated.rs");

    let mut code = String::with_capacity(64 * 1024);

    generate_opcode_enum(&resolved, &mut code);
    generate_format_enum(&resolved, &mut code);
    generate_opcode_flags(&mut code);
    generate_operand_types(&mut code);
    generate_opcode_info(&resolved, &mut code);
    generate_opcode_table(&resolved, &mut code);
    generate_decode_function(&resolved, &prefix_map, &mut code);

    fs::write(&out_path, &code).expect("Failed to write generated code");
}

fn parse_opcode_value(val: &serde_yaml::Value) -> u8 {
    match val {
        serde_yaml::Value::Number(n) => n.as_u64().unwrap() as u8,
        _ => panic!("Unexpected opcode_idx value: {val:?}"),
    }
}

fn parse_acc(acc: &str) -> (bool, bool) {
    if acc == "none" {
        return (false, false);
    }
    let read = acc.contains("in:") || acc.contains("inout:");
    let write = acc.contains("out:") || acc.contains("inout:");
    (read, write)
}

fn make_rust_name(mnemonic: &str, format: &str) -> String {
    // Convert mnemonic like "deprecated.ldlexenv" to "DeprecatedLdlexenv"
    // and append format suffix for disambiguation
    let base: String = mnemonic
        .split('.')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect();

    // Check if format provides disambiguation (multiple formats for same mnemonic)
    let fmt_suffix = format_suffix(format);
    if fmt_suffix.is_empty() {
        base
    } else {
        format!("{base}{fmt_suffix}")
    }
}

fn format_suffix(format: &str) -> String {
    // Extract a short suffix from format name for disambiguation
    // e.g., "op_imm_8" -> "Imm8", "op_v1_4_v2_4" -> "V4V4"
    let stripped = format
        .strip_prefix("pref_op_")
        .or_else(|| format.strip_prefix("op_"))
        .unwrap_or(format);

    if stripped == "none" {
        return String::new();
    }

    // Parse format parts
    let parts: Vec<&str> = stripped.split('_').collect();
    let mut suffix = String::new();
    let mut i = 0;
    while i < parts.len() {
        let part = parts[i];
        if part.starts_with('v') || part == "imm" || part == "id" {
            let name = match part {
                p if p.starts_with('v') => "V",
                p if p.starts_with("imm") => "Imm",
                p if p.starts_with("id") => "Id",
                _ => part,
            };
            if i + 1 < parts.len() {
                if let Ok(_) = parts[i + 1].parse::<usize>() {
                    write!(suffix, "{name}{}", parts[i + 1]).unwrap();
                    i += 2;
                    continue;
                }
            }
            suffix.push_str(name);
        }
        i += 1;
    }
    suffix
}

/// Parse a format name into operand parts with byte offsets.
fn parse_format(format: &str, is_jump: bool, is_float: bool) -> Vec<OperandPart> {
    let is_prefixed = format.starts_with("pref_");
    let stripped = format
        .strip_prefix("pref_op_")
        .or_else(|| format.strip_prefix("op_"))
        .unwrap_or(format);

    if stripped == "none" {
        return Vec::new();
    }

    let opcode_bytes = if is_prefixed { 2 } else { 1 };
    let mut parts = Vec::new();
    let tokens: Vec<&str> = stripped.split('_').collect();
    let mut bit_offset = 0usize; // bits after opcode

    let mut i = 0;
    while i < tokens.len() {
        let token = tokens[i];

        // Determine operand kind
        let (kind, name) = if token.starts_with('v') {
            ("Reg", token.to_string())
        } else if token.starts_with("imm") {
            ("Imm", token.to_string())
        } else if token.starts_with("id") {
            ("Id", token.to_string())
        } else if let Ok(_) = token.parse::<usize>() {
            // This is a bit width for the previous token - skip
            i += 1;
            continue;
        } else {
            i += 1;
            continue;
        };

        // Next token should be the bit width
        let bit_width = if i + 1 < tokens.len() {
            if let Ok(w) = tokens[i + 1].parse::<usize>() {
                i += 2;
                w
            } else {
                i += 1;
                8 // default
            }
        } else {
            i += 1;
            8
        };

        let byte_offset = opcode_bytes + bit_offset / 8;
        let bit_offset_in_byte = bit_offset % 8;

        parts.push(OperandPart {
            name,
            kind,
            bit_width,
            byte_offset,
            bit_offset_in_byte,
            is_jump: is_jump && kind == "Imm",
            is_float: is_float && kind == "Imm",
        });

        bit_offset += bit_width;
    }

    parts
}

fn compute_format_size(format: &str) -> usize {
    let is_prefixed = format.starts_with("pref_");
    let stripped = format
        .strip_prefix("pref_op_")
        .or_else(|| format.strip_prefix("op_"))
        .unwrap_or(format);

    let opcode_bytes = if is_prefixed { 2 } else { 1 };

    if stripped == "none" {
        return opcode_bytes;
    }

    // Sum up all bit widths from the format name
    let tokens: Vec<&str> = stripped.split('_').collect();
    let mut total_bits = 0;
    for token in &tokens {
        if let Ok(bits) = token.parse::<usize>() {
            total_bits += bits;
        }
    }

    opcode_bytes + (total_bits + 7) / 8
}

fn generate_opcode_enum(resolved: &[ResolvedInsn], code: &mut String) {
    writeln!(code, "/// All opcodes in the ArkCompiler ISA.").unwrap();
    writeln!(code, "///").unwrap();
    writeln!(code, "/// Non-prefixed opcodes fit in a u8.").unwrap();
    writeln!(
        code,
        "/// Prefixed opcodes are encoded as (prefix_byte << 8) | sub_opcode."
    )
    .unwrap();
    writeln!(code, "#[allow(non_camel_case_types)]").unwrap();
    writeln!(code, "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]").unwrap();
    writeln!(code, "#[repr(u16)]").unwrap();
    writeln!(code, "pub enum Opcode {{").unwrap();

    // Track used names to avoid duplicates
    let mut used_names: HashMap<String, usize> = HashMap::new();

    for insn in resolved {
        let name = &insn.rust_name;
        let count = used_names.entry(name.clone()).or_insert(0);
        let final_name = if *count > 0 {
            format!("{name}_{count}")
        } else {
            name.clone()
        };
        *used_names.get_mut(name).unwrap() += 1;

        writeln!(
            code,
            "    /// `{mnemonic}` (format: {fmt})",
            mnemonic = insn.mnemonic,
            fmt = insn.format_name
        )
        .unwrap();
        writeln!(code, "    {final_name} = {:#06x},", insn.opcode_value).unwrap();
    }

    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();

    // Implement Display - use a match instead of table lookup
    writeln!(code, "impl Opcode {{").unwrap();
    writeln!(code, "    /// Get the mnemonic string for this opcode.").unwrap();
    writeln!(code, "    pub fn mnemonic(self) -> &'static str {{").unwrap();
    writeln!(code, "        match self {{").unwrap();

    let mut used_names2: HashMap<String, usize> = HashMap::new();
    for insn in resolved {
        let name = &insn.rust_name;
        let count = used_names2.entry(name.clone()).or_insert(0);
        let final_name = if *count > 0 {
            format!("{name}_{count}")
        } else {
            name.clone()
        };
        *used_names2.get_mut(name).unwrap() += 1;
        writeln!(
            code,
            "            Opcode::{final_name} => \"{mnemonic}\",",
            mnemonic = insn.mnemonic
        )
        .unwrap();
    }

    writeln!(code, "        }}").unwrap();
    writeln!(code, "    }}").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();

    writeln!(code, "impl core::fmt::Display for Opcode {{").unwrap();
    writeln!(
        code,
        "    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {{"
    )
    .unwrap();
    writeln!(code, "        f.write_str(self.mnemonic())").unwrap();
    writeln!(code, "    }}").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn generate_format_enum(_resolved: &[ResolvedInsn], code: &mut String) {
    writeln!(code, "/// Instruction format determining operand layout.").unwrap();
    writeln!(code, "#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]").unwrap();
    writeln!(code, "pub enum Format {{").unwrap();

    // Collect unique formats
    let mut formats: Vec<String> = _resolved
        .iter()
        .map(|r| r.format_name.clone())
        .collect::<std::collections::HashSet<_>>()
        .into_iter()
        .collect();
    formats.sort();

    for fmt in &formats {
        let rust_fmt = format_to_rust_variant(fmt);
        let size = compute_format_size(fmt);
        writeln!(code, "    /// `{fmt}` ({size} bytes)").unwrap();
        writeln!(code, "    {rust_fmt},").unwrap();
    }

    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();

    writeln!(code, "impl Format {{").unwrap();
    writeln!(
        code,
        "    /// Total instruction size in bytes (including opcode)."
    )
    .unwrap();
    writeln!(code, "    pub fn size(self) -> usize {{").unwrap();
    writeln!(code, "        match self {{").unwrap();
    for fmt in &formats {
        let rust_fmt = format_to_rust_variant(fmt);
        let size = compute_format_size(fmt);
        writeln!(code, "            Format::{rust_fmt} => {size},").unwrap();
    }
    writeln!(code, "        }}").unwrap();
    writeln!(code, "    }}").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn format_to_rust_variant(fmt: &str) -> String {
    // Convert "op_imm_8_v_8" to "OpImm8V8"
    // Convert "pref_op_none" to "PrefOpNone"
    fmt.split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(c) => c.to_uppercase().to_string() + chars.as_str(),
                None => String::new(),
            }
        })
        .collect()
}

fn generate_opcode_flags(code: &mut String) {
    writeln!(code, "bitflags::bitflags! {{").unwrap();
    writeln!(code, "    /// Instruction property flags.").unwrap();
    writeln!(code, "    #[derive(Debug, Clone, Copy, PartialEq, Eq)]").unwrap();
    writeln!(code, "    pub struct OpcodeFlags: u32 {{").unwrap();
    writeln!(code, "        const JUMP = 1 << 0;").unwrap();
    writeln!(code, "        const CONDITIONAL = 1 << 1;").unwrap();
    writeln!(code, "        const CALL = 1 << 2;").unwrap();
    writeln!(code, "        const RETURN = 1 << 3;").unwrap();
    writeln!(code, "        const THROW = 1 << 4;").unwrap();
    writeln!(code, "        const SUSPEND = 1 << 5;").unwrap();
    writeln!(code, "        const FLOAT = 1 << 6;").unwrap();
    writeln!(code, "        const DYNAMIC = 1 << 7;").unwrap();
    writeln!(code, "        const STRING_ID = 1 << 8;").unwrap();
    writeln!(code, "        const METHOD_ID = 1 << 9;").unwrap();
    writeln!(code, "        const LITERALARRAY_ID = 1 << 10;").unwrap();
    writeln!(code, "        const TYPE_ID = 1 << 11;").unwrap();
    writeln!(code, "        const FIELD_ID = 1 << 12;").unwrap();
    writeln!(code, "        const IC_SLOT = 1 << 13;").unwrap();
    writeln!(code, "        const NO_SIDE_EFFECT = 1 << 14;").unwrap();
    writeln!(code, "        const ACC_READ = 1 << 15;").unwrap();
    writeln!(code, "        const ACC_WRITE = 1 << 16;").unwrap();
    writeln!(code, "    }}").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn props_to_flags(insn: &ResolvedInsn) -> String {
    let mut flags = Vec::new();
    let props = &insn.properties;

    if props.contains(&"jump".to_string()) || insn.mnemonic.starts_with('j') {
        flags.push("OpcodeFlags::JUMP");
    }
    if props.contains(&"conditional".to_string()) {
        flags.push("OpcodeFlags::CONDITIONAL");
    }
    if props.contains(&"call".to_string()) || props.contains(&"call_virt".to_string()) {
        flags.push("OpcodeFlags::CALL");
    }
    if props.contains(&"return".to_string()) || insn.mnemonic.starts_with("return") {
        flags.push("OpcodeFlags::RETURN");
    }
    if insn.mnemonic.starts_with("throw") {
        flags.push("OpcodeFlags::THROW");
    }
    if props.contains(&"suspend".to_string()) {
        flags.push("OpcodeFlags::SUSPEND");
    }
    if props.contains(&"float".to_string()) {
        flags.push("OpcodeFlags::FLOAT");
    }
    if props.contains(&"dynamic".to_string()) || props.contains(&"maybe_dynamic".to_string()) {
        flags.push("OpcodeFlags::DYNAMIC");
    }
    if props.contains(&"string_id".to_string()) {
        flags.push("OpcodeFlags::STRING_ID");
    }
    if props.contains(&"method_id".to_string()) {
        flags.push("OpcodeFlags::METHOD_ID");
    }
    if props.contains(&"literalarray_id".to_string()) {
        flags.push("OpcodeFlags::LITERALARRAY_ID");
    }
    if props.contains(&"type_id".to_string()) {
        flags.push("OpcodeFlags::TYPE_ID");
    }
    if props.contains(&"field_id".to_string()) {
        flags.push("OpcodeFlags::FIELD_ID");
    }
    if props.contains(&"ic_slot".to_string()) || props.contains(&"jit_ic_slot".to_string()) {
        flags.push("OpcodeFlags::IC_SLOT");
    }
    if props.contains(&"no_side_effect".to_string()) {
        flags.push("OpcodeFlags::NO_SIDE_EFFECT");
    }
    if insn.acc_read {
        flags.push("OpcodeFlags::ACC_READ");
    }
    if insn.acc_write {
        flags.push("OpcodeFlags::ACC_WRITE");
    }

    if flags.is_empty() {
        "OpcodeFlags::empty()".to_string()
    } else {
        flags.join(".union(") + &")".repeat(flags.len() - 1)
    }
}

fn generate_operand_types(code: &mut String) {
    writeln!(code, "/// Kind of operand in an instruction format.").unwrap();
    writeln!(code, "#[derive(Debug, Clone, Copy, PartialEq, Eq)]").unwrap();
    writeln!(code, "pub enum OperandKind {{").unwrap();
    writeln!(code, "    /// Virtual register.").unwrap();
    writeln!(code, "    Reg,").unwrap();
    writeln!(code, "    /// Immediate value.").unwrap();
    writeln!(code, "    Imm,").unwrap();
    writeln!(
        code,
        "    /// Entity ID (string, method, literalarray, etc.)."
    )
    .unwrap();
    writeln!(code, "    Id,").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();

    writeln!(
        code,
        "/// Description of a single operand within an instruction."
    )
    .unwrap();
    writeln!(code, "#[derive(Debug, Clone, Copy)]").unwrap();
    writeln!(code, "pub struct OperandDesc {{").unwrap();
    writeln!(code, "    pub kind: OperandKind,").unwrap();
    writeln!(code, "    pub bit_width: usize,").unwrap();
    writeln!(code, "    pub byte_offset: usize,").unwrap();
    writeln!(
        code,
        "    /// For sub-byte operands: bit offset within the byte (0 or 4 for nibbles)."
    )
    .unwrap();
    writeln!(code, "    pub bit_offset_in_byte: usize,").unwrap();
    writeln!(code, "    pub is_jump: bool,").unwrap();
    writeln!(code, "    pub is_float: bool,").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn generate_opcode_info(_resolved: &[ResolvedInsn], code: &mut String) {
    writeln!(code, "/// Metadata for a single opcode.").unwrap();
    writeln!(code, "#[derive(Debug, Clone)]").unwrap();
    writeln!(code, "pub struct OpcodeInfo {{").unwrap();
    writeln!(code, "    pub mnemonic: &'static str,").unwrap();
    writeln!(code, "    pub format: Format,").unwrap();
    writeln!(code, "    pub flags: OpcodeFlags,").unwrap();
    writeln!(code, "    pub is_prefixed: bool,").unwrap();
    writeln!(code, "    pub operand_parts: &'static [OperandDesc],").unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn generate_opcode_table(resolved: &[ResolvedInsn], code: &mut String) {
    // Generate static operand descriptor arrays
    for (i, insn) in resolved.iter().enumerate() {
        if insn.operand_parts.is_empty() {
            continue;
        }
        writeln!(code, "static OPERANDS_{i}: &[OperandDesc] = &[").unwrap();
        for part in &insn.operand_parts {
            writeln!(
                code,
                "    OperandDesc {{ kind: OperandKind::{kind}, bit_width: {bw}, byte_offset: {bo}, bit_offset_in_byte: {bib}, is_jump: {ij}, is_float: {if_} }},",
                kind = part.kind,
                bw = part.bit_width,
                bo = part.byte_offset,
                bib = part.bit_offset_in_byte,
                ij = part.is_jump,
                if_ = part.is_float,
            )
            .unwrap();
        }
        writeln!(code, "];").unwrap();
    }
    writeln!(code).unwrap();

    // Generate the lookup table indexed by opcode value
    // We use a HashMap-style approach since opcodes are sparse
    writeln!(
        code,
        "/// Lookup table: maps opcode u16 value to OpcodeInfo."
    )
    .unwrap();
    writeln!(code, "pub static OPCODE_TABLE: &[(u16, OpcodeInfo)] = &[").unwrap();

    for (i, insn) in resolved.iter().enumerate() {
        let flags = props_to_flags(insn);
        let fmt = format_to_rust_variant(&insn.format_name);
        let operands = if insn.operand_parts.is_empty() {
            "&[]".to_string()
        } else {
            format!("OPERANDS_{i}")
        };

        writeln!(
            code,
            "    ({:#06x}, OpcodeInfo {{ mnemonic: \"{mnemonic}\", format: Format::{fmt}, flags: {flags}, is_prefixed: {pref}, operand_parts: {operands} }}),",
            insn.opcode_value,
            mnemonic = insn.mnemonic,
            pref = insn.is_prefixed,
        )
        .unwrap();
    }

    writeln!(code, "];").unwrap();
    writeln!(code).unwrap();

    // Generate a fast lookup function
    writeln!(code, "/// Find OpcodeInfo by opcode u16 value.").unwrap();
    writeln!(
        code,
        "pub fn lookup_opcode(value: u16) -> Option<&'static OpcodeInfo> {{"
    )
    .unwrap();
    writeln!(
        code,
        "    OPCODE_TABLE.iter().find(|(v, _)| *v == value).map(|(_, info)| info)"
    )
    .unwrap();
    writeln!(code, "}}").unwrap();
    writeln!(code).unwrap();
}

fn generate_decode_function(
    resolved: &[ResolvedInsn],
    prefix_map: &HashMap<String, u8>,
    code: &mut String,
) {
    let prefix_bytes: Vec<u8> = prefix_map.values().copied().collect();

    writeln!(code, "/// Decode an opcode from a byte stream.").unwrap();
    writeln!(code, "///").unwrap();
    writeln!(
        code,
        "/// Returns the Opcode enum variant and a reference to its OpcodeInfo."
    )
    .unwrap();
    writeln!(
        code,
        "pub fn decode_opcode(bytes: &[u8]) -> Option<(Opcode, &'static OpcodeInfo)> {{"
    )
    .unwrap();
    writeln!(code, "    if bytes.is_empty() {{ return None; }}").unwrap();
    writeln!(code, "    let first = bytes[0];").unwrap();
    writeln!(code).unwrap();

    // Check if first byte is a prefix
    writeln!(code, "    // Check for prefix bytes").unwrap();
    writeln!(code, "    let opcode_value: u16 = match first {{").unwrap();
    for (name, byte) in prefix_map {
        writeln!(code, "        {byte:#04x} => {{ // {name} prefix").unwrap();
        writeln!(code, "            if bytes.len() < 2 {{ return None; }}").unwrap();
        writeln!(
            code,
            "            ({byte:#04x}u16 << 8) | (bytes[1] as u16)"
        )
        .unwrap();
        writeln!(code, "        }}").unwrap();
    }
    writeln!(code, "        _ => first as u16,").unwrap();
    writeln!(code, "    }};").unwrap();
    writeln!(code).unwrap();

    // Look up in table
    writeln!(code, "    let info = lookup_opcode(opcode_value)?;").unwrap();
    writeln!(code).unwrap();

    // Convert to Opcode enum
    writeln!(code, "    // SAFETY: opcode_value matches a known entry").unwrap();
    writeln!(
        code,
        "    let opcode = unsafe {{ core::mem::transmute::<u16, Opcode>(opcode_value) }};"
    )
    .unwrap();
    writeln!(code, "    Some((opcode, info))").unwrap();
    writeln!(code, "}}").unwrap();
}
