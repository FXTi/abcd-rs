//! Zero-`serde`, zero-recursion summary parser for OpenHarmony Stage
//! (`module.json`) and FA (`config.json`) module manifests.
//!
//! The scanner validates full RFC 8259 JSON syntax (plus an optional leading
//! UTF-8 BOM) using an explicit `Vec<Frame>` heap workstack (`O(1)` call stack,
//! zero panics), materializing only the keys and string values needed to
//! populate [`ManifestSummary`].

use std::borrow::Cow;

/// Summary metadata extracted from a Stage `module.json` or FA `config.json`
/// manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ManifestSummary {
    /// Logical module name (`module.name` in Stage `module.json`, or
    /// `module.distro.moduleName` in FA `config.json`).
    pub module_name: Option<String>,
    /// Module kind (`module.type` in Stage `module.json`, or
    /// `module.distro.moduleType` in FA `config.json`, such as `"entry"`,
    /// `"feature"`, `"shared"`, or `"har"`).
    pub module_type: Option<String>,
    /// `true` for a Stage-model `module.json` (`module` object without
    /// `module.distro`); `false` when `module.distro` (FA `config.json`) is
    /// present.
    pub is_stage_model: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObjRole {
    Root,
    Module,
    Distro,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FieldTarget {
    None,
    RootModule,
    ModuleName,
    ModuleType,
    ModuleDistro,
    DistroModuleName,
    DistroModuleType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ObjStep {
    Start,
    NeedKey,
    NeedValue(FieldTarget),
    AfterValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArrayStep {
    Start,
    NeedValue,
    AfterValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Frame {
    Object { role: ObjRole, step: ObjStep },
    Array { step: ArrayStep },
}

fn skip_ws(raw: &[u8], mut pos: usize) -> usize {
    while let Some(&b) = raw.get(pos) {
        if matches!(b, b' ' | b'\t' | b'\n' | b'\r') {
            pos += 1;
        } else {
            break;
        }
    }
    pos
}

fn classify_field(role: ObjRole, key: &str) -> FieldTarget {
    match (role, key) {
        (ObjRole::Root, "module") => FieldTarget::RootModule,
        (ObjRole::Module, "name") => FieldTarget::ModuleName,
        (ObjRole::Module, "type") => FieldTarget::ModuleType,
        (ObjRole::Module, "distro") => FieldTarget::ModuleDistro,
        (ObjRole::Distro, "moduleName") => FieldTarget::DistroModuleName,
        (ObjRole::Distro, "moduleType") => FieldTarget::DistroModuleType,
        _ => FieldTarget::None,
    }
}

fn parse_hex4(raw: &[u8], pos: &mut usize) -> Option<u16> {
    let end = pos.checked_add(4)?;
    let digits = raw.get(*pos..end)?;
    let mut val = 0u16;
    for &d in digits {
        let nibble = match d {
            b'0'..=b'9' => d - b'0',
            b'a'..=b'f' => d - b'a' + 10,
            b'A'..=b'F' => d - b'A' + 10,
            _ => return None,
        };
        val = (val << 4) | u16::from(nibble);
    }
    *pos = end;
    Some(val)
}

fn parse_string<'a>(text: &'a str, pos: &mut usize, need_value: bool) -> Option<Cow<'a, str>> {
    let raw = text.as_bytes();
    if raw.get(*pos) != Some(&b'"') {
        return None;
    }
    *pos += 1;
    let start = *pos;
    let mut run_start = start;
    let mut owned: Option<String> = None;

    while let Some(&b) = raw.get(*pos) {
        if b == b'"' {
            let end = *pos;
            *pos += 1;
            if !need_value {
                return Some(Cow::Borrowed(""));
            }
            return match owned {
                Some(mut buf) => {
                    buf.push_str(text.get(run_start..end)?);
                    Some(Cow::Owned(buf))
                }
                None => Some(Cow::Borrowed(text.get(start..end)?)),
            };
        }
        if b < 0x20 {
            return None;
        }
        if b == b'\\' {
            let esc_pos = *pos;
            if need_value {
                let prefix = text.get(run_start..esc_pos)?;
                match &mut owned {
                    Some(buf) => buf.push_str(prefix),
                    None => owned = Some(String::from(prefix)),
                }
            }
            *pos += 1;
            let esc = *raw.get(*pos)?;
            *pos += 1;
            let decoded = match esc {
                b'"' => '"',
                b'\\' => '\\',
                b'/' => '/',
                b'b' => '\u{0008}',
                b'f' => '\u{000C}',
                b'n' => '\n',
                b'r' => '\r',
                b't' => '\t',
                b'u' => {
                    let u1 = parse_hex4(raw, pos)?;
                    if (0xD800..=0xDBFF).contains(&u1) {
                        let pair_sig_end = pos.checked_add(2)?;
                        if raw.get(*pos..pair_sig_end) != Some(b"\\u") {
                            return None;
                        }
                        *pos = pair_sig_end;
                        let u2 = parse_hex4(raw, pos)?;
                        if !(0xDC00..=0xDFFF).contains(&u2) {
                            return None;
                        }
                        let cp =
                            0x10000 + (((u32::from(u1) - 0xD800) << 10) | (u32::from(u2) - 0xDC00));
                        char::from_u32(cp)?
                    } else if (0xDC00..=0xDFFF).contains(&u1) {
                        return None;
                    } else {
                        char::from_u32(u32::from(u1))?
                    }
                }
                _ => return None,
            };
            if let Some(buf) = &mut owned {
                buf.push(decoded);
            }
            run_start = *pos;
            continue;
        }
        *pos += 1;
    }
    None
}

fn parse_number(raw: &[u8], pos: &mut usize) -> Option<()> {
    let mut i = *pos;
    if raw.get(i) == Some(&b'-') {
        i += 1;
    }
    match raw.get(i)? {
        b'0' => {
            i += 1;
            if raw.get(i).is_some_and(u8::is_ascii_digit) {
                return None;
            }
        }
        b'1'..=b'9' => {
            i += 1;
            while raw.get(i).is_some_and(u8::is_ascii_digit) {
                i += 1;
            }
        }
        _ => return None,
    }
    if raw.get(i) == Some(&b'.') {
        i += 1;
        if !raw.get(i).is_some_and(u8::is_ascii_digit) {
            return None;
        }
        while raw.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
    }
    if matches!(raw.get(i), Some(b'e' | b'E')) {
        i += 1;
        if matches!(raw.get(i), Some(b'+' | b'-')) {
            i += 1;
        }
        if !raw.get(i).is_some_and(u8::is_ascii_digit) {
            return None;
        }
        while raw.get(i).is_some_and(u8::is_ascii_digit) {
            i += 1;
        }
    }
    *pos = i;
    Some(())
}

/// Parse [`ManifestSummary`] from raw Stage `module.json` or FA `config.json`
/// bytes without recursion or `serde`.
///
/// Handles an optional UTF-8 BOM (`\xEF\xBB\xBF`), full RFC 8259 string escapes
/// (including `\uXXXX` and UTF-16 surrogate pairs), and FA vs. Stage field
/// precedence:
///
/// - When `module.distro` is present as a JSON object (FA `config.json`),
///   `module.distro.{moduleName, moduleType}` take precedence over FA's
///   `AbilityPackage` `module.name`, and `is_stage_model` is `false`.
/// - Otherwise, when `module` is present as a JSON object without `distro`
///   (Stage `module.json`), `module.{name, type}` are extracted and
///   `is_stage_model` is `true`.
/// - Returns `None` on malformed JSON, non-UTF-8 bytes, or JSON documents
///   lacking a top-level `"module"` object.
pub fn parse_manifest_summary(bytes: &[u8]) -> Option<ManifestSummary> {
    let bytes = bytes.strip_prefix(&[0xEF, 0xBB, 0xBF]).unwrap_or(bytes);
    let text = std::str::from_utf8(bytes).ok()?;
    let raw = text.as_bytes();

    let mut pos = skip_ws(raw, 0);
    if raw.get(pos) != Some(&b'{') {
        return None;
    }
    pos += 1;

    let mut stack = Vec::with_capacity(8);
    stack.push(Frame::Object {
        role: ObjRole::Root,
        step: ObjStep::Start,
    });

    let mut saw_module_obj = false;
    let mut invalid_module_field = false;
    let mut saw_distro_obj = false;
    let mut stage_name: Option<String> = None;
    let mut stage_type: Option<String> = None;
    let mut distro_name: Option<String> = None;
    let mut distro_type: Option<String> = None;

    while !stack.is_empty() {
        pos = skip_ws(raw, pos);
        let b = *raw.get(pos)?;

        let target = match stack.last_mut()? {
            Frame::Object {
                role,
                step: step @ (ObjStep::Start | ObjStep::NeedKey),
            } => {
                if *step == ObjStep::Start && b == b'}' {
                    pos += 1;
                    stack.pop();
                    continue;
                }
                if b != b'"' {
                    return None;
                }
                let role_copy = *role;
                let need_key =
                    matches!(role_copy, ObjRole::Root | ObjRole::Module | ObjRole::Distro);
                let key = parse_string(text, &mut pos, need_key)?;
                let target = classify_field(role_copy, key.as_ref());
                pos = skip_ws(raw, pos);
                if raw.get(pos) != Some(&b':') {
                    return None;
                }
                pos += 1;
                if let Some(Frame::Object { step: s, .. }) = stack.last_mut() {
                    *s = ObjStep::NeedValue(target);
                }
                continue;
            }
            Frame::Object {
                step: step @ ObjStep::NeedValue(_),
                ..
            } => {
                let ObjStep::NeedValue(target) = *step else {
                    return None;
                };
                *step = ObjStep::AfterValue;
                target
            }
            Frame::Object {
                role,
                step: ObjStep::AfterValue,
            } => {
                if b == b'}' {
                    pos += 1;
                    stack.pop();
                } else if b == b',' {
                    pos += 1;
                    let role_copy = *role;
                    if let Some(top_frame) = stack.last_mut() {
                        *top_frame = Frame::Object {
                            role: role_copy,
                            step: ObjStep::NeedKey,
                        };
                    }
                } else {
                    return None;
                }
                continue;
            }
            Frame::Array {
                step: step @ ArrayStep::Start,
            } => {
                if b == b']' {
                    pos += 1;
                    stack.pop();
                    continue;
                }
                *step = ArrayStep::AfterValue;
                FieldTarget::None
            }
            Frame::Array {
                step: step @ ArrayStep::NeedValue,
            } => {
                *step = ArrayStep::AfterValue;
                FieldTarget::None
            }
            Frame::Array {
                step: step @ ArrayStep::AfterValue,
            } => {
                if b == b']' {
                    pos += 1;
                    stack.pop();
                } else if b == b',' {
                    pos += 1;
                    *step = ArrayStep::NeedValue;
                } else {
                    return None;
                }
                continue;
            }
        };

        match b {
            b'{' => {
                pos += 1;
                let child_role = match target {
                    FieldTarget::RootModule => {
                        saw_module_obj = true;
                        ObjRole::Module
                    }
                    FieldTarget::ModuleDistro => {
                        saw_distro_obj = true;
                        ObjRole::Distro
                    }
                    _ => ObjRole::Other,
                };
                stack.push(Frame::Object {
                    role: child_role,
                    step: ObjStep::Start,
                });
            }
            b'[' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                pos += 1;
                stack.push(Frame::Array {
                    step: ArrayStep::Start,
                });
            }
            b'"' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                let need_val = matches!(
                    target,
                    FieldTarget::ModuleName
                        | FieldTarget::ModuleType
                        | FieldTarget::DistroModuleName
                        | FieldTarget::DistroModuleType
                );
                let val = parse_string(text, &mut pos, need_val)?;
                let non_empty = if need_val && !val.is_empty() {
                    Some(val.into_owned())
                } else {
                    None
                };
                match target {
                    FieldTarget::ModuleName => stage_name = non_empty,
                    FieldTarget::ModuleType => stage_type = non_empty,
                    FieldTarget::DistroModuleName => distro_name = non_empty,
                    FieldTarget::DistroModuleType => distro_type = non_empty,
                    _ => {}
                }
            }
            b't' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                let end = pos.checked_add(4)?;
                if raw.get(pos..end) != Some(b"true") {
                    return None;
                }
                pos = end;
            }
            b'f' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                let end = pos.checked_add(5)?;
                if raw.get(pos..end) != Some(b"false") {
                    return None;
                }
                pos = end;
            }
            b'n' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                let end = pos.checked_add(4)?;
                if raw.get(pos..end) != Some(b"null") {
                    return None;
                }
                pos = end;
            }
            b'-' | b'0'..=b'9' => {
                if target == FieldTarget::RootModule {
                    invalid_module_field = true;
                }
                parse_number(raw, &mut pos)?;
            }
            _ => return None,
        }
    }

    pos = skip_ws(raw, pos);
    if pos != raw.len() || !saw_module_obj || invalid_module_field {
        return None;
    }

    if saw_distro_obj {
        Some(ManifestSummary {
            module_name: distro_name,
            module_type: distro_type,
            is_stage_model: false,
        })
    } else {
        Some(ManifestSummary {
            module_name: stage_name,
            module_type: stage_type,
            is_stage_model: true,
        })
    }
}
