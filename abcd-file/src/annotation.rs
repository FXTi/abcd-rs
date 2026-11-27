#![forbid(unsafe_code)]

use std::fmt;

use abcd_file_sys as sys;

use crate::model::Annotation;

/// Annotation element with resolved name.
pub struct AnnotationElem {
    pub name: crate::StringId,
    pub value: AnnotationValue,
}

/// MethodHandle operation type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum MethodHandleType {
    PutStatic = sys::MethodHandleType_PUT_STATIC,
    GetStatic = sys::MethodHandleType_GET_STATIC,
    PutInstance = sys::MethodHandleType_PUT_INSTANCE,
    GetInstance = sys::MethodHandleType_GET_INSTANCE,
    InvokeStatic = sys::MethodHandleType_INVOKE_STATIC,
    InvokeInstance = sys::MethodHandleType_INVOKE_INSTANCE,
    InvokeConstructor = sys::MethodHandleType_INVOKE_CONSTRUCTOR,
    InvokeDirect = sys::MethodHandleType_INVOKE_DIRECT,
    InvokeInterface = sys::MethodHandleType_INVOKE_INTERFACE,
}

impl MethodHandleType {
    /// Convert a raw byte to a `MethodHandleType`.
    pub fn from_u8(v: u8) -> Option<Self> {
        match v {
            x if x == sys::MethodHandleType_PUT_STATIC => Some(Self::PutStatic),
            x if x == sys::MethodHandleType_GET_STATIC => Some(Self::GetStatic),
            x if x == sys::MethodHandleType_PUT_INSTANCE => Some(Self::PutInstance),
            x if x == sys::MethodHandleType_GET_INSTANCE => Some(Self::GetInstance),
            x if x == sys::MethodHandleType_INVOKE_STATIC => Some(Self::InvokeStatic),
            x if x == sys::MethodHandleType_INVOKE_INSTANCE => Some(Self::InvokeInstance),
            x if x == sys::MethodHandleType_INVOKE_CONSTRUCTOR => Some(Self::InvokeConstructor),
            x if x == sys::MethodHandleType_INVOKE_DIRECT => Some(Self::InvokeDirect),
            x if x == sys::MethodHandleType_INVOKE_INTERFACE => Some(Self::InvokeInterface),
            _ => None,
        }
    }

    /// Returns `true` for field operations (Put/Get Static/Instance).
    pub fn is_field_op(self) -> bool {
        (self as u8) <= sys::MethodHandleType_GET_INSTANCE
    }
}

/// A resolved method handle reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ResolvedMethodHandle {
    pub handle_type: MethodHandleType,
    /// Interned name of the referenced field or method.
    pub entity: crate::StringId,
    /// Dense method index in [`File::all_methods`](crate::File::all_methods)
    /// when `handle_type` is a method op and the target is a class method in
    /// this file (`None` for foreign items or unindexed hand-built refs).
    pub target_method: Option<crate::MethodIdx>,
    /// Dense field index in [`File::all_fields`](crate::File::all_fields)
    /// when `handle_type` is a field op and the target is a class field in
    /// this file (`None` for foreign items or unindexed hand-built refs).
    pub target_field: Option<crate::FieldIdx>,
    /// Offset of the referenced field/method item in the source file;
    /// 0 when the reference could not be resolved or has no wire provenance.
    pub entity_offset: u32,
}

/// Fully-typed annotation element value.
///
/// All variants are fully resolved at decode time:
/// - String, Record, Method, Enum → interned [`StringId`](crate::StringId)
///   (plus dense [`MethodIdx`](crate::MethodIdx) / [`FieldIdx`](crate::FieldIdx) handles)
/// - Annotation → iteratively resolved nested [`Annotation`](crate::Annotation)
/// - MethodHandle → resolved [`ResolvedMethodHandle`]
/// - LiteralArray → resolved [`LiteralValue`](crate::LiteralValue) items
///   (nested [`LiteralArrayIdx`](crate::LiteralArrayIdx) and
///   [`MethodIdx`](crate::MethodIdx) items are rewritten to table indices)
/// - Array → element count preserved with original tag
///
/// `Drop`, `Clone`, `PartialEq`, and `Debug` are implemented iteratively over
/// explicit heap workstacks so arbitrarily deep annotation trees never overflow
/// the call stack.
pub enum AnnotationValue {
    Bool(bool),
    I8(i8),
    U8(u8),
    I16(i16),
    U16(u16),
    I32(i32),
    U32(u32),
    I64(i64),
    U64(u64),
    F32(f32),
    F64(f64),
    /// Interned string content.
    String(crate::StringId),
    /// Interned class descriptor.
    Record(crate::StringId),
    /// Referenced method: interned name, optional [`MethodIdx`](crate::MethodIdx)
    /// into [`File::all_methods`](crate::File::all_methods), and source-file
    /// item offset (`0` when hand-built).
    Method {
        name: crate::StringId,
        method: Option<crate::MethodIdx>,
        offset: u32,
    },
    /// Referenced enum field: interned name, optional [`FieldIdx`](crate::FieldIdx)
    /// into [`File::all_fields`](crate::File::all_fields), and source-file
    /// item offset (`0` when hand-built).
    Enum {
        name: crate::StringId,
        field: Option<crate::FieldIdx>,
        offset: u32,
    },
    /// Recursively resolved nested annotation.
    Annotation(Box<crate::model::Annotation>),
    /// Resolved method handle with type and entity reference.
    MethodHandle(ResolvedMethodHandle),
    /// Resolved literal array contents.
    LiteralArray(Vec<crate::LiteralValue>),
    Void,
    StringNullptr,
    /// Resolved typed array of annotation values.
    ///
    /// `tag` preserves the original array element type tag from the ABC file
    /// (e.g. `ArrayU1`, `ArrayI8`, `ArrayString`, etc.).
    Array {
        tag: u8,
        values: Vec<AnnotationValue>,
    },
}

#[inline]
const fn has_nested_annotation_children(v: &AnnotationValue) -> bool {
    matches!(
        v,
        AnnotationValue::Annotation(_) | AnnotationValue::Array { .. }
    )
}

impl Drop for AnnotationValue {
    fn drop(&mut self) {
        let needs_drain = match self {
            Self::Annotation(ann) => ann
                .elements
                .iter()
                .any(|e| has_nested_annotation_children(&e.value)),
            Self::Array { values, .. } => values.iter().any(has_nested_annotation_children),
            _ => false,
        };
        if !needs_drain {
            return;
        }
        let mut stack: Vec<AnnotationValue> = Vec::new();
        match self {
            Self::Annotation(ann) => {
                for elem in std::mem::take(&mut ann.elements) {
                    if has_nested_annotation_children(&elem.value) {
                        stack.push(elem.value);
                    }
                }
            }
            Self::Array { values, .. } => {
                for v in std::mem::take(values) {
                    if has_nested_annotation_children(&v) {
                        stack.push(v);
                    }
                }
            }
            _ => {}
        }
        while let Some(mut node) = stack.pop() {
            match &mut node {
                Self::Annotation(ann) => {
                    for elem in std::mem::take(&mut ann.elements) {
                        if has_nested_annotation_children(&elem.value) {
                            stack.push(elem.value);
                        }
                    }
                }
                Self::Array { values, .. } => {
                    for v in std::mem::take(values) {
                        if has_nested_annotation_children(&v) {
                            stack.push(v);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

fn try_clone_leaf_annotation_value(v: &AnnotationValue) -> Option<AnnotationValue> {
    Some(match v {
        AnnotationValue::Bool(x) => AnnotationValue::Bool(*x),
        AnnotationValue::I8(x) => AnnotationValue::I8(*x),
        AnnotationValue::U8(x) => AnnotationValue::U8(*x),
        AnnotationValue::I16(x) => AnnotationValue::I16(*x),
        AnnotationValue::U16(x) => AnnotationValue::U16(*x),
        AnnotationValue::I32(x) => AnnotationValue::I32(*x),
        AnnotationValue::U32(x) => AnnotationValue::U32(*x),
        AnnotationValue::I64(x) => AnnotationValue::I64(*x),
        AnnotationValue::U64(x) => AnnotationValue::U64(*x),
        AnnotationValue::F32(x) => AnnotationValue::F32(*x),
        AnnotationValue::F64(x) => AnnotationValue::F64(*x),
        AnnotationValue::String(x) => AnnotationValue::String(*x),
        AnnotationValue::Record(x) => AnnotationValue::Record(*x),
        AnnotationValue::Method {
            name,
            method,
            offset,
        } => AnnotationValue::Method {
            name: *name,
            method: *method,
            offset: *offset,
        },
        AnnotationValue::Enum {
            name,
            field,
            offset,
        } => AnnotationValue::Enum {
            name: *name,
            field: *field,
            offset: *offset,
        },
        AnnotationValue::MethodHandle(mh) => AnnotationValue::MethodHandle(*mh),
        AnnotationValue::LiteralArray(vals) => AnnotationValue::LiteralArray(vals.clone()),
        AnnotationValue::Void => AnnotationValue::Void,
        AnnotationValue::StringNullptr => AnnotationValue::StringNullptr,
        AnnotationValue::Annotation(_) | AnnotationValue::Array { .. } => return None,
    })
}

enum AnnCloneFrame<'a> {
    Ann {
        class_descriptor: crate::StringId,
        elems: &'a [AnnotationElem],
        next_idx: usize,
        pending_name: Option<crate::StringId>,
        built: Vec<AnnotationElem>,
    },
    Arr {
        tag: u8,
        vals: &'a [AnnotationValue],
        next_idx: usize,
        built: Vec<AnnotationValue>,
    },
}

fn run_ann_clone_stack(mut stack: Vec<AnnCloneFrame<'_>>) -> AnnotationValue {
    let mut completed: Option<AnnotationValue> = None;
    while let Some(frame) = stack.last_mut() {
        if let Some(child_val) = completed.take() {
            match frame {
                AnnCloneFrame::Ann {
                    pending_name,
                    built,
                    ..
                } => {
                    if let Some(name) = pending_name.take() {
                        built.push(AnnotationElem {
                            name,
                            value: child_val,
                        });
                    }
                }
                AnnCloneFrame::Arr { built, .. } => {
                    built.push(child_val);
                }
            }
        }

        let mut push_frame: Option<AnnCloneFrame<'_>> = None;
        match frame {
            AnnCloneFrame::Ann {
                elems,
                next_idx,
                pending_name,
                built,
                ..
            } => {
                while *next_idx < elems.len() {
                    let elem = &elems[*next_idx];
                    *next_idx += 1;
                    if let Some(leaf) = try_clone_leaf_annotation_value(&elem.value) {
                        built.push(AnnotationElem {
                            name: elem.name,
                            value: leaf,
                        });
                    } else {
                        *pending_name = Some(elem.name);
                        push_frame = Some(match &elem.value {
                            AnnotationValue::Annotation(inner) => AnnCloneFrame::Ann {
                                class_descriptor: inner.class_descriptor,
                                elems: &inner.elements,
                                next_idx: 0,
                                pending_name: None,
                                built: Vec::with_capacity(inner.elements.len()),
                            },
                            AnnotationValue::Array { tag, values } => AnnCloneFrame::Arr {
                                tag: *tag,
                                vals: values,
                                next_idx: 0,
                                built: Vec::with_capacity(values.len()),
                            },
                            _ => unreachable!(),
                        });
                        break;
                    }
                }
            }
            AnnCloneFrame::Arr {
                vals,
                next_idx,
                built,
                ..
            } => {
                while *next_idx < vals.len() {
                    let item = &vals[*next_idx];
                    *next_idx += 1;
                    if let Some(leaf) = try_clone_leaf_annotation_value(item) {
                        built.push(leaf);
                    } else {
                        push_frame = Some(match item {
                            AnnotationValue::Annotation(inner) => AnnCloneFrame::Ann {
                                class_descriptor: inner.class_descriptor,
                                elems: &inner.elements,
                                next_idx: 0,
                                pending_name: None,
                                built: Vec::with_capacity(inner.elements.len()),
                            },
                            AnnotationValue::Array { tag, values } => AnnCloneFrame::Arr {
                                tag: *tag,
                                vals: values,
                                next_idx: 0,
                                built: Vec::with_capacity(values.len()),
                            },
                            _ => unreachable!(),
                        });
                        break;
                    }
                }
            }
        }

        if let Some(next) = push_frame {
            stack.push(next);
            continue;
        }

        let Some(finished) = stack.pop() else {
            break;
        };
        let node = match finished {
            AnnCloneFrame::Ann {
                class_descriptor,
                built,
                ..
            } => AnnotationValue::Annotation(Box::new(Annotation {
                class_descriptor,
                elements: built,
            })),
            AnnCloneFrame::Arr { tag, built, .. } => AnnotationValue::Array { tag, values: built },
        };
        if stack.is_empty() {
            return node;
        }
        completed = Some(node);
    }
    AnnotationValue::Void
}

fn clone_annotation_value_iterative(root: &AnnotationValue) -> AnnotationValue {
    if let Some(leaf) = try_clone_leaf_annotation_value(root) {
        return leaf;
    }
    let init = match root {
        AnnotationValue::Annotation(inner) => AnnCloneFrame::Ann {
            class_descriptor: inner.class_descriptor,
            elems: &inner.elements,
            next_idx: 0,
            pending_name: None,
            built: Vec::with_capacity(inner.elements.len()),
        },
        AnnotationValue::Array { tag, values } => AnnCloneFrame::Arr {
            tag: *tag,
            vals: values,
            next_idx: 0,
            built: Vec::with_capacity(values.len()),
        },
        _ => unreachable!(),
    };
    run_ann_clone_stack(vec![init])
}

impl Clone for AnnotationValue {
    fn clone(&self) -> Self {
        clone_annotation_value_iterative(self)
    }
}

impl Clone for AnnotationElem {
    fn clone(&self) -> Self {
        Self {
            name: self.name,
            value: clone_annotation_value_iterative(&self.value),
        }
    }
}

impl Clone for Annotation {
    fn clone(&self) -> Self {
        let mut elements = Vec::with_capacity(self.elements.len());
        for elem in &self.elements {
            elements.push(AnnotationElem {
                name: elem.name,
                value: clone_annotation_value_iterative(&elem.value),
            });
        }
        Self {
            class_descriptor: self.class_descriptor,
            elements,
        }
    }
}

fn eq_annotation_value_pairs<'a>(
    mut stack: Vec<(&'a AnnotationValue, &'a AnnotationValue)>,
) -> bool {
    while let Some((lhs, rhs)) = stack.pop() {
        match (lhs, rhs) {
            (AnnotationValue::Bool(a), AnnotationValue::Bool(b)) if a == b => {}
            (AnnotationValue::I8(a), AnnotationValue::I8(b)) if a == b => {}
            (AnnotationValue::U8(a), AnnotationValue::U8(b)) if a == b => {}
            (AnnotationValue::I16(a), AnnotationValue::I16(b)) if a == b => {}
            (AnnotationValue::U16(a), AnnotationValue::U16(b)) if a == b => {}
            (AnnotationValue::I32(a), AnnotationValue::I32(b)) if a == b => {}
            (AnnotationValue::U32(a), AnnotationValue::U32(b)) if a == b => {}
            (AnnotationValue::I64(a), AnnotationValue::I64(b)) if a == b => {}
            (AnnotationValue::U64(a), AnnotationValue::U64(b)) if a == b => {}
            (AnnotationValue::F32(a), AnnotationValue::F32(b)) if a == b => {}
            (AnnotationValue::F64(a), AnnotationValue::F64(b)) if a == b => {}
            (AnnotationValue::String(a), AnnotationValue::String(b)) if a == b => {}
            (AnnotationValue::Record(a), AnnotationValue::Record(b)) if a == b => {}
            (
                AnnotationValue::Method {
                    name: na,
                    method: ma,
                    offset: oa,
                },
                AnnotationValue::Method {
                    name: nb,
                    method: mb,
                    offset: ob,
                },
            ) if na == nb && ma == mb && oa == ob => {}
            (
                AnnotationValue::Enum {
                    name: na,
                    field: fa,
                    offset: oa,
                },
                AnnotationValue::Enum {
                    name: nb,
                    field: fb,
                    offset: ob,
                },
            ) if na == nb && fa == fb && oa == ob => {}
            (AnnotationValue::MethodHandle(a), AnnotationValue::MethodHandle(b)) if a == b => {}
            (AnnotationValue::LiteralArray(a), AnnotationValue::LiteralArray(b)) if a == b => {}
            (AnnotationValue::Void, AnnotationValue::Void)
            | (AnnotationValue::StringNullptr, AnnotationValue::StringNullptr) => {}
            (AnnotationValue::Annotation(a), AnnotationValue::Annotation(b)) => {
                if a.class_descriptor != b.class_descriptor || a.elements.len() != b.elements.len()
                {
                    return false;
                }
                for (le, re) in a.elements.iter().zip(&b.elements) {
                    if le.name != re.name {
                        return false;
                    }
                    stack.push((&le.value, &re.value));
                }
            }
            (
                AnnotationValue::Array {
                    tag: ta,
                    values: va,
                },
                AnnotationValue::Array {
                    tag: tb,
                    values: vb,
                },
            ) => {
                if ta != tb || va.len() != vb.len() {
                    return false;
                }
                for (lv, rv) in va.iter().zip(vb) {
                    stack.push((lv, rv));
                }
            }
            _ => return false,
        }
    }
    true
}

impl PartialEq for AnnotationValue {
    fn eq(&self, other: &Self) -> bool {
        eq_annotation_value_pairs(vec![(self, other)])
    }
}

impl PartialEq for AnnotationElem {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && eq_annotation_value_pairs(vec![(&self.value, &other.value)])
    }
}

impl PartialEq for Annotation {
    fn eq(&self, other: &Self) -> bool {
        if self.class_descriptor != other.class_descriptor
            || self.elements.len() != other.elements.len()
        {
            return false;
        }
        let mut stack = Vec::with_capacity(self.elements.len());
        for (le, re) in self.elements.iter().zip(&other.elements) {
            if le.name != re.name {
                return false;
            }
            stack.push((&le.value, &re.value));
        }
        eq_annotation_value_pairs(stack)
    }
}

enum AnnDebugStep<'a> {
    Str(&'static str),
    Ann(&'a Annotation),
    Elem(&'a AnnotationElem),
    Value(&'a AnnotationValue),
    ElemSlice {
        slice: &'a [AnnotationElem],
        idx: usize,
    },
    ValSlice {
        slice: &'a [AnnotationValue],
        idx: usize,
    },
}

fn fmt_annotation_debug(
    mut stack: Vec<AnnDebugStep<'_>>,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    while let Some(step) = stack.pop() {
        match step {
            AnnDebugStep::Str(s) => f.write_str(s)?,
            AnnDebugStep::Ann(ann) => {
                write!(
                    f,
                    "Annotation {{ class_descriptor: {:?}, elements: [",
                    ann.class_descriptor
                )?;
                stack.push(AnnDebugStep::Str("] }"));
                stack.push(AnnDebugStep::ElemSlice {
                    slice: &ann.elements,
                    idx: 0,
                });
            }
            AnnDebugStep::Elem(elem) => {
                write!(f, "AnnotationElem {{ name: {:?}, value: ", elem.name)?;
                stack.push(AnnDebugStep::Str(" }"));
                stack.push(AnnDebugStep::Value(&elem.value));
            }
            AnnDebugStep::ElemSlice { slice, idx } => {
                if idx < slice.len() {
                    if idx > 0 {
                        f.write_str(", ")?;
                    }
                    stack.push(AnnDebugStep::ElemSlice {
                        slice,
                        idx: idx + 1,
                    });
                    stack.push(AnnDebugStep::Elem(&slice[idx]));
                }
            }
            AnnDebugStep::ValSlice { slice, idx } => {
                if idx < slice.len() {
                    if idx > 0 {
                        f.write_str(", ")?;
                    }
                    stack.push(AnnDebugStep::ValSlice {
                        slice,
                        idx: idx + 1,
                    });
                    stack.push(AnnDebugStep::Value(&slice[idx]));
                }
            }
            AnnDebugStep::Value(val) => match val {
                AnnotationValue::Bool(v) => write!(f, "Bool({v:?})")?,
                AnnotationValue::I8(v) => write!(f, "I8({v:?})")?,
                AnnotationValue::U8(v) => write!(f, "U8({v:?})")?,
                AnnotationValue::I16(v) => write!(f, "I16({v:?})")?,
                AnnotationValue::U16(v) => write!(f, "U16({v:?})")?,
                AnnotationValue::I32(v) => write!(f, "I32({v:?})")?,
                AnnotationValue::U32(v) => write!(f, "U32({v:?})")?,
                AnnotationValue::I64(v) => write!(f, "I64({v:?})")?,
                AnnotationValue::U64(v) => write!(f, "U64({v:?})")?,
                AnnotationValue::F32(v) => write!(f, "F32({v:?})")?,
                AnnotationValue::F64(v) => write!(f, "F64({v:?})")?,
                AnnotationValue::String(v) => write!(f, "String({v:?})")?,
                AnnotationValue::Record(v) => write!(f, "Record({v:?})")?,
                AnnotationValue::Method {
                    name,
                    method,
                    offset,
                } => write!(
                    f,
                    "Method {{ name: {name:?}, method: {method:?}, offset: {offset:?} }}"
                )?,
                AnnotationValue::Enum {
                    name,
                    field,
                    offset,
                } => write!(
                    f,
                    "Enum {{ name: {name:?}, field: {field:?}, offset: {offset:?} }}"
                )?,
                AnnotationValue::MethodHandle(mh) => write!(f, "MethodHandle({mh:?})")?,
                AnnotationValue::LiteralArray(vals) => write!(f, "LiteralArray({vals:?})")?,
                AnnotationValue::Void => f.write_str("Void")?,
                AnnotationValue::StringNullptr => f.write_str("StringNullptr")?,
                AnnotationValue::Annotation(inner) => {
                    f.write_str("Annotation(")?;
                    stack.push(AnnDebugStep::Str(")"));
                    stack.push(AnnDebugStep::Ann(inner));
                }
                AnnotationValue::Array { tag, values } => {
                    write!(f, "Array {{ tag: {tag:?}, values: [")?;
                    stack.push(AnnDebugStep::Str("] }"));
                    stack.push(AnnDebugStep::ValSlice {
                        slice: values,
                        idx: 0,
                    });
                }
            },
        }
    }
    Ok(())
}

impl fmt::Debug for AnnotationValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_annotation_debug(vec![AnnDebugStep::Value(self)], f)
    }
}

impl fmt::Debug for AnnotationElem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_annotation_debug(vec![AnnDebugStep::Elem(self)], f)
    }
}

impl fmt::Debug for Annotation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_annotation_debug(vec![AnnDebugStep::Ann(self)], f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `from_u8` covers every vendored `MethodHandleType` constant and
    /// rejects unknown bytes; `is_field_op` splits at GET_INSTANCE.
    #[test]
    fn method_handle_type_table() {
        let cases: [(u8, MethodHandleType, bool); 9] = [
            (
                sys::MethodHandleType_PUT_STATIC,
                MethodHandleType::PutStatic,
                true,
            ),
            (
                sys::MethodHandleType_GET_STATIC,
                MethodHandleType::GetStatic,
                true,
            ),
            (
                sys::MethodHandleType_PUT_INSTANCE,
                MethodHandleType::PutInstance,
                true,
            ),
            (
                sys::MethodHandleType_GET_INSTANCE,
                MethodHandleType::GetInstance,
                true,
            ),
            (
                sys::MethodHandleType_INVOKE_STATIC,
                MethodHandleType::InvokeStatic,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_INSTANCE,
                MethodHandleType::InvokeInstance,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_CONSTRUCTOR,
                MethodHandleType::InvokeConstructor,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_DIRECT,
                MethodHandleType::InvokeDirect,
                false,
            ),
            (
                sys::MethodHandleType_INVOKE_INTERFACE,
                MethodHandleType::InvokeInterface,
                false,
            ),
        ];
        for (raw, expect, field_op) in cases {
            assert_eq!(MethodHandleType::from_u8(raw), Some(expect), "raw {raw}");
            assert_eq!(expect.is_field_op(), field_op, "raw {raw}");
        }
        assert_eq!(MethodHandleType::from_u8(9), None);
        assert_eq!(MethodHandleType::from_u8(u8::MAX), None);
    }
}
