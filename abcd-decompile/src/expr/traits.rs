//! Iterative heap-workstack `Drop`, `Clone`, `PartialEq`, `Eq`, and `Debug`
//! implementations for [`Expr`], [`Lit`], [`ObjEntry`], [`ObjKey`], and [`ArrayElem`].

use super::{ArrayElem, Expr, Lit, ObjEntry, ObjKey};

impl Drop for Lit {
    fn drop(&mut self) {
        let mut stack: Vec<Lit> = Vec::new();
        match self {
            Lit::Array(items) if !items.is_empty() => {
                stack.extend(std::mem::take(items));
            }
            Lit::Object(entries) if !entries.is_empty() => {
                for (k, v) in std::mem::take(entries) {
                    stack.push(k);
                    stack.push(v);
                }
            }
            _ => return,
        }
        while let Some(mut cur) = stack.pop() {
            match &mut cur {
                Lit::Array(items) => stack.extend(std::mem::take(items)),
                Lit::Object(entries) => {
                    for (k, v) in std::mem::take(entries) {
                        stack.push(k);
                        stack.push(v);
                    }
                }
                _ => {}
            }
        }
    }
}

impl Clone for Lit {
    fn clone(&self) -> Self {
        fn clone_flat_lit(lit: &Lit) -> Option<Lit> {
            match lit {
                Lit::Undefined => Some(Lit::Undefined),
                Lit::Hole => Some(Lit::Hole),
                Lit::Null => Some(Lit::Null),
                Lit::Bool(b) => Some(Lit::Bool(*b)),
                Lit::Number(n) => Some(Lit::Number(*n)),
                Lit::Int64(n) => Some(Lit::Int64(*n)),
                Lit::UInt64(n) => Some(Lit::UInt64(*n)),
                Lit::String(s) => Some(Lit::String(s.clone())),
                Lit::Utf16(u) => Some(Lit::Utf16(u.clone())),
                Lit::BigInt(s) => Some(Lit::BigInt(s.clone())),
                Lit::MethodRef(f) => Some(Lit::MethodRef(*f)),
                Lit::Array(items) if items.is_empty() => Some(Lit::Array(Vec::new())),
                Lit::Object(entries) if entries.is_empty() => Some(Lit::Object(Vec::new())),
                Lit::Array(_) | Lit::Object(_) => None,
            }
        }

        if let Some(flat) = clone_flat_lit(self) {
            return flat;
        }

        enum Step<'a> {
            Eval(&'a Lit),
            BuildArray(usize),
            BuildObject(usize),
        }

        let mut steps: Vec<Step<'_>> = vec![Step::Eval(self)];
        let mut vals: Vec<Lit> = Vec::new();
        while let Some(step) = steps.pop() {
            match step {
                Step::Eval(lit) => {
                    if let Some(flat) = clone_flat_lit(lit) {
                        vals.push(flat);
                    } else {
                        match lit {
                            Lit::Array(items) => {
                                steps.push(Step::BuildArray(items.len()));
                                for it in items.iter().rev() {
                                    steps.push(Step::Eval(it));
                                }
                            }
                            Lit::Object(entries) => {
                                steps.push(Step::BuildObject(entries.len()));
                                for (k, v) in entries.iter().rev() {
                                    steps.push(Step::Eval(v));
                                    steps.push(Step::Eval(k));
                                }
                            }
                            _ => vals.push(Lit::Undefined),
                        }
                    }
                }
                Step::BuildArray(n) => {
                    let start = vals.len().saturating_sub(n);
                    let arr = vals.split_off(start);
                    vals.push(Lit::Array(arr));
                }
                Step::BuildObject(n) => {
                    let start = vals.len().saturating_sub(n.saturating_mul(2));
                    let mut drain = vals.drain(start..);
                    let mut pairs = Vec::with_capacity(n);
                    for _ in 0..n {
                        let k = drain.next().unwrap_or(Lit::Undefined);
                        let v = drain.next().unwrap_or(Lit::Undefined);
                        pairs.push((k, v));
                    }
                    drop(drain);
                    vals.push(Lit::Object(pairs));
                }
            }
        }
        vals.pop().unwrap_or(Lit::Undefined)
    }
}

impl PartialEq for Lit {
    fn eq(&self, other: &Self) -> bool {
        fn cmp_lit_step<'a>(a: &'a Lit, b: &'a Lit, stack: &mut Vec<(&'a Lit, &'a Lit)>) -> bool {
            match (a, b) {
                (Lit::Undefined, Lit::Undefined)
                | (Lit::Hole, Lit::Hole)
                | (Lit::Null, Lit::Null) => true,
                (Lit::Bool(x), Lit::Bool(y)) => x == y,
                (Lit::Number(x), Lit::Number(y)) => x == y,
                (Lit::Int64(x), Lit::Int64(y)) => x == y,
                (Lit::UInt64(x), Lit::UInt64(y)) => x == y,
                (Lit::String(x), Lit::String(y)) => x == y,
                (Lit::Utf16(x), Lit::Utf16(y)) => x == y,
                (Lit::BigInt(x), Lit::BigInt(y)) => x == y,
                (Lit::MethodRef(x), Lit::MethodRef(y)) => x == y,
                (Lit::Array(xs), Lit::Array(ys)) => {
                    if xs.len() != ys.len() {
                        return false;
                    }
                    for (x, y) in xs.iter().zip(ys.iter()).rev() {
                        stack.push((x, y));
                    }
                    true
                }
                (Lit::Object(xs), Lit::Object(ys)) => {
                    if xs.len() != ys.len() {
                        return false;
                    }
                    for ((kx, vx), (ky, vy)) in xs.iter().zip(ys.iter()).rev() {
                        stack.push((vx, vy));
                        stack.push((kx, ky));
                    }
                    true
                }
                _ => false,
            }
        }

        let mut stack: Vec<(&Lit, &Lit)> = Vec::new();
        if !cmp_lit_step(self, other, &mut stack) {
            return false;
        }
        while let Some((x, y)) = stack.pop() {
            if !cmp_lit_step(x, y, &mut stack) {
                return false;
            }
        }
        true
    }
}

fn drain_obj_key_children(key: &mut ObjKey, stack: &mut Vec<Expr>) {
    if let ObjKey::Computed(ke) = key {
        stack.push(std::mem::replace(ke.as_mut(), Expr::SuperMarker));
    }
}

fn drain_obj_entry_children(entry: &mut ObjEntry, stack: &mut Vec<Expr>) {
    match entry {
        ObjEntry::KeyValue(_, v)
        | ObjEntry::Spread(v)
        | ObjEntry::Proto(v)
        | ObjEntry::Method(_, v) => stack.push(std::mem::replace(v, Expr::SuperMarker)),
        ObjEntry::Computed(k, v) => {
            stack.push(std::mem::replace(k, Expr::SuperMarker));
            stack.push(std::mem::replace(v, Expr::SuperMarker));
        }
        ObjEntry::Getter(k, v) | ObjEntry::Setter(k, v) => {
            drain_obj_key_children(k, stack);
            stack.push(std::mem::replace(v, Expr::SuperMarker));
        }
    }
}

fn drain_array_elem_children(elem: &mut ArrayElem, stack: &mut Vec<Expr>) {
    match elem {
        ArrayElem::Item(e) | ArrayElem::Spread(e) => {
            stack.push(std::mem::replace(e, Expr::SuperMarker));
        }
    }
}

fn drain_expr_children(expr: &mut Expr, stack: &mut Vec<Expr>) {
    let take_box = |b: &mut Box<Expr>| std::mem::replace(b.as_mut(), Expr::SuperMarker);
    match expr {
        Expr::PropName { object, .. }
        | Expr::PrivateLoad { object, .. }
        | Expr::PrivateTest { object, .. } => stack.push(take_box(object)),
        Expr::PropIndex { object, index } => {
            stack.push(take_box(object));
            stack.push(take_box(index));
        }
        Expr::PropDyn { object, key } => {
            stack.push(take_box(object));
            stack.push(take_box(key));
        }
        Expr::SuperProp { key: Some(k), .. } => {
            stack.push(take_box(k));
        }
        Expr::Call {
            callee, this, args, ..
        } => {
            stack.push(take_box(callee));
            if let Some(t) = this.as_mut() {
                stack.push(take_box(t));
            }
            stack.extend(std::mem::take(args));
        }
        Expr::DynamicImport { specifier } => stack.push(take_box(specifier)),
        Expr::Unary { operand, .. } => stack.push(take_box(operand)),
        Expr::Delete { target } => stack.push(take_box(target)),
        Expr::Binary { left, right, .. } | Expr::Compare { left, right, .. } => {
            stack.push(take_box(left));
            stack.push(take_box(right));
        }
        Expr::Closure { captures, .. } if !captures.is_empty() => {
            for (_, c) in std::mem::take(captures) {
                stack.push(c);
            }
        }
        Expr::Class {
            heritage: Some(h), ..
        } => {
            stack.push(take_box(h));
        }
        Expr::Yield { value }
        | Expr::YieldStar { value }
        | Expr::Await { value, .. }
        | Expr::Iter { obj: value, .. }
        | Expr::CreateGenerator { func: value }
        | Expr::GeneratorDriver { genobj: value, .. }
        | Expr::AsyncDriver { value, .. } => stack.push(take_box(value)),
        Expr::TaggedTemplate { tag, exprs, .. } => {
            stack.push(take_box(tag));
            stack.extend(std::mem::take(exprs));
        }
        Expr::IterResultObj { value, done }
        | Expr::CopyDataProps {
            dst: value,
            src: done,
        }
        | Expr::SetObjectWithProto {
            obj: value,
            proto: done,
        } => {
            stack.push(take_box(value));
            stack.push(take_box(done));
        }
        Expr::AsyncGeneratorResolve {
            genobj: a,
            value: b,
            done: c,
        }
        | Expr::ArraySpread {
            dst: a,
            index: b,
            src: c,
        } => {
            stack.push(take_box(a));
            stack.push(take_box(b));
            stack.push(take_box(c));
        }
        Expr::RestObject { obj, excluded } => {
            stack.push(take_box(obj));
            stack.extend(std::mem::take(excluded));
        }
        Expr::DefineGetterSetter {
            obj,
            key,
            getter,
            setter,
        } => {
            stack.push(take_box(obj));
            stack.push(take_box(key));
            stack.push(take_box(getter));
            stack.push(take_box(setter));
        }
        Expr::ObjectBuild { entries } if !entries.is_empty() => {
            for mut entry in std::mem::take(entries) {
                drain_obj_entry_children(&mut entry, stack);
            }
        }
        Expr::ArrayBuild { elements } if !elements.is_empty() => {
            for mut elem in std::mem::take(elements) {
                drain_array_elem_children(&mut elem, stack);
            }
        }
        Expr::Fallback { operands, .. } if !operands.is_empty() => {
            stack.extend(std::mem::take(operands));
        }
        _ => {}
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack: Vec<Expr> = Vec::new();
        drain_expr_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_expr_children(&mut cur, &mut stack);
        }
    }
}

impl Clone for Expr {
    fn clone(&self) -> Self {
        fn clone_flat_expr(e: &Expr) -> Option<Expr> {
            match e {
                Expr::Lit(l) => Some(Expr::Lit(l.clone())),
                Expr::Ident(s) => Some(Expr::Ident(s.clone())),
                Expr::Temp { value, name } => Some(Expr::Temp {
                    value: *value,
                    name: name.clone(),
                }),
                Expr::SuperProp { name, key: None } => Some(Expr::SuperProp {
                    name: name.clone(),
                    key: None,
                }),
                Expr::SuperMarker => Some(Expr::SuperMarker),
                Expr::RegExp { pattern, flags } => Some(Expr::RegExp {
                    pattern: pattern.clone(),
                    flags: flags.clone(),
                }),
                Expr::ObjectLit { entries } => Some(Expr::ObjectLit {
                    entries: entries.clone(),
                }),
                Expr::ArrayLit { elements } => Some(Expr::ArrayLit {
                    elements: elements.clone(),
                }),
                Expr::Closure {
                    body,
                    name,
                    kind,
                    captures,
                } if captures.is_empty() => Some(Expr::Closure {
                    body: *body,
                    name: name.clone(),
                    kind: *kind,
                    captures: Vec::new(),
                }),
                Expr::Class {
                    ctor,
                    name,
                    heritage: None,
                    members,
                    member_attrs,
                    sendable,
                } => Some(Expr::Class {
                    ctor: *ctor,
                    name: name.clone(),
                    heritage: None,
                    members: *members,
                    member_attrs: member_attrs.clone(),
                    sendable: *sendable,
                }),
                Expr::NewTarget => Some(Expr::NewTarget),
                Expr::GlobalThis => Some(Expr::GlobalThis),
                Expr::SelfFunction(s) => Some(Expr::SelfFunction(s.clone())),
                Expr::Arguments => Some(Expr::Arguments),
                Expr::RestArgs { start_index } => Some(Expr::RestArgs {
                    start_index: *start_index,
                }),
                Expr::TemplateObject { raw, cooked } => Some(Expr::TemplateObject {
                    raw: raw.clone(),
                    cooked: cooked.clone(),
                }),
                Expr::ModuleNamespace { index } => Some(Expr::ModuleNamespace { index: *index }),
                Expr::ObjectBuild { entries } if entries.is_empty() => Some(Expr::ObjectBuild {
                    entries: Vec::new(),
                }),
                Expr::ArrayBuild { elements } if elements.is_empty() => Some(Expr::ArrayBuild {
                    elements: Vec::new(),
                }),
                Expr::Fallback { op, note, operands } if operands.is_empty() => {
                    Some(Expr::Fallback {
                        op,
                        note,
                        operands: Vec::new(),
                    })
                }
                _ => None,
            }
        }

        if let Some(flat) = clone_flat_expr(self) {
            return flat;
        }

        enum Step<'a> {
            Eval(&'a Expr),
            Finish(&'a Expr),
        }

        let pop_expr = |vals: &mut Vec<Expr>| vals.pop().unwrap_or(Expr::SuperMarker);
        let mut steps: Vec<Step<'_>> = vec![Step::Eval(self)];
        let mut vals: Vec<Expr> = Vec::new();

        while let Some(step) = steps.pop() {
            match step {
                Step::Eval(e) => {
                    if let Some(flat) = clone_flat_expr(e) {
                        vals.push(flat);
                        continue;
                    }
                    steps.push(Step::Finish(e));
                    match e {
                        Expr::PropName { object, .. }
                        | Expr::PrivateLoad { object, .. }
                        | Expr::PrivateTest { object, .. } => steps.push(Step::Eval(object)),
                        Expr::PropIndex { object, index } => {
                            steps.push(Step::Eval(index));
                            steps.push(Step::Eval(object));
                        }
                        Expr::PropDyn { object, key } => {
                            steps.push(Step::Eval(key));
                            steps.push(Step::Eval(object));
                        }
                        Expr::SuperProp { key: Some(k), .. } => steps.push(Step::Eval(k)),
                        Expr::Call {
                            callee, this, args, ..
                        } => {
                            for a in args.iter().rev() {
                                steps.push(Step::Eval(a));
                            }
                            if let Some(t) = this {
                                steps.push(Step::Eval(t));
                            }
                            steps.push(Step::Eval(callee));
                        }
                        Expr::DynamicImport { specifier } => steps.push(Step::Eval(specifier)),
                        Expr::Unary { operand, .. } => steps.push(Step::Eval(operand)),
                        Expr::Delete { target } => steps.push(Step::Eval(target)),
                        Expr::Binary { left, right, .. } | Expr::Compare { left, right, .. } => {
                            steps.push(Step::Eval(right));
                            steps.push(Step::Eval(left));
                        }
                        Expr::Closure { captures, .. } => {
                            for (_, c) in captures.iter().rev() {
                                steps.push(Step::Eval(c));
                            }
                        }
                        Expr::Class {
                            heritage: Some(h), ..
                        } => steps.push(Step::Eval(h)),
                        Expr::Yield { value }
                        | Expr::YieldStar { value }
                        | Expr::Await { value, .. }
                        | Expr::Iter { obj: value, .. }
                        | Expr::CreateGenerator { func: value }
                        | Expr::GeneratorDriver { genobj: value, .. }
                        | Expr::AsyncDriver { value, .. } => steps.push(Step::Eval(value)),
                        Expr::TaggedTemplate { tag, exprs, .. } => {
                            for ex in exprs.iter().rev() {
                                steps.push(Step::Eval(ex));
                            }
                            steps.push(Step::Eval(tag));
                        }
                        Expr::IterResultObj { value, done }
                        | Expr::CopyDataProps {
                            dst: value,
                            src: done,
                        }
                        | Expr::SetObjectWithProto {
                            obj: value,
                            proto: done,
                        } => {
                            steps.push(Step::Eval(done));
                            steps.push(Step::Eval(value));
                        }
                        Expr::AsyncGeneratorResolve {
                            genobj: a,
                            value: b,
                            done: c,
                        }
                        | Expr::ArraySpread {
                            dst: a,
                            index: b,
                            src: c,
                        } => {
                            steps.push(Step::Eval(c));
                            steps.push(Step::Eval(b));
                            steps.push(Step::Eval(a));
                        }
                        Expr::RestObject { obj, excluded } => {
                            for ex in excluded.iter().rev() {
                                steps.push(Step::Eval(ex));
                            }
                            steps.push(Step::Eval(obj));
                        }
                        Expr::DefineGetterSetter {
                            obj,
                            key,
                            getter,
                            setter,
                        } => {
                            steps.push(Step::Eval(setter));
                            steps.push(Step::Eval(getter));
                            steps.push(Step::Eval(key));
                            steps.push(Step::Eval(obj));
                        }
                        Expr::ObjectBuild { entries } => {
                            for entry in entries.iter().rev() {
                                match entry {
                                    ObjEntry::KeyValue(_, v)
                                    | ObjEntry::Spread(v)
                                    | ObjEntry::Proto(v)
                                    | ObjEntry::Method(_, v) => steps.push(Step::Eval(v)),
                                    ObjEntry::Computed(k, v) => {
                                        steps.push(Step::Eval(v));
                                        steps.push(Step::Eval(k));
                                    }
                                    ObjEntry::Getter(k, v) | ObjEntry::Setter(k, v) => {
                                        steps.push(Step::Eval(v));
                                        if let ObjKey::Computed(ke) = k {
                                            steps.push(Step::Eval(ke));
                                        }
                                    }
                                }
                            }
                        }
                        Expr::ArrayBuild { elements } => {
                            for elem in elements.iter().rev() {
                                match elem {
                                    ArrayElem::Item(ex) | ArrayElem::Spread(ex) => {
                                        steps.push(Step::Eval(ex));
                                    }
                                }
                            }
                        }
                        Expr::Fallback { operands, .. } => {
                            for opnd in operands.iter().rev() {
                                steps.push(Step::Eval(opnd));
                            }
                        }
                        _ => {}
                    }
                }
                Step::Finish(e) => {
                    let built = match e {
                        Expr::PropName {
                            name, dot_legal, ..
                        } => Expr::PropName {
                            object: Box::new(pop_expr(&mut vals)),
                            name: name.clone(),
                            dot_legal: *dot_legal,
                        },
                        Expr::PrivateLoad { name, .. } => Expr::PrivateLoad {
                            object: Box::new(pop_expr(&mut vals)),
                            name: name.clone(),
                        },
                        Expr::PrivateTest { name, .. } => Expr::PrivateTest {
                            object: Box::new(pop_expr(&mut vals)),
                            name: name.clone(),
                        },
                        Expr::PropIndex { .. } => {
                            let index = Box::new(pop_expr(&mut vals));
                            let object = Box::new(pop_expr(&mut vals));
                            Expr::PropIndex { object, index }
                        }
                        Expr::PropDyn { .. } => {
                            let key = Box::new(pop_expr(&mut vals));
                            let object = Box::new(pop_expr(&mut vals));
                            Expr::PropDyn { object, key }
                        }
                        Expr::SuperProp { name, key: Some(_) } => Expr::SuperProp {
                            name: name.clone(),
                            key: Some(Box::new(pop_expr(&mut vals))),
                        },
                        Expr::Call {
                            this, args, kind, ..
                        } => {
                            let start = vals.len().saturating_sub(args.len());
                            let cloned_args = vals.split_off(start);
                            let cloned_this = this.as_ref().map(|_| Box::new(pop_expr(&mut vals)));
                            let cloned_callee = Box::new(pop_expr(&mut vals));
                            Expr::Call {
                                callee: cloned_callee,
                                this: cloned_this,
                                args: cloned_args,
                                kind: *kind,
                            }
                        }
                        Expr::DynamicImport { .. } => Expr::DynamicImport {
                            specifier: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::Unary { op, .. } => Expr::Unary {
                            op: *op,
                            operand: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::Delete { .. } => Expr::Delete {
                            target: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::Binary { op, .. } => {
                            let right = Box::new(pop_expr(&mut vals));
                            let left = Box::new(pop_expr(&mut vals));
                            Expr::Binary {
                                op: *op,
                                left,
                                right,
                            }
                        }
                        Expr::Compare { op, .. } => {
                            let right = Box::new(pop_expr(&mut vals));
                            let left = Box::new(pop_expr(&mut vals));
                            Expr::Compare {
                                op: *op,
                                left,
                                right,
                            }
                        }
                        Expr::Closure {
                            body,
                            name,
                            kind,
                            captures,
                        } => {
                            let start = vals.len().saturating_sub(captures.len());
                            let mut drain = vals.drain(start..);
                            let mut out_caps = Vec::with_capacity(captures.len());
                            for (cname, _) in captures {
                                out_caps.push((
                                    cname.clone(),
                                    drain.next().unwrap_or(Expr::SuperMarker),
                                ));
                            }
                            drop(drain);
                            Expr::Closure {
                                body: *body,
                                name: name.clone(),
                                kind: *kind,
                                captures: out_caps,
                            }
                        }
                        Expr::Class {
                            ctor,
                            name,
                            heritage: Some(_),
                            members,
                            member_attrs,
                            sendable,
                        } => Expr::Class {
                            ctor: *ctor,
                            name: name.clone(),
                            heritage: Some(Box::new(pop_expr(&mut vals))),
                            members: *members,
                            member_attrs: member_attrs.clone(),
                            sendable: *sendable,
                        },
                        Expr::Yield { .. } => Expr::Yield {
                            value: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::YieldStar { .. } => Expr::YieldStar {
                            value: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::Await { uncaught, .. } => Expr::Await {
                            value: Box::new(pop_expr(&mut vals)),
                            uncaught: *uncaught,
                        },
                        Expr::Iter { op, status, .. } => Expr::Iter {
                            op: *op,
                            obj: Box::new(pop_expr(&mut vals)),
                            status: *status,
                        },
                        Expr::CreateGenerator { .. } => Expr::CreateGenerator {
                            func: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::GeneratorDriver { resume, .. } => Expr::GeneratorDriver {
                            resume: *resume,
                            genobj: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::AsyncDriver { resolve, .. } => Expr::AsyncDriver {
                            resolve: *resolve,
                            value: Box::new(pop_expr(&mut vals)),
                        },
                        Expr::TaggedTemplate { quasis, exprs, .. } => {
                            let start = vals.len().saturating_sub(exprs.len());
                            let cloned_exprs = vals.split_off(start);
                            let cloned_tag = Box::new(pop_expr(&mut vals));
                            Expr::TaggedTemplate {
                                tag: cloned_tag,
                                quasis: quasis.clone(),
                                exprs: cloned_exprs,
                            }
                        }
                        Expr::IterResultObj { .. } => {
                            let done = Box::new(pop_expr(&mut vals));
                            let value = Box::new(pop_expr(&mut vals));
                            Expr::IterResultObj { value, done }
                        }
                        Expr::CopyDataProps { .. } => {
                            let src = Box::new(pop_expr(&mut vals));
                            let dst = Box::new(pop_expr(&mut vals));
                            Expr::CopyDataProps { dst, src }
                        }
                        Expr::SetObjectWithProto { .. } => {
                            let proto = Box::new(pop_expr(&mut vals));
                            let obj = Box::new(pop_expr(&mut vals));
                            Expr::SetObjectWithProto { obj, proto }
                        }
                        Expr::AsyncGeneratorResolve { .. } => {
                            let done = Box::new(pop_expr(&mut vals));
                            let value = Box::new(pop_expr(&mut vals));
                            let genobj = Box::new(pop_expr(&mut vals));
                            Expr::AsyncGeneratorResolve {
                                genobj,
                                value,
                                done,
                            }
                        }
                        Expr::ArraySpread { .. } => {
                            let src = Box::new(pop_expr(&mut vals));
                            let index = Box::new(pop_expr(&mut vals));
                            let dst = Box::new(pop_expr(&mut vals));
                            Expr::ArraySpread { dst, index, src }
                        }
                        Expr::RestObject { excluded, .. } => {
                            let start = vals.len().saturating_sub(excluded.len());
                            let cloned_ex = vals.split_off(start);
                            let cloned_obj = Box::new(pop_expr(&mut vals));
                            Expr::RestObject {
                                obj: cloned_obj,
                                excluded: cloned_ex,
                            }
                        }
                        Expr::DefineGetterSetter { .. } => {
                            let setter = Box::new(pop_expr(&mut vals));
                            let getter = Box::new(pop_expr(&mut vals));
                            let key = Box::new(pop_expr(&mut vals));
                            let obj = Box::new(pop_expr(&mut vals));
                            Expr::DefineGetterSetter {
                                obj,
                                key,
                                getter,
                                setter,
                            }
                        }
                        Expr::ObjectBuild { entries } => {
                            let total: usize = entries
                                .iter()
                                .map(|ent| match ent {
                                    ObjEntry::Computed(_, _)
                                    | ObjEntry::Getter(ObjKey::Computed(_), _)
                                    | ObjEntry::Setter(ObjKey::Computed(_), _) => 2,
                                    _ => 1,
                                })
                                .sum();
                            let start = vals.len().saturating_sub(total);
                            let mut drain = vals.drain(start..);
                            let mut next_val = || drain.next().unwrap_or(Expr::SuperMarker);
                            let mut out_entries = Vec::with_capacity(entries.len());
                            for ent in entries {
                                let built_ent = match ent {
                                    ObjEntry::KeyValue(k, _) => {
                                        ObjEntry::KeyValue(k.clone(), next_val())
                                    }
                                    ObjEntry::Computed(_, _) => {
                                        let k = next_val();
                                        let v = next_val();
                                        ObjEntry::Computed(k, v)
                                    }
                                    ObjEntry::Spread(_) => ObjEntry::Spread(next_val()),
                                    ObjEntry::Proto(_) => ObjEntry::Proto(next_val()),
                                    ObjEntry::Method(m, _) => {
                                        ObjEntry::Method(m.clone(), next_val())
                                    }
                                    ObjEntry::Getter(ObjKey::Name(n), _) => {
                                        ObjEntry::Getter(ObjKey::Name(n.clone()), next_val())
                                    }
                                    ObjEntry::Getter(ObjKey::Computed(_), _) => {
                                        let ke = Box::new(next_val());
                                        let v = next_val();
                                        ObjEntry::Getter(ObjKey::Computed(ke), v)
                                    }
                                    ObjEntry::Setter(ObjKey::Name(n), _) => {
                                        ObjEntry::Setter(ObjKey::Name(n.clone()), next_val())
                                    }
                                    ObjEntry::Setter(ObjKey::Computed(_), _) => {
                                        let ke = Box::new(next_val());
                                        let v = next_val();
                                        ObjEntry::Setter(ObjKey::Computed(ke), v)
                                    }
                                };
                                out_entries.push(built_ent);
                            }
                            drop(drain);
                            Expr::ObjectBuild {
                                entries: out_entries,
                            }
                        }
                        Expr::ArrayBuild { elements } => {
                            let start = vals.len().saturating_sub(elements.len());
                            let mut drain = vals.drain(start..);
                            let mut out_elems = Vec::with_capacity(elements.len());
                            for elem in elements {
                                let v = drain.next().unwrap_or(Expr::SuperMarker);
                                out_elems.push(match elem {
                                    ArrayElem::Item(_) => ArrayElem::Item(v),
                                    ArrayElem::Spread(_) => ArrayElem::Spread(v),
                                });
                            }
                            drop(drain);
                            Expr::ArrayBuild {
                                elements: out_elems,
                            }
                        }
                        Expr::Fallback { op, note, operands } => {
                            let start = vals.len().saturating_sub(operands.len());
                            let cloned_ops = vals.split_off(start);
                            Expr::Fallback {
                                op,
                                note,
                                operands: cloned_ops,
                            }
                        }
                        _ => clone_flat_expr(e).unwrap_or(Expr::SuperMarker),
                    };
                    vals.push(built);
                }
            }
        }
        pop_expr(&mut vals)
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        fn cmp_expr_step<'a>(
            a: &'a Expr,
            b: &'a Expr,
            stack: &mut Vec<(&'a Expr, &'a Expr)>,
        ) -> bool {
            match (a, b) {
                (Expr::Lit(x), Expr::Lit(y)) => x == y,
                (Expr::Ident(x), Expr::Ident(y)) => x == y,
                (
                    Expr::Temp {
                        value: vx,
                        name: nx,
                    },
                    Expr::Temp {
                        value: vy,
                        name: ny,
                    },
                ) => vx == vy && nx == ny,
                (
                    Expr::PropName {
                        object: ox,
                        name: nx,
                        dot_legal: dx,
                    },
                    Expr::PropName {
                        object: oy,
                        name: ny,
                        dot_legal: dy,
                    },
                ) => {
                    if dx != dy || nx != ny {
                        return false;
                    }
                    stack.push((ox, oy));
                    true
                }
                (
                    Expr::PropIndex {
                        object: ox,
                        index: ix,
                    },
                    Expr::PropIndex {
                        object: oy,
                        index: iy,
                    },
                ) => {
                    stack.push((ix, iy));
                    stack.push((ox, oy));
                    true
                }
                (
                    Expr::PropDyn {
                        object: ox,
                        key: kx,
                    },
                    Expr::PropDyn {
                        object: oy,
                        key: ky,
                    },
                ) => {
                    stack.push((kx, ky));
                    stack.push((ox, oy));
                    true
                }
                (
                    Expr::PrivateLoad {
                        object: ox,
                        name: nx,
                    },
                    Expr::PrivateLoad {
                        object: oy,
                        name: ny,
                    },
                )
                | (
                    Expr::PrivateTest {
                        object: ox,
                        name: nx,
                    },
                    Expr::PrivateTest {
                        object: oy,
                        name: ny,
                    },
                ) => {
                    if nx != ny {
                        return false;
                    }
                    stack.push((ox, oy));
                    true
                }
                (Expr::SuperProp { name: nx, key: kx }, Expr::SuperProp { name: ny, key: ky }) => {
                    match (kx, ky) {
                        (None, None) => nx == ny,
                        (Some(kx), Some(ky)) if nx == ny => {
                            stack.push((kx, ky));
                            true
                        }
                        _ => false,
                    }
                }
                (
                    Expr::Call {
                        callee: cx,
                        this: tx,
                        args: ax,
                        kind: kx,
                    },
                    Expr::Call {
                        callee: cy,
                        this: ty,
                        args: ay,
                        kind: ky,
                    },
                ) => {
                    if kx != ky || ax.len() != ay.len() || tx.is_some() != ty.is_some() {
                        return false;
                    }
                    for (x, y) in ax.iter().zip(ay.iter()).rev() {
                        stack.push((x, y));
                    }
                    if let (Some(tx), Some(ty)) = (tx, ty) {
                        stack.push((tx, ty));
                    }
                    stack.push((cx, cy));
                    true
                }
                (Expr::SuperMarker, Expr::SuperMarker)
                | (Expr::NewTarget, Expr::NewTarget)
                | (Expr::GlobalThis, Expr::GlobalThis)
                | (Expr::Arguments, Expr::Arguments) => true,
                (Expr::DynamicImport { specifier: sx }, Expr::DynamicImport { specifier: sy }) => {
                    stack.push((sx, sy));
                    true
                }
                (
                    Expr::Unary {
                        op: ox,
                        operand: px,
                    },
                    Expr::Unary {
                        op: oy,
                        operand: py,
                    },
                ) => {
                    if ox != oy {
                        return false;
                    }
                    stack.push((px, py));
                    true
                }
                (Expr::Delete { target: tx }, Expr::Delete { target: ty }) => {
                    stack.push((tx, ty));
                    true
                }
                (
                    Expr::Binary {
                        op: ox,
                        left: lx,
                        right: rx,
                    },
                    Expr::Binary {
                        op: oy,
                        left: ly,
                        right: ry,
                    },
                ) => {
                    if ox != oy {
                        return false;
                    }
                    stack.push((rx, ry));
                    stack.push((lx, ly));
                    true
                }
                (
                    Expr::Compare {
                        op: ox,
                        left: lx,
                        right: rx,
                    },
                    Expr::Compare {
                        op: oy,
                        left: ly,
                        right: ry,
                    },
                ) => {
                    if ox != oy {
                        return false;
                    }
                    stack.push((rx, ry));
                    stack.push((lx, ly));
                    true
                }
                (
                    Expr::RegExp {
                        pattern: px,
                        flags: fx,
                    },
                    Expr::RegExp {
                        pattern: py,
                        flags: fy,
                    },
                ) => px == py && fx == fy,
                (Expr::ObjectLit { entries: ex }, Expr::ObjectLit { entries: ey }) => ex == ey,
                (Expr::ArrayLit { elements: ex }, Expr::ArrayLit { elements: ey }) => ex == ey,
                (
                    Expr::Closure {
                        body: bx,
                        name: nx,
                        kind: kx,
                        captures: cx,
                    },
                    Expr::Closure {
                        body: by,
                        name: ny,
                        kind: ky,
                        captures: cy,
                    },
                ) => {
                    if bx != by || kx != ky || nx != ny || cx.len() != cy.len() {
                        return false;
                    }
                    for ((cnx, cvx), (cny, cvy)) in cx.iter().zip(cy.iter()).rev() {
                        if cnx != cny {
                            return false;
                        }
                        stack.push((cvx, cvy));
                    }
                    true
                }
                (
                    Expr::Class {
                        ctor: cx,
                        name: nx,
                        heritage: hx,
                        members: mx,
                        member_attrs: max,
                        sendable: sx,
                    },
                    Expr::Class {
                        ctor: cy,
                        name: ny,
                        heritage: hy,
                        members: my,
                        member_attrs: may,
                        sendable: sy,
                    },
                ) => {
                    if cx != cy
                        || mx != my
                        || sx != sy
                        || nx != ny
                        || max != may
                        || hx.is_some() != hy.is_some()
                    {
                        return false;
                    }
                    if let (Some(hx), Some(hy)) = (hx, hy) {
                        stack.push((hx, hy));
                    }
                    true
                }
                (Expr::Yield { value: vx }, Expr::Yield { value: vy })
                | (Expr::YieldStar { value: vx }, Expr::YieldStar { value: vy })
                | (Expr::CreateGenerator { func: vx }, Expr::CreateGenerator { func: vy }) => {
                    stack.push((vx, vy));
                    true
                }
                (
                    Expr::Await {
                        value: vx,
                        uncaught: ux,
                    },
                    Expr::Await {
                        value: vy,
                        uncaught: uy,
                    },
                ) => {
                    if ux != uy {
                        return false;
                    }
                    stack.push((vx, vy));
                    true
                }
                (Expr::SelfFunction(x), Expr::SelfFunction(y)) => x == y,
                (Expr::RestArgs { start_index: x }, Expr::RestArgs { start_index: y }) => x == y,
                (
                    Expr::TemplateObject {
                        raw: rx,
                        cooked: cx,
                    },
                    Expr::TemplateObject {
                        raw: ry,
                        cooked: cy,
                    },
                ) => rx == ry && cx == cy,
                (
                    Expr::TaggedTemplate {
                        tag: tx,
                        quasis: qx,
                        exprs: ex,
                    },
                    Expr::TaggedTemplate {
                        tag: ty,
                        quasis: qy,
                        exprs: ey,
                    },
                ) => {
                    if qx != qy || ex.len() != ey.len() {
                        return false;
                    }
                    for (x, y) in ex.iter().zip(ey.iter()).rev() {
                        stack.push((x, y));
                    }
                    stack.push((tx, ty));
                    true
                }
                (
                    Expr::IterResultObj {
                        value: vx,
                        done: dx,
                    },
                    Expr::IterResultObj {
                        value: vy,
                        done: dy,
                    },
                )
                | (
                    Expr::CopyDataProps { dst: vx, src: dx },
                    Expr::CopyDataProps { dst: vy, src: dy },
                )
                | (
                    Expr::SetObjectWithProto { obj: vx, proto: dx },
                    Expr::SetObjectWithProto { obj: vy, proto: dy },
                ) => {
                    stack.push((dx, dy));
                    stack.push((vx, vy));
                    true
                }
                (
                    Expr::Iter {
                        op: ox,
                        obj: bx,
                        status: sx,
                    },
                    Expr::Iter {
                        op: oy,
                        obj: by,
                        status: sy,
                    },
                ) => {
                    if ox != oy || sx != sy {
                        return false;
                    }
                    stack.push((bx, by));
                    true
                }
                (
                    Expr::GeneratorDriver {
                        resume: rx,
                        genobj: gx,
                    },
                    Expr::GeneratorDriver {
                        resume: ry,
                        genobj: gy,
                    },
                )
                | (
                    Expr::AsyncDriver {
                        resolve: rx,
                        value: gx,
                    },
                    Expr::AsyncDriver {
                        resolve: ry,
                        value: gy,
                    },
                ) => {
                    if rx != ry {
                        return false;
                    }
                    stack.push((gx, gy));
                    true
                }
                (
                    Expr::AsyncGeneratorResolve {
                        genobj: ax,
                        value: bx,
                        done: cx,
                    },
                    Expr::AsyncGeneratorResolve {
                        genobj: ay,
                        value: by,
                        done: cy,
                    },
                )
                | (
                    Expr::ArraySpread {
                        dst: ax,
                        index: bx,
                        src: cx,
                    },
                    Expr::ArraySpread {
                        dst: ay,
                        index: by,
                        src: cy,
                    },
                ) => {
                    stack.push((cx, cy));
                    stack.push((bx, by));
                    stack.push((ax, ay));
                    true
                }
                (
                    Expr::RestObject {
                        obj: ox,
                        excluded: ex,
                    },
                    Expr::RestObject {
                        obj: oy,
                        excluded: ey,
                    },
                ) => {
                    if ex.len() != ey.len() {
                        return false;
                    }
                    for (x, y) in ex.iter().zip(ey.iter()).rev() {
                        stack.push((x, y));
                    }
                    stack.push((ox, oy));
                    true
                }
                (
                    Expr::DefineGetterSetter {
                        obj: ox,
                        key: kx,
                        getter: gx,
                        setter: sx,
                    },
                    Expr::DefineGetterSetter {
                        obj: oy,
                        key: ky,
                        getter: gy,
                        setter: sy,
                    },
                ) => {
                    stack.push((sx, sy));
                    stack.push((gx, gy));
                    stack.push((kx, ky));
                    stack.push((ox, oy));
                    true
                }
                (Expr::ModuleNamespace { index: x }, Expr::ModuleNamespace { index: y }) => x == y,
                (Expr::ObjectBuild { entries: ex }, Expr::ObjectBuild { entries: ey }) => {
                    if ex.len() != ey.len() {
                        return false;
                    }
                    for (x, y) in ex.iter().zip(ey.iter()).rev() {
                        match (x, y) {
                            (ObjEntry::KeyValue(kx, vx), ObjEntry::KeyValue(ky, vy)) => {
                                if kx != ky {
                                    return false;
                                }
                                stack.push((vx, vy));
                            }
                            (ObjEntry::Computed(kx, vx), ObjEntry::Computed(ky, vy)) => {
                                stack.push((vx, vy));
                                stack.push((kx, ky));
                            }
                            (ObjEntry::Spread(vx), ObjEntry::Spread(vy))
                            | (ObjEntry::Proto(vx), ObjEntry::Proto(vy)) => stack.push((vx, vy)),
                            (ObjEntry::Method(mx, vx), ObjEntry::Method(my, vy)) => {
                                if mx != my {
                                    return false;
                                }
                                stack.push((vx, vy));
                            }
                            (
                                ObjEntry::Getter(ObjKey::Name(nx), vx),
                                ObjEntry::Getter(ObjKey::Name(ny), vy),
                            )
                            | (
                                ObjEntry::Setter(ObjKey::Name(nx), vx),
                                ObjEntry::Setter(ObjKey::Name(ny), vy),
                            ) => {
                                if nx != ny {
                                    return false;
                                }
                                stack.push((vx, vy));
                            }
                            (
                                ObjEntry::Getter(ObjKey::Computed(kx), vx),
                                ObjEntry::Getter(ObjKey::Computed(ky), vy),
                            )
                            | (
                                ObjEntry::Setter(ObjKey::Computed(kx), vx),
                                ObjEntry::Setter(ObjKey::Computed(ky), vy),
                            ) => {
                                stack.push((vx, vy));
                                stack.push((kx, ky));
                            }
                            _ => return false,
                        }
                    }
                    true
                }
                (Expr::ArrayBuild { elements: ex }, Expr::ArrayBuild { elements: ey }) => {
                    if ex.len() != ey.len() {
                        return false;
                    }
                    for (x, y) in ex.iter().zip(ey.iter()).rev() {
                        match (x, y) {
                            (ArrayElem::Item(vx), ArrayElem::Item(vy))
                            | (ArrayElem::Spread(vx), ArrayElem::Spread(vy)) => {
                                stack.push((vx, vy));
                            }
                            _ => return false,
                        }
                    }
                    true
                }
                (
                    Expr::Fallback {
                        op: ox,
                        note: nx,
                        operands: px,
                    },
                    Expr::Fallback {
                        op: oy,
                        note: ny,
                        operands: py,
                    },
                ) => {
                    if ox != oy || nx != ny || px.len() != py.len() {
                        return false;
                    }
                    for (x, y) in px.iter().zip(py.iter()).rev() {
                        stack.push((x, y));
                    }
                    true
                }
                _ => false,
            }
        }

        let mut stack: Vec<(&Expr, &Expr)> = Vec::new();
        if !cmp_expr_step(self, other, &mut stack) {
            return false;
        }
        while let Some((x, y)) = stack.pop() {
            if !cmp_expr_step(x, y, &mut stack) {
                return false;
            }
        }
        true
    }
}

impl Eq for Lit {}
impl Eq for Expr {}

impl Drop for ObjKey {
    fn drop(&mut self) {
        let mut stack: Vec<Expr> = Vec::new();
        drain_obj_key_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_expr_children(&mut cur, &mut stack);
        }
    }
}

impl Drop for ObjEntry {
    fn drop(&mut self) {
        let mut stack: Vec<Expr> = Vec::new();
        drain_obj_entry_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_expr_children(&mut cur, &mut stack);
        }
    }
}

impl Drop for ArrayElem {
    fn drop(&mut self) {
        let mut stack: Vec<Expr> = Vec::new();
        drain_array_elem_children(self, &mut stack);
        while let Some(mut cur) = stack.pop() {
            drain_expr_children(&mut cur, &mut stack);
        }
    }
}

impl Clone for ObjKey {
    fn clone(&self) -> Self {
        match self {
            ObjKey::Name(n) => ObjKey::Name(n.clone()),
            ObjKey::Computed(e) => ObjKey::Computed(Box::new((**e).clone())),
        }
    }
}

impl Clone for ObjEntry {
    fn clone(&self) -> Self {
        match self {
            ObjEntry::KeyValue(k, v) => ObjEntry::KeyValue(k.clone(), v.clone()),
            ObjEntry::Computed(k, v) => ObjEntry::Computed(k.clone(), v.clone()),
            ObjEntry::Spread(v) => ObjEntry::Spread(v.clone()),
            ObjEntry::Proto(v) => ObjEntry::Proto(v.clone()),
            ObjEntry::Method(n, v) => ObjEntry::Method(n.clone(), v.clone()),
            ObjEntry::Getter(k, v) => ObjEntry::Getter(k.clone(), v.clone()),
            ObjEntry::Setter(k, v) => ObjEntry::Setter(k.clone(), v.clone()),
        }
    }
}

impl Clone for ArrayElem {
    fn clone(&self) -> Self {
        match self {
            ArrayElem::Item(e) => ArrayElem::Item(e.clone()),
            ArrayElem::Spread(e) => ArrayElem::Spread(e.clone()),
        }
    }
}

impl PartialEq for ObjKey {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ObjKey::Name(a), ObjKey::Name(b)) => a == b,
            (ObjKey::Computed(a), ObjKey::Computed(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ObjKey {}

impl PartialEq for ObjEntry {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ObjEntry::KeyValue(ka, va), ObjEntry::KeyValue(kb, vb)) => ka == kb && va == vb,
            (ObjEntry::Computed(ka, va), ObjEntry::Computed(kb, vb)) => ka == kb && va == vb,
            (ObjEntry::Spread(a), ObjEntry::Spread(b))
            | (ObjEntry::Proto(a), ObjEntry::Proto(b)) => a == b,
            (ObjEntry::Method(na, va), ObjEntry::Method(nb, vb)) => na == nb && va == vb,
            (ObjEntry::Getter(ka, va), ObjEntry::Getter(kb, vb))
            | (ObjEntry::Setter(ka, va), ObjEntry::Setter(kb, vb)) => ka == kb && va == vb,
            _ => false,
        }
    }
}

impl Eq for ObjEntry {}

impl PartialEq for ArrayElem {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ArrayElem::Item(a), ArrayElem::Item(b))
            | (ArrayElem::Spread(a), ArrayElem::Spread(b)) => a == b,
            _ => false,
        }
    }
}

impl Eq for ArrayElem {}

enum LitDebugTask<'a> {
    Lit(&'a Lit),
    Raw(&'static str),
}

fn fmt_lit_debug_iter(root: &Lit, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut stack = vec![LitDebugTask::Lit(root)];
    while let Some(task) = stack.pop() {
        match task {
            LitDebugTask::Raw(s) => f.write_str(s)?,
            LitDebugTask::Lit(lit) => match lit {
                Lit::Undefined => f.write_str("Undefined")?,
                Lit::Hole => f.write_str("Hole")?,
                Lit::Null => f.write_str("Null")?,
                Lit::Bool(b) => write!(f, "Bool({b:?})")?,
                Lit::Number(n) => write!(f, "Number({n:?})")?,
                Lit::Int64(n) => write!(f, "Int64({n:?})")?,
                Lit::UInt64(n) => write!(f, "UInt64({n:?})")?,
                Lit::String(s) => write!(f, "String({s:?})")?,
                Lit::Utf16(u) => write!(f, "Utf16({u:?})")?,
                Lit::BigInt(s) => write!(f, "BigInt({s:?})")?,
                Lit::MethodRef(id) => write!(f, "MethodRef({id:?})")?,
                Lit::Array(items) => {
                    f.write_str("Array([")?;
                    stack.push(LitDebugTask::Raw("])"));
                    for (idx, it) in items.iter().enumerate().rev() {
                        stack.push(LitDebugTask::Lit(it));
                        if idx > 0 {
                            stack.push(LitDebugTask::Raw(", "));
                        }
                    }
                }
                Lit::Object(entries) => {
                    f.write_str("Object([")?;
                    stack.push(LitDebugTask::Raw("])"));
                    for (idx, (k, v)) in entries.iter().enumerate().rev() {
                        stack.push(LitDebugTask::Raw(")"));
                        stack.push(LitDebugTask::Lit(v));
                        stack.push(LitDebugTask::Raw(", "));
                        stack.push(LitDebugTask::Lit(k));
                        stack.push(LitDebugTask::Raw("("));
                        if idx > 0 {
                            stack.push(LitDebugTask::Raw(", "));
                        }
                    }
                }
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for Lit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt_lit_debug_iter(self, f)
    }
}

enum ExprDebugTask<'a> {
    Expr(&'a Expr),
    ObjEntry(&'a ObjEntry),
    ObjKey(&'a ObjKey),
    ArrayElem(&'a ArrayElem),
    Lit(&'a Lit),
    Raw(&'static str),
    Owned(String),
}

#[allow(
    clippy::too_many_lines,
    reason = "iterative heap-workstack Debug formatter across all Expr/ObjEntry/ObjKey/ArrayElem variants"
)]
fn run_expr_debug_tasks(
    mut stack: Vec<ExprDebugTask<'_>>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    while let Some(task) = stack.pop() {
        match task {
            ExprDebugTask::Raw(s) => f.write_str(s)?,
            ExprDebugTask::Owned(s) => f.write_str(&s)?,
            ExprDebugTask::Lit(l) => fmt_lit_debug_iter(l, f)?,
            ExprDebugTask::ObjKey(k) => match k {
                ObjKey::Name(n) => write!(f, "Name({n:?})")?,
                ObjKey::Computed(e) => {
                    f.write_str("Computed(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(e));
                }
            },
            ExprDebugTask::ObjEntry(entry) => match entry {
                ObjEntry::KeyValue(k, v) => {
                    f.write_str("KeyValue(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                    stack.push(ExprDebugTask::Raw(", "));
                    stack.push(ExprDebugTask::Lit(k));
                }
                ObjEntry::Computed(k, v) => {
                    f.write_str("Computed(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                    stack.push(ExprDebugTask::Raw(", "));
                    stack.push(ExprDebugTask::Expr(k));
                }
                ObjEntry::Spread(v) => {
                    f.write_str("Spread(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                }
                ObjEntry::Proto(v) => {
                    f.write_str("Proto(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                }
                ObjEntry::Method(n, v) => {
                    write!(f, "Method({n:?}, ")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                }
                ObjEntry::Getter(k, v) => {
                    f.write_str("Getter(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                    stack.push(ExprDebugTask::Raw(", "));
                    stack.push(ExprDebugTask::ObjKey(k));
                }
                ObjEntry::Setter(k, v) => {
                    f.write_str("Setter(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(v));
                    stack.push(ExprDebugTask::Raw(", "));
                    stack.push(ExprDebugTask::ObjKey(k));
                }
            },
            ExprDebugTask::ArrayElem(el) => match el {
                ArrayElem::Item(e) => {
                    f.write_str("Item(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(e));
                }
                ArrayElem::Spread(e) => {
                    f.write_str("Spread(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Expr(e));
                }
            },
            ExprDebugTask::Expr(expr) => match expr {
                Expr::Lit(l) => {
                    f.write_str("Lit(")?;
                    stack.push(ExprDebugTask::Raw(")"));
                    stack.push(ExprDebugTask::Lit(l));
                }
                Expr::Ident(s) => write!(f, "Ident({s:?})")?,
                Expr::Temp { value, name } => {
                    write!(f, "Temp {{ value: {value:?}, name: {name:?} }}")?;
                }
                Expr::PropName {
                    object,
                    name,
                    dot_legal,
                } => {
                    f.write_str("PropName { object: ")?;
                    stack.push(ExprDebugTask::Owned(format!(
                        ", name: {name:?}, dot_legal: {dot_legal:?} }}"
                    )));
                    stack.push(ExprDebugTask::Expr(object));
                }
                Expr::PropIndex { object, index } => {
                    f.write_str("PropIndex { object: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(index));
                    stack.push(ExprDebugTask::Raw(", index: "));
                    stack.push(ExprDebugTask::Expr(object));
                }
                Expr::PropDyn { object, key } => {
                    f.write_str("PropDyn { object: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(key));
                    stack.push(ExprDebugTask::Raw(", key: "));
                    stack.push(ExprDebugTask::Expr(object));
                }
                Expr::PrivateLoad { object, name } => {
                    f.write_str("PrivateLoad { object: ")?;
                    stack.push(ExprDebugTask::Owned(format!(", name: {name:?} }}")));
                    stack.push(ExprDebugTask::Expr(object));
                }
                Expr::PrivateTest { object, name } => {
                    f.write_str("PrivateTest { object: ")?;
                    stack.push(ExprDebugTask::Owned(format!(", name: {name:?} }}")));
                    stack.push(ExprDebugTask::Expr(object));
                }
                Expr::SuperProp { name, key } => match key {
                    Some(k) => {
                        write!(f, "SuperProp {{ name: {name:?}, key: Some(")?;
                        stack.push(ExprDebugTask::Raw(") }"));
                        stack.push(ExprDebugTask::Expr(k));
                    }
                    None => write!(f, "SuperProp {{ name: {name:?}, key: None }}")?,
                },
                Expr::Call {
                    callee,
                    this,
                    args,
                    kind,
                } => {
                    f.write_str("Call { callee: ")?;
                    stack.push(ExprDebugTask::Owned(format!("], kind: {kind:?} }}")));
                    for (idx, a) in args.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Expr(a));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                    match this {
                        Some(t) => {
                            stack.push(ExprDebugTask::Raw("), args: ["));
                            stack.push(ExprDebugTask::Expr(t));
                            stack.push(ExprDebugTask::Raw(", this: Some("));
                        }
                        None => stack.push(ExprDebugTask::Raw(", this: None, args: [")),
                    }
                    stack.push(ExprDebugTask::Expr(callee));
                }
                Expr::SuperMarker => f.write_str("SuperMarker")?,
                Expr::DynamicImport { specifier } => {
                    f.write_str("DynamicImport { specifier: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(specifier));
                }
                Expr::Unary { op, operand } => {
                    write!(f, "Unary {{ op: {op:?}, operand: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(operand));
                }
                Expr::Delete { target } => {
                    f.write_str("Delete { target: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(target));
                }
                Expr::Binary { op, left, right } => {
                    write!(f, "Binary {{ op: {op:?}, left: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(right));
                    stack.push(ExprDebugTask::Raw(", right: "));
                    stack.push(ExprDebugTask::Expr(left));
                }
                Expr::Compare { op, left, right } => {
                    write!(f, "Compare {{ op: {op:?}, left: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(right));
                    stack.push(ExprDebugTask::Raw(", right: "));
                    stack.push(ExprDebugTask::Expr(left));
                }
                Expr::RegExp { pattern, flags } => {
                    write!(f, "RegExp {{ pattern: {pattern:?}, flags: {flags:?} }}")?;
                }
                Expr::ObjectLit { entries } => {
                    f.write_str("ObjectLit { entries: [")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, (k, v)) in entries.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Raw(")"));
                        stack.push(ExprDebugTask::Lit(v));
                        stack.push(ExprDebugTask::Raw(", "));
                        stack.push(ExprDebugTask::Lit(k));
                        stack.push(ExprDebugTask::Raw("("));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
                Expr::ArrayLit { elements } => {
                    f.write_str("ArrayLit { elements: [")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, el) in elements.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Lit(el));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
                Expr::Closure {
                    body,
                    name,
                    kind,
                    captures,
                } => {
                    write!(
                        f,
                        "Closure {{ body: {body:?}, name: {name:?}, kind: {kind:?}, captures: ["
                    )?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, (cn, cv)) in captures.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Raw(")"));
                        stack.push(ExprDebugTask::Expr(cv));
                        stack.push(ExprDebugTask::Owned(format!("({cn:?}, ")));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
                Expr::Class {
                    ctor,
                    name,
                    heritage,
                    members,
                    member_attrs,
                    sendable,
                } => {
                    write!(f, "Class {{ ctor: {ctor:?}, name: {name:?}, heritage: ")?;
                    let tail = format!(
                        ", members: {members:?}, member_attrs: {member_attrs:?}, sendable: {sendable:?} }}"
                    );
                    match heritage {
                        Some(h) => {
                            f.write_str("Some(")?;
                            stack.push(ExprDebugTask::Owned(format!("){tail}")));
                            stack.push(ExprDebugTask::Expr(h));
                        }
                        None => write!(f, "None{tail}")?,
                    }
                }
                Expr::Yield { value } => {
                    f.write_str("Yield { value: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(value));
                }
                Expr::YieldStar { value } => {
                    f.write_str("YieldStar { value: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(value));
                }
                Expr::Await { value, uncaught } => {
                    f.write_str("Await { value: ")?;
                    stack.push(ExprDebugTask::Owned(format!(", uncaught: {uncaught:?} }}")));
                    stack.push(ExprDebugTask::Expr(value));
                }
                Expr::NewTarget => f.write_str("NewTarget")?,
                Expr::GlobalThis => f.write_str("GlobalThis")?,
                Expr::SelfFunction(s) => write!(f, "SelfFunction({s:?})")?,
                Expr::Arguments => f.write_str("Arguments")?,
                Expr::RestArgs { start_index } => {
                    write!(f, "RestArgs {{ start_index: {start_index:?} }}")?;
                }
                Expr::TemplateObject { raw, cooked } => {
                    write!(f, "TemplateObject {{ raw: {raw:?}, cooked: {cooked:?} }}")?;
                }
                Expr::TaggedTemplate { tag, quasis, exprs } => {
                    f.write_str("TaggedTemplate { tag: ")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, ex) in exprs.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Expr(ex));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                    stack.push(ExprDebugTask::Owned(format!(
                        ", quasis: {quasis:?}, exprs: ["
                    )));
                    stack.push(ExprDebugTask::Expr(tag));
                }
                Expr::IterResultObj { value, done } => {
                    f.write_str("IterResultObj { value: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(done));
                    stack.push(ExprDebugTask::Raw(", done: "));
                    stack.push(ExprDebugTask::Expr(value));
                }
                Expr::Iter { op, obj, status } => {
                    write!(f, "Iter {{ op: {op:?}, obj: ")?;
                    stack.push(ExprDebugTask::Owned(format!(", status: {status:?} }}")));
                    stack.push(ExprDebugTask::Expr(obj));
                }
                Expr::CreateGenerator { func } => {
                    f.write_str("CreateGenerator { func: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(func));
                }
                Expr::GeneratorDriver { resume, genobj } => {
                    write!(f, "GeneratorDriver {{ resume: {resume:?}, genobj: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(genobj));
                }
                Expr::AsyncDriver { resolve, value } => {
                    write!(f, "AsyncDriver {{ resolve: {resolve:?}, value: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(value));
                }
                Expr::AsyncGeneratorResolve {
                    genobj,
                    value,
                    done,
                } => {
                    f.write_str("AsyncGeneratorResolve { genobj: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(done));
                    stack.push(ExprDebugTask::Raw(", done: "));
                    stack.push(ExprDebugTask::Expr(value));
                    stack.push(ExprDebugTask::Raw(", value: "));
                    stack.push(ExprDebugTask::Expr(genobj));
                }
                Expr::CopyDataProps { dst, src } => {
                    f.write_str("CopyDataProps { dst: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(src));
                    stack.push(ExprDebugTask::Raw(", src: "));
                    stack.push(ExprDebugTask::Expr(dst));
                }
                Expr::SetObjectWithProto { obj, proto } => {
                    f.write_str("SetObjectWithProto { obj: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(proto));
                    stack.push(ExprDebugTask::Raw(", proto: "));
                    stack.push(ExprDebugTask::Expr(obj));
                }
                Expr::ArraySpread { dst, index, src } => {
                    f.write_str("ArraySpread { dst: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(src));
                    stack.push(ExprDebugTask::Raw(", src: "));
                    stack.push(ExprDebugTask::Expr(index));
                    stack.push(ExprDebugTask::Raw(", index: "));
                    stack.push(ExprDebugTask::Expr(dst));
                }
                Expr::RestObject { obj, excluded } => {
                    f.write_str("RestObject { obj: ")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, ex) in excluded.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Expr(ex));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                    stack.push(ExprDebugTask::Raw(", excluded: ["));
                    stack.push(ExprDebugTask::Expr(obj));
                }
                Expr::DefineGetterSetter {
                    obj,
                    key,
                    getter,
                    setter,
                } => {
                    f.write_str("DefineGetterSetter { obj: ")?;
                    stack.push(ExprDebugTask::Raw(" }"));
                    stack.push(ExprDebugTask::Expr(setter));
                    stack.push(ExprDebugTask::Raw(", setter: "));
                    stack.push(ExprDebugTask::Expr(getter));
                    stack.push(ExprDebugTask::Raw(", getter: "));
                    stack.push(ExprDebugTask::Expr(key));
                    stack.push(ExprDebugTask::Raw(", key: "));
                    stack.push(ExprDebugTask::Expr(obj));
                }
                Expr::ModuleNamespace { index } => {
                    write!(f, "ModuleNamespace {{ index: {index:?} }}")?;
                }
                Expr::ObjectBuild { entries } => {
                    f.write_str("ObjectBuild { entries: [")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, ent) in entries.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::ObjEntry(ent));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
                Expr::ArrayBuild { elements } => {
                    f.write_str("ArrayBuild { elements: [")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, el) in elements.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::ArrayElem(el));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
                Expr::Fallback { op, note, operands } => {
                    write!(f, "Fallback {{ op: {op:?}, note: {note:?}, operands: [")?;
                    stack.push(ExprDebugTask::Raw("] }"));
                    for (idx, opnd) in operands.iter().enumerate().rev() {
                        stack.push(ExprDebugTask::Expr(opnd));
                        if idx > 0 {
                            stack.push(ExprDebugTask::Raw(", "));
                        }
                    }
                }
            },
        }
    }
    Ok(())
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        run_expr_debug_tasks(vec![ExprDebugTask::Expr(self)], f)
    }
}

impl std::fmt::Debug for ObjEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        run_expr_debug_tasks(vec![ExprDebugTask::ObjEntry(self)], f)
    }
}

impl std::fmt::Debug for ObjKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        run_expr_debug_tasks(vec![ExprDebugTask::ObjKey(self)], f)
    }
}

impl std::fmt::Debug for ArrayElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        run_expr_debug_tasks(vec![ExprDebugTask::ArrayElem(self)], f)
    }
}
