//! Textual IR dump, similar to Hermes IR printer.
//!
//! Example output:
//! ```text
//! function foo(2) {
//!   %bb_0:
//!     %v_0 = LiteralNumber 42.0
//!     %v_1 = LiteralString "hello"
//!     %v_2 = BinaryOp Add %v_0, %v_1
//!     CondBranch %v_2, %bb_1, %bb_2
//!   %bb_1:                           ; preds: %bb_0
//!     Return %v_0
//!   %bb_2:                           ; preds: %bb_0
//!     Return %v_1
//! }
//! ```

use std::fmt;

use crate::entity::FuncId;
use crate::inst::{BinOp, CallKind, InstData, PropKind, UnOp};
use crate::module::Module;

/// Display wrapper for printing a single function.
pub struct DisplayFunc<'a> {
    pub module: &'a Module,
    pub func: FuncId,
}

/// Display wrapper for printing the entire module.
pub struct DisplayModule<'a> {
    pub module: &'a Module,
}

impl Module {
    pub fn display_func(&self, func: FuncId) -> DisplayFunc<'_> {
        DisplayFunc { module: self, func }
    }

    pub fn display(&self) -> DisplayModule<'_> {
        DisplayModule { module: self }
    }
}

impl fmt::Display for DisplayModule<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.module;
        for (i, _) in m.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            write!(f, "{}", m.display_func(FuncId::from_index(i)))?;
        }
        Ok(())
    }
}

fn write_prop(f: &mut fmt::Formatter<'_>, m: &Module, key: &PropKind) -> fmt::Result {
    match key {
        PropKind::ByName(s) => write!(f, "[\"{}\"]", m.strings.get(*s)),
        PropKind::ByValue(v) => write!(f, "[{v}]"),
        PropKind::ByIndex(i) => write!(f, "[#{i}]"),
    }
}

fn write_binop(f: &mut fmt::Formatter<'_>, op: &BinOp) -> fmt::Result {
    let s = match op {
        BinOp::Add => "Add",
        BinOp::Sub => "Sub",
        BinOp::Mul => "Mul",
        BinOp::Div => "Div",
        BinOp::Mod => "Mod",
        BinOp::Exp => "Exp",
        BinOp::Eq => "Eq",
        BinOp::NotEq => "NotEq",
        BinOp::StrictEq => "StrictEq",
        BinOp::StrictNotEq => "StrictNotEq",
        BinOp::Less => "Less",
        BinOp::LessEq => "LessEq",
        BinOp::Greater => "Greater",
        BinOp::GreaterEq => "GreaterEq",
        BinOp::Shl => "Shl",
        BinOp::Shr => "Shr",
        BinOp::Ashr => "Ashr",
        BinOp::BitAnd => "BitAnd",
        BinOp::BitOr => "BitOr",
        BinOp::BitXor => "BitXor",
        BinOp::In => "In",
        BinOp::InstanceOf => "InstanceOf",
    };
    write!(f, "{s}")
}

fn write_unop(f: &mut fmt::Formatter<'_>, op: &UnOp) -> fmt::Result {
    let s = match op {
        UnOp::Minus => "Minus",
        UnOp::BitNot => "BitNot",
        UnOp::LogicalNot => "LogicalNot",
        UnOp::Inc => "Inc",
        UnOp::Dec => "Dec",
        UnOp::TypeOf => "TypeOf",
        UnOp::ToNumber => "ToNumber",
        UnOp::ToNumeric => "ToNumeric",
        UnOp::Void => "Void",
    };
    write!(f, "{s}")
}

fn write_inst_data(f: &mut fmt::Formatter<'_>, m: &Module, data: &InstData) -> fmt::Result {
    match data {
        // Literals
        InstData::LiteralUndefined => write!(f, "LiteralUndefined"),
        InstData::LiteralNull => write!(f, "LiteralNull"),
        InstData::LiteralBool(b) => write!(f, "LiteralBool {b}"),
        InstData::LiteralNumber(n) => write!(f, "LiteralNumber {n}"),
        InstData::LiteralString(s) => write!(f, "LiteralString \"{}\"", m.strings.get(*s)),
        InstData::LiteralNaN => write!(f, "LiteralNaN"),
        InstData::LiteralInfinity => write!(f, "LiteralInfinity"),
        InstData::LiteralHole => write!(f, "LiteralHole"),

        // Binary / Unary
        InstData::BinaryOp { op, left, right } => {
            write!(f, "BinaryOp ")?;
            write_binop(f, op)?;
            write!(f, " {left}, {right}")
        }
        InstData::UnaryOp { op, operand } => {
            write!(f, "UnaryOp ")?;
            write_unop(f, op)?;
            write!(f, " {operand}")
        }
        InstData::IsTrue { operand } => write!(f, "IsTrue {operand}"),
        InstData::IsFalse { operand } => write!(f, "IsFalse {operand}"),

        // Object creation
        InstData::CreateEmptyObject => write!(f, "CreateEmptyObject"),
        InstData::CreateEmptyArray => write!(f, "CreateEmptyArray"),
        InstData::CreateObjectWithBuffer { literal_array } => {
            write!(f, "CreateObjectWithBuffer #{literal_array}")
        }
        InstData::CreateArrayWithBuffer { literal_array } => {
            write!(f, "CreateArrayWithBuffer #{literal_array}")
        }
        InstData::CreateRegExp { pattern, flags } => {
            write!(
                f,
                "CreateRegExp /{}/{}",
                m.strings.get(*pattern),
                m.strings.get(*flags)
            )
        }
        InstData::CreateObjectWithExcludedKeys { obj, keys } => {
            write!(f, "CreateObjectWithExcludedKeys {obj}")?;
            for k in keys {
                write!(f, ", {k}")?;
            }
            Ok(())
        }

        // Property access
        InstData::LoadProperty { object, key } => {
            write!(f, "LoadProperty {object}")?;
            write_prop(f, m, key)
        }
        InstData::StoreProperty { object, key, value } => {
            write!(f, "StoreProperty {object}")?;
            write_prop(f, m, key)?;
            write!(f, ", {value}")
        }
        InstData::StoreOwnProperty { object, key, value } => {
            write!(f, "StoreOwnProperty {object}")?;
            write_prop(f, m, key)?;
            write!(f, ", {value}")
        }
        InstData::DeleteProperty { object, key } => {
            write!(f, "DeleteProperty {object}, {key}")
        }
        InstData::LoadSuperProperty { key } => {
            write!(f, "LoadSuperProperty")?;
            write_prop(f, m, key)
        }
        InstData::StoreSuperProperty { key, value } => {
            write!(f, "StoreSuperProperty")?;
            write_prop(f, m, key)?;
            write!(f, ", {value}")
        }

        // Global variables
        InstData::LoadGlobalVar { name } => {
            write!(f, "LoadGlobalVar \"{}\"", m.strings.get(*name))
        }
        InstData::StoreGlobalVar { name, value } => {
            write!(f, "StoreGlobalVar \"{}\", {value}", m.strings.get(*name))
        }
        InstData::TryLoadGlobalByName { name } => {
            write!(f, "TryLoadGlobalByName \"{}\"", m.strings.get(*name))
        }
        InstData::TryStoreGlobalByName { name, value } => {
            write!(
                f,
                "TryStoreGlobalByName \"{}\", {value}",
                m.strings.get(*name)
            )
        }

        // Lexical variables
        InstData::LoadLexVar { level, slot } => write!(f, "LoadLexVar {level}, {slot}"),
        InstData::StoreLexVar { level, slot, value } => {
            write!(f, "StoreLexVar {level}, {slot}, {value}")
        }

        // Module variables
        InstData::LoadLocalModuleVar { index } => write!(f, "LoadLocalModuleVar {index}"),
        InstData::LoadExternalModuleVar { index } => write!(f, "LoadExternalModuleVar {index}"),
        InstData::StoreModuleVar { index, value } => {
            write!(f, "StoreModuleVar {index}, {value}")
        }
        InstData::GetModuleNamespace { index } => write!(f, "GetModuleNamespace {index}"),
        InstData::DynamicImport { specifier } => write!(f, "DynamicImport {specifier}"),

        // Scope management
        InstData::NewLexEnv { num_vars } => write!(f, "NewLexEnv {num_vars}"),
        InstData::NewLexEnvWithName {
            num_vars,
            scope_name,
        } => {
            write!(
                f,
                "NewLexEnvWithName {num_vars}, \"{}\"",
                m.strings.get(*scope_name)
            )
        }
        InstData::PopLexEnv => write!(f, "PopLexEnv"),

        // Function operations
        InstData::DefineFunc { method_id, length } => {
            write!(f, "DefineFunc \"{}\", {length}", m.strings.get(*method_id))
        }
        InstData::DefineMethod {
            method_id,
            length,
            home_object,
        } => {
            write!(
                f,
                "DefineMethod \"{}\", {length}, {home_object}",
                m.strings.get(*method_id)
            )
        }
        InstData::DefineClassWithBuffer {
            method_id,
            literal_array,
            base,
        } => {
            write!(
                f,
                "DefineClassWithBuffer \"{}\", #{literal_array}, {base}",
                m.strings.get(*method_id)
            )
        }
        InstData::DefineGetterSetterByValue {
            obj,
            key,
            getter,
            setter,
        } => {
            write!(
                f,
                "DefineGetterSetterByValue {obj}, {key}, {getter}, {setter}"
            )
        }

        // Calls
        InstData::Call { kind, callee, args } => {
            let kind_str = match kind {
                CallKind::Call => "Call",
                CallKind::CallThis => "CallThis",
                CallKind::SuperCall => "SuperCall",
                CallKind::SuperCallArrow => "SuperCallArrow",
                CallKind::SuperCallSpread => "SuperCallSpread",
                CallKind::Apply => "Apply",
            };
            write!(f, "{kind_str} {callee}")?;
            for a in args {
                write!(f, ", {a}")?;
            }
            Ok(())
        }

        // Special value loaders
        InstData::LoadThis => write!(f, "LoadThis"),
        InstData::LoadNewTarget => write!(f, "LoadNewTarget"),
        InstData::LoadGlobalObject => write!(f, "LoadGlobalObject"),
        InstData::LoadFunction => write!(f, "LoadFunction"),
        InstData::GetUnmappedArgs => write!(f, "GetUnmappedArgs"),
        InstData::CopyRestArgs { start_index } => write!(f, "CopyRestArgs {start_index}"),

        // Iterators
        InstData::GetIterator { obj } => write!(f, "GetIterator {obj}"),
        InstData::GetAsyncIterator { obj } => write!(f, "GetAsyncIterator {obj}"),
        InstData::GetPropIterator { obj } => write!(f, "GetPropIterator {obj}"),
        InstData::CloseIterator { iterator } => write!(f, "CloseIterator {iterator}"),

        // Generator / Async
        InstData::CreateGeneratorObj { func } => write!(f, "CreateGeneratorObj {func}"),
        InstData::SuspendGenerator { value } => write!(f, "SuspendGenerator {value}"),
        InstData::ResumeGenerator => write!(f, "ResumeGenerator"),
        InstData::AsyncFunctionEnter => write!(f, "AsyncFunctionEnter"),
        InstData::AsyncFunctionAwaitUncaught { value } => {
            write!(f, "AsyncFunctionAwaitUncaught {value}")
        }
        InstData::AsyncFunctionResolve { value } => write!(f, "AsyncFunctionResolve {value}"),
        InstData::AsyncFunctionReject { value } => write!(f, "AsyncFunctionReject {value}"),
        InstData::CreateIterResultObj { value, done } => {
            write!(f, "CreateIterResultObj {value}, {done}")
        }

        // Exception handling
        InstData::Throw { value } => write!(f, "Throw {value}"),
        InstData::ThrowIfNotObject { value } => write!(f, "ThrowIfNotObject {value}"),
        InstData::ThrowConstAssignment { name } => {
            write!(f, "ThrowConstAssignment \"{}\"", m.strings.get(*name))
        }
        InstData::ThrowUndefinedIfHole { name, value } => {
            write!(
                f,
                "ThrowUndefinedIfHole \"{}\", {value}",
                m.strings.get(*name)
            )
        }
        InstData::ThrowIfSuperNotCorrectCall { value } => {
            write!(f, "ThrowIfSuperNotCorrectCall {value}")
        }
        InstData::ThrowNotExists => write!(f, "ThrowNotExists"),
        InstData::ThrowPatternNonCoercible => write!(f, "ThrowPatternNonCoercible"),
        InstData::ThrowDeleteSuperProperty => write!(f, "ThrowDeleteSuperProperty"),

        // Phi
        InstData::Phi { entries } => {
            write!(f, "Phi")?;
            for (i, (block, val)) in entries.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, " [{block}: {val}]")?;
            }
            Ok(())
        }

        // Terminators
        InstData::Branch { dest } => write!(f, "Branch {dest}"),
        InstData::CondBranch {
            cond,
            true_dest,
            false_dest,
        } => {
            write!(f, "CondBranch {cond}, {true_dest}, {false_dest}")
        }
        InstData::Return { value: Some(v) } => write!(f, "Return {v}"),
        InstData::Return { value: None } => write!(f, "Return"),
        InstData::Unreachable => write!(f, "Unreachable"),

        // Debug
        InstData::Debugger => write!(f, "Debugger"),
    }
}

impl fmt::Display for DisplayFunc<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let m = self.module;
        let func = m.func(self.func);
        writeln!(
            f,
            "function {}({}) {{",
            m.strings.get(func.name),
            func.param_count
        )?;
        for &bb in &func.blocks {
            let block = m.block(bb);
            // Block header with predecessors
            if block.preds.is_empty() {
                writeln!(f, "  {bb}:")?;
            } else {
                let preds: Vec<String> = block.preds.iter().map(|p| p.to_string()).collect();
                writeln!(f, "  {bb}:    ; preds: {}", preds.join(", "))?;
            }
            // Phi instructions
            for &inst_id in &block.phis {
                let inst = m.inst(inst_id);
                write!(f, "    ")?;
                if let Some(val) = inst.result {
                    write!(f, "{val} = ")?;
                }
                write_inst_data(f, m, &inst.data)?;
                writeln!(f)?;
            }
            // Regular instructions
            for &inst_id in &block.insts {
                let inst = m.inst(inst_id);
                write!(f, "    ")?;
                if let Some(val) = inst.result {
                    write!(f, "{val} = ")?;
                }
                write_inst_data(f, m, &inst.data)?;
                writeln!(f)?;
            }
        }
        writeln!(f, "}}")
    }
}

#[cfg(test)]
mod tests {
    use crate::builder::IRBuilder;
    use crate::inst::{BinOp, InstData};
    use crate::module::Module;
    use crate::types::IrType;
    use abcd_file::{FileType, FunctionKind, Version};

    #[test]
    fn display_simple_function() {
        let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
        let func = IRBuilder::create_function(&mut module, "add", FunctionKind::Function, 2);
        let mut b = IRBuilder::new(&mut module, func);

        let p0 = b.create_func_param(0, IrType::default());
        let p1 = b.create_func_param(1, IrType::default());
        let sum = b.emit_val(
            InstData::BinaryOp {
                op: BinOp::Add,
                left: p0,
                right: p1,
            },
            IrType::default(),
        );
        b.emit_void(InstData::Return { value: Some(sum) });

        let output = format!("{}", module.display_func(func));
        assert!(output.contains("function add(2)"));
        assert!(output.contains("BinaryOp Add %v_0, %v_1"));
        assert!(output.contains("Return %v_2"));
    }

    #[test]
    fn display_branch_with_preds() {
        let mut module = Module::new(Version::new(12, 0, 6, 0), FileType::Dynamic);
        let func = IRBuilder::create_function(&mut module, "test", FunctionKind::Function, 0);
        let mut b = IRBuilder::new(&mut module, func);

        let cond = b.emit_val(InstData::LiteralBool(true), IrType::default());
        let bb1 = b.create_block();
        let bb2 = b.create_block();
        let entry = b.current_block();
        b.add_predecessor(bb1, entry);
        b.add_predecessor(bb2, entry);
        b.emit_void(InstData::CondBranch {
            cond,
            true_dest: bb1,
            false_dest: bb2,
        });

        b.set_insert_block(bb1);
        b.emit_void(InstData::Return { value: None });

        b.set_insert_block(bb2);
        b.emit_void(InstData::Return { value: None });

        let output = format!("{}", module.display_func(func));
        assert!(output.contains("; preds: %bb_0"));
    }
}
