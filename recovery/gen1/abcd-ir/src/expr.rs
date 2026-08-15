/// Expression tree nodes for decompiled code.
#[derive(Debug, Clone)]
pub enum Expr {
    /// Numeric literal (integer).
    NumberLit(f64),
    /// String literal.
    StringLit(String),
    /// Boolean literal.
    BoolLit(bool),
    /// `null`
    Null,
    /// `undefined`
    Undefined,
    /// A named variable (register or lexical).
    Var(String),
    /// `this`
    This,
    /// `new.target`
    NewTarget,
    /// Binary operation: `lhs op rhs`
    BinaryOp {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    /// Unary operation: `op expr`
    UnaryOp { op: UnOp, expr: Box<Expr> },
    /// `typeof expr`
    TypeOf(Box<Expr>),
    /// Property access: `obj.prop`
    MemberAccess { object: Box<Expr>, property: String },
    /// Computed property access: `obj[expr]`
    ComputedAccess { object: Box<Expr>, index: Box<Expr> },
    /// Function/method call: `callee(args...)`
    Call { callee: Box<Expr>, args: Vec<Expr> },
    /// `new Ctor(args...)`
    New { callee: Box<Expr>, args: Vec<Expr> },
    /// `super(args...)`
    SuperCall { args: Vec<Expr> },
    /// Array literal: `[a, b, c]`
    ArrayLit(Vec<Expr>),
    /// Object literal: `{ key: value, ... }`
    ObjectLit(Vec<(PropKey, Expr)>),
    /// Template literal (simplified as string concat for now)
    TemplateLit(Vec<Expr>),
    /// Conditional: `cond ? then : else`
    Conditional {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Spread: `...expr`
    Spread(Box<Expr>),
    /// `await expr`
    Await(Box<Expr>),
    /// `yield expr`
    Yield(Box<Expr>),
    /// Assignment: `lhs = rhs`
    Assign { target: Box<Expr>, value: Box<Expr> },
    /// Unresolved accumulator reference (internal, should be eliminated).
    Acc,
    /// Raw opcode we couldn't decompile.
    Unknown(String),
}

/// Object property key.
#[derive(Debug, Clone)]
pub enum PropKey {
    Ident(String),
    Computed(Expr),
}

/// Binary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Exp,
    Eq,
    NotEq,
    StrictEq,
    StrictNotEq,
    Lt,
    Gt,
    Le,
    Ge,
    And,
    Or,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    UShr,
    In,
    InstanceOf,
    NullishCoalesce,
}

/// Unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    BitNot,
    Void,
    Delete,
    Pos,
    Inc,
    Dec,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Exp => "**",
            BinOp::Eq => "==",
            BinOp::NotEq => "!=",
            BinOp::StrictEq => "===",
            BinOp::StrictNotEq => "!==",
            BinOp::Lt => "<",
            BinOp::Gt => ">",
            BinOp::Le => "<=",
            BinOp::Ge => ">=",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::UShr => ">>>",
            BinOp::In => "in",
            BinOp::InstanceOf => "instanceof",
            BinOp::NullishCoalesce => "??",
        };
        f.write_str(s)
    }
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            UnOp::Neg => "-",
            UnOp::Not => "!",
            UnOp::BitNot => "~",
            UnOp::Void => "void ",
            UnOp::Delete => "delete ",
            UnOp::Pos => "+",
            UnOp::Inc => "++",
            UnOp::Dec => "--",
        };
        f.write_str(s)
    }
}
