use crate::expr::Expr;

/// Statement nodes for decompiled code.
#[derive(Debug, Clone)]
pub enum Stmt {
    /// Expression statement: `expr;`
    Expr(Expr),
    /// Variable declaration: `let name = init;`
    Let { name: String, init: Option<Expr> },
    /// Const declaration: `const name = init;`
    Const { name: String, init: Expr },
    /// Assignment: `target = value;`
    Assign { target: Expr, value: Expr },
    /// Return statement: `return expr;`
    Return(Option<Expr>),
    /// Throw statement: `throw expr;`
    Throw(Expr),
    /// If statement.
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    /// While loop.
    While { cond: Expr, body: Vec<Stmt> },
    /// For-in loop.
    ForIn {
        binding: String,
        object: Expr,
        body: Vec<Stmt>,
    },
    /// For-of loop.
    ForOf {
        binding: String,
        iterable: Expr,
        body: Vec<Stmt>,
    },
    /// Try-catch-finally.
    TryCatch {
        try_body: Vec<Stmt>,
        catch_binding: Option<String>,
        catch_body: Vec<Stmt>,
        finally_body: Vec<Stmt>,
    },
    /// Switch statement.
    Switch {
        discriminant: Expr,
        cases: Vec<SwitchCase>,
        default: Vec<Stmt>,
    },
    /// Break.
    Break,
    /// Continue.
    Continue,
    /// Block of statements.
    Block(Vec<Stmt>),
    /// A comment (for undecompilable regions).
    Comment(String),
    /// Debugger statement.
    Debugger,
}

/// A single case in a switch statement.
#[derive(Debug, Clone)]
pub struct SwitchCase {
    pub test: Expr,
    pub body: Vec<Stmt>,
}
