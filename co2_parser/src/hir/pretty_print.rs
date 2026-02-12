use itertools::Itertools;

use crate::hir::{Block, Expr, HirBody, HirCtxInterface, Stmt};

use super::{ExprKind, StmtKind};

trait HirPrint<C: HirCtxInterface> {
    fn print(&self, ctx: &HirBody<C>) -> String;
}

fn indent(x: String) -> String {
    x.lines().map(|l| format!("    {l}")).join("\n")
}

impl<C: HirCtxInterface> HirPrint<C> for Expr<C> {
    fn print(&self, _ctx: &HirBody<C>) -> String {
        match &self.kind {
            ExprKind::Lit(_) => todo!(),
            ExprKind::Local(_) => todo!(),
            ExprKind::Call(_, _) => todo!(),
            ExprKind::Binary(_, _, _) => todo!(),
            ExprKind::Unary(_, _) => todo!(),
            ExprKind::Assign(_, _) => todo!(),
            ExprKind::AssignWithBinOp(_, _, _, _, _) => todo!(),
            ExprKind::Field(_, _) => todo!(),
            ExprKind::PtrOffset(_, _) => todo!(),
            ExprKind::PtrDiff(_, _) => todo!(),
            ExprKind::AssignPtrOffset(_, _, _) => todo!(),
            ExprKind::Cast(_) => todo!(),
            ExprKind::InitializerList(_) => todo!(),
            ExprKind::Comma(_) => todo!(),
            ExprKind::OffsetOf => todo!(),
            ExprKind::Cond(_, _, _) => todo!(),
            ExprKind::GnuBlock(_) => todo!(),
            ExprKind::Empty => todo!(),
        }
    }
}

impl<C: HirCtxInterface> HirPrint<C> for Stmt<C> {
    fn print(&self, ctx: &HirBody<C>) -> String {
        match &self.kind {
            StmtKind::Block(block) => block.print(ctx),
            StmtKind::Expr(expr) => format!("{};", expr.print(ctx)),
            StmtKind::Decl(_) => todo!(),
            StmtKind::Ret(_) => todo!(),
            StmtKind::Label(_, _) => todo!(),
            StmtKind::Goto(_) => todo!(),
            StmtKind::If(_, _, _) => todo!(),
            StmtKind::Noop => todo!(),
        }
    }
}

impl<C: HirCtxInterface> HirPrint<C> for Block<C> {
    fn print(&self, ctx: &HirBody<C>) -> String {
        let inner = self.stmts.iter().map(|stmt| stmt.print(ctx)).join("\n");
        format!("{{\n{}\n}}", indent(inner))
    }
}

impl<C: HirCtxInterface> HirBody<C> {
    pub fn pretty_print(&self) -> String {
        self.root.print(self)
    }
}
