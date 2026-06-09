use crate::lexer::token::Token;
use crate::parser::syntax_kind::SyntaxKind;
use std::fmt::Write;

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Clone)]
pub struct SyntaxTree {
    pub kind: SyntaxKind,
    pub children: Vec<SyntaxChild>,
    /// Byte offset of the first token in this subtree (u32::MAX if empty).
    pub start: u32,
    /// Byte offset of the end of the last token in this subtree (0 if empty).
    pub end: u32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
#[derive(Clone)]
pub enum SyntaxChild {
    Token(Token),
    Tree(SyntaxTree),
}

// The CST nests one level per operator in a long chain, so a query like a
// thousands-element `IN` list expanded to `x = a OR x = b OR ...`, or a long
// `AND` predicate list, produces a tree thousands of levels deep. The compiler's
// derived drop glue recurses one frame per level and overflows the stack on such
// inputs (a ~500KB query is enough). Dismantle iteratively instead: hoist every
// descendant subtree into a flat work list and drop it there, so no SyntaxTree is
// ever dropped while it still owns nested Tree children. Token children carry no
// further trees, so they drop in place without recursing.
impl Drop for SyntaxTree {
    fn drop(&mut self) {
        let mut stack: Vec<SyntaxTree> = Vec::new();
        for child in std::mem::take(&mut self.children) {
            if let SyntaxChild::Tree(tree) = child {
                stack.push(tree);
            }
        }
        while let Some(mut tree) = stack.pop() {
            for child in std::mem::take(&mut tree.children) {
                if let SyntaxChild::Tree(subtree) = child {
                    stack.push(subtree);
                }
            }
            // `tree` drops here with its children already emptied, so this same
            // Drop impl re-runs as a no-op — no recursion.
        }
    }
}

impl SyntaxChild {
    pub fn is_token(&self) -> bool {
        matches!(self, SyntaxChild::Token(_))
    }

    pub fn is_tree(&self) -> bool {
        matches!(self, SyntaxChild::Tree(_))
    }

    pub fn get_token_with_kind(&self, kind: SyntaxKind) -> Option<&Token> {
        match self {
            SyntaxChild::Token(token) if token.kind == kind => Some(token),
            _ => None,
        }
    }

    pub fn get_tree_with_kind(&self, kind: SyntaxKind) -> Option<&SyntaxTree> {
        match self {
            SyntaxChild::Tree(tree) if tree.kind == kind => Some(tree),
            _ => None,
        }
    }
}

#[allow(dead_code)]
pub trait SyntaxChildExt {
    fn get_token_with_kind(&self, kind: SyntaxKind) -> Option<&Token>;
    fn get_tree_with_kind(&self, kind: SyntaxKind) -> Option<&SyntaxTree>;
}

impl SyntaxChildExt for Option<&SyntaxChild> {
    fn get_token_with_kind(&self, kind: SyntaxKind) -> Option<&Token> {
        match self {
            Some(SyntaxChild::Token(token)) if token.kind == kind => Some(token),
            _ => None,
        }
    }

    fn get_tree_with_kind(&self, kind: SyntaxKind) -> Option<&SyntaxTree> {
        match self {
            Some(SyntaxChild::Tree(tree)) if tree.kind == kind => Some(tree),
            _ => None,
        }
    }
}

impl SyntaxTree {
    pub fn print(&self, buf: &mut String, level: usize, source: &str) {
        let indent = "  ".repeat(level);
        let _ = writeln!(buf, "{indent}{:?}", self.kind);
        for child in &self.children {
            match child {
                SyntaxChild::Token(token) => {
                    if token.kind == SyntaxKind::Whitespace {
                        continue;
                    }
                    let _ = writeln!(buf, "{indent}  '{}'", token.text(source));
                }
                SyntaxChild::Tree(tree) => tree.print(buf, level + 1, source),
            }
        }
        // Invariant: print always ends with a newline (from writeln above).
        // Use debug_assert to catch violations during development without
        // crashing production callers.
        debug_assert!(buf.ends_with('\n'));
    }
}
