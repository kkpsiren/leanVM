//! A tiny indentation-aware source builder for emitting zkDSL.
//!
//! zkDSL blocks are Python-style (significant indentation; the parser treats a tab as four
//! spaces). The emitter always uses four-space indents and tracks the current depth so
//! generated programs parse without hand-managed whitespace.

/// Accumulates lines of zkDSL at a tracked indentation depth.
#[derive(Debug, Default)]
pub struct Emitter {
    lines: Vec<String>,
    depth: usize,
}

impl Emitter {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Emit one logical line at the current depth.
    pub fn line(&mut self, text: &str) {
        let mut s = String::with_capacity(self.depth * 4 + text.len());
        for _ in 0..self.depth {
            s.push_str("    ");
        }
        s.push_str(text);
        self.lines.push(s);
    }

    /// Emit a blank line (no indentation).
    pub fn blank(&mut self) {
        self.lines.push(String::new());
    }

    /// Increase indentation for the lines emitted by `body`.
    pub fn indented(&mut self, body: impl FnOnce(&mut Self)) {
        self.depth += 1;
        body(self);
        self.depth -= 1;
    }

    /// Finalize into a single source string (trailing newline included).
    #[must_use]
    pub fn finish(self) -> String {
        let mut s = self.lines.join("\n");
        s.push('\n');
        s
    }
}
