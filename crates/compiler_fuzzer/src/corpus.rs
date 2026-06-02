//! Mutation fuzzing over the real `program_*.py` corpus.
//!
//! The structured generator explores a designed space; mutating *hand-written* programs reaches
//! shapes it never would. We load the compiler's own `program_*.py` test data (the ones whose
//! only import is `snark_lib`, so they compile from raw source), apply small source mutations,
//! and compile each mutant in a bounded subprocess. A mutant may well be rejected — that is
//! fine; we only flag panics / hangs / crashes (goal #1).

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use crate::rng::Rng;
use crate::subprocess::{SubprocessOutcome, compile_in_subprocess};
use crate::triage::{Finding, FindingKind};

/// Default location of the compiler's program corpus, relative to the repo root.
pub const DEFAULT_CORPUS_DIR: &str = "crates/lean_compiler/tests/test_data";

/// Load `program_*.py` sources that are self-contained (import only `snark_lib`, so the raw
/// source compiles without a file-relative import root).
#[must_use]
pub fn load_corpus(dir: &Path) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let Ok(entries) = fs::read_dir(dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        if !(name.starts_with("program_") && name.ends_with(".py")) {
            continue;
        }
        let Ok(src) = fs::read_to_string(&path) else {
            continue;
        };
        // Skip programs that import sibling files (can't be compiled from raw source).
        let imports_only_snark_lib = src
            .lines()
            .filter(|l| l.trim_start().starts_with("from ") || l.trim_start().starts_with("import "))
            .all(|l| l.contains("snark_lib"));
        if imports_only_snark_lib {
            out.push((name.to_string(), src));
        }
    }
    out.sort();
    out
}

/// How many times [`mutate`] re-rolls to avoid emitting a recursive `@inline`.
const MUTATE_RETRIES: usize = 16;

/// Apply one random small mutation to `src`, returning the mutant.
///
/// The result never contains a recursive `@inline` function (an unsupported
/// construct the compiler would try to inline forever — see the KNOWN LIMITATIONS
/// note in the simplifier). A line-duplication / shuffle can splice a call to an
/// inline function into that function's own body; if a mutation does, we re-roll.
/// Corpus programs never contain such a cycle, so the unmutated source is a safe
/// fallback if every re-roll happens to introduce one.
#[must_use]
pub fn mutate(src: &str, rng: &mut Rng) -> String {
    for _ in 0..MUTATE_RETRIES {
        let mutant = mutate_once(src, rng);
        if !has_recursive_inline(&mutant) {
            return mutant;
        }
    }
    src.to_string()
}

fn mutate_once(src: &str, rng: &mut Rng) -> String {
    let mut lines: Vec<String> = src.lines().map(str::to_string).collect();
    if lines.is_empty() {
        return src.to_string();
    }
    match rng.below(5) {
        0 => {
            // Delete a random line.
            let i = rng.below(lines.len());
            lines.remove(i);
        }
        1 => {
            // Duplicate a random line.
            let i = rng.below(lines.len());
            lines.insert(i, lines[i].clone());
        }
        2 => {
            // Swap two adjacent lines.
            if lines.len() >= 2 {
                let i = rng.below(lines.len() - 1);
                lines.swap(i, i + 1);
            }
        }
        3 => {
            // Perturb the first integer literal on a random line.
            let i = rng.below(lines.len());
            lines[i] = perturb_first_int(&lines[i], rng);
        }
        _ => {
            // Duplicate a random indented block line into another position (shuffles structure).
            let i = rng.below(lines.len());
            let j = rng.below(lines.len());
            let l = lines[i].clone();
            lines.insert(j, l);
        }
    }
    lines.join("\n")
}

fn perturb_first_int(line: &str, rng: &mut Rng) -> String {
    let bytes = line.as_bytes();
    let Some(start) = bytes.iter().position(u8::is_ascii_digit) else {
        return line.to_string();
    };
    let mut end = start;
    while end < bytes.len() && bytes[end].is_ascii_digit() {
        end += 1;
    }
    let replacement = match rng.below(4) {
        0 => "0".to_string(),
        1 => "1".to_string(),
        2 => "65537".to_string(),
        _ => format!("{}", rng.next_u32()),
    };
    format!("{}{}{}", &line[..start], replacement, &line[end..])
}

/// Whether `src` defines a recursive `@inline` function: a self-call, or a cycle of
/// `@inline` functions calling one another. The compiler expands `@inline` calls
/// eagerly, so such a cycle never terminates — generated programs must avoid it.
#[must_use]
pub fn has_recursive_inline(src: &str) -> bool {
    // Parse top-level functions. A function is `def NAME(...)` at column 0, possibly
    // preceded by an `@inline` decorator; its body is the following indented / blank
    // lines, up to the next top-level construct.
    struct Func {
        name: String,
        inline: bool,
        body: String,
    }
    let mut funcs: Vec<Func> = Vec::new();
    let mut pending_inline = false;
    let mut cur: Option<usize> = None;
    for line in src.lines() {
        let at_col0 = !line.starts_with([' ', '\t']);
        let trimmed = line.trim_start();
        if at_col0 && trimmed == "@inline" {
            pending_inline = true;
            cur = None;
        } else if at_col0 && trimmed.starts_with("def ") {
            let name = trimmed[4..].split('(').next().unwrap_or("").trim().to_string();
            funcs.push(Func {
                name,
                inline: pending_inline,
                body: String::new(),
            });
            cur = Some(funcs.len() - 1);
            pending_inline = false;
        } else if at_col0 && !trimmed.is_empty() {
            cur = None;
            pending_inline = false;
        } else if let Some(c) = cur {
            funcs[c].body.push_str(line);
            funcs[c].body.push('\n');
        }
    }

    let inline_names: Vec<&str> = funcs.iter().filter(|f| f.inline).map(|f| f.name.as_str()).collect();
    if inline_names.is_empty() {
        return false;
    }
    // Inline-call graph: F -> M when inline F's body calls inline M.
    let edges: std::collections::BTreeMap<&str, Vec<&str>> = funcs
        .iter()
        .filter(|f| f.inline)
        .map(|f| {
            let callees = inline_names
                .iter()
                .copied()
                .filter(|m| body_calls(&f.body, m))
                .collect();
            (f.name.as_str(), callees)
        })
        .collect();

    // DFS: a back-edge to a function still on the current path (incl. a self-edge) is a cycle.
    fn has_cycle<'a>(
        node: &'a str,
        edges: &std::collections::BTreeMap<&'a str, Vec<&'a str>>,
        on_path: &mut Vec<&'a str>,
        done: &mut std::collections::BTreeSet<&'a str>,
    ) -> bool {
        on_path.push(node);
        for &next in edges.get(node).into_iter().flatten() {
            if on_path.contains(&next) || (!done.contains(next) && has_cycle(next, edges, on_path, done)) {
                return true;
            }
        }
        on_path.pop();
        done.insert(node);
        false
    }
    let mut done = std::collections::BTreeSet::new();
    edges
        .keys()
        .any(|&n| !done.contains(n) && has_cycle(n, &edges, &mut Vec::new(), &mut done))
}

/// Whether `body` contains a call `name(` — `name` as a whole identifier, directly
/// followed (modulo spaces) by `(`.
fn body_calls(body: &str, name: &str) -> bool {
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let bytes = body.as_bytes();
    let nb = name.as_bytes();
    let mut i = 0;
    while i + nb.len() <= bytes.len() {
        let word_start = i == 0 || !is_ident(bytes[i - 1]);
        if &bytes[i..i + nb.len()] == nb && word_start {
            let mut j = i + nb.len();
            if !(j < bytes.len() && is_ident(bytes[j])) {
                while j < bytes.len() && (bytes[j] == b' ' || bytes[j] == b'\t') {
                    j += 1;
                }
                if j < bytes.len() && bytes[j] == b'(' {
                    return true;
                }
            }
        }
        i += 1;
    }
    false
}

/// Run a mutation campaign: `iterations` mutants drawn from the corpus, each compiled in a
/// bounded subprocess. Returns a finding per crash.
#[must_use]
pub fn fuzz_corpus(
    bin: &Path,
    dir: &Path,
    start_seed: u64,
    iterations: u64,
    timeout: Duration,
    mem_limit: u64,
) -> Vec<Finding> {
    let corpus = load_corpus(dir);
    let mut findings = Vec::new();
    if corpus.is_empty() {
        return findings;
    }
    for k in 0..iterations {
        let seed = start_seed.wrapping_add(k);
        let mut rng = Rng::new(seed ^ 0x00C0_FFEE_C0DE_C0DE);
        let (name, src) = &corpus[rng.below(corpus.len())];
        let mutant = mutate(src, &mut rng);
        let outcome = match compile_in_subprocess(bin, &mutant, timeout, mem_limit) {
            Ok(o) => o,
            Err(_) => continue,
        };
        let (kind, what) = match &outcome {
            SubprocessOutcome::Compiled | SubprocessOutcome::Rejected => continue,
            SubprocessOutcome::Panicked(m) => (FindingKind::CompilerPanic, format!("panicked: {m}")),
            SubprocessOutcome::Timeout => (FindingKind::CompilerHang, "hung".to_string()),
            SubprocessOutcome::Crashed { signal, .. } => (FindingKind::CompilerCrash, format!("signal {signal}")),
            SubprocessOutcome::UnexpectedExit { code, .. } => (FindingKind::CompilerCrash, format!("exit {code}")),
        };
        findings.push(Finding::new(kind, seed, format!("mutant of {name}: {what}"), mutant));
    }
    findings
}

/// Convenience: resolve the default corpus dir relative to the current working directory.
#[must_use]
pub fn default_corpus_dir() -> PathBuf {
    PathBuf::from(DEFAULT_CORPUS_DIR)
}
