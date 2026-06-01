//! Findings: what an oracle reports, plus reproducible serialization to disk.
//!
//! Every finding carries the seed and the full program source, so it replays exactly. Findings
//! with a witness also carry the offending buffers. Critical/High findings are real signals;
//! Info findings (e.g. an unexpected-but-still-rejecting error variant) are diagnostics.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use serde::Serialize;

/// How serious a finding is. Tests fail on `Critical`/`High`; `Info` is advisory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum Severity {
    Info,
    High,
    Critical,
}

/// The categories an oracle can report.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FindingKind {
    /// The compiler unwound (panicked) — always a bug.
    CompilerPanic,
    /// A witness that violates a check was accepted by the VM — the check was dropped.
    DroppedCheck,
    /// The honest witness was rejected (over-zealous check, miscompilation, or generator bug).
    HonestRunFailed,
    /// The VM panicked while running the honest witness.
    HonestRunPanicked,
    /// The VM panicked while running a violating witness.
    ViolationPanicked,
    /// A well-formed generated program was rejected by the compiler.
    CompileRejected,
    /// A check fired, but with an error variant inconsistent with its kind (possible
    /// non-isolated perturbation — diagnostic only).
    InconsistentVariant,
    /// Bytecode is missing the expected lowering of a check (structural oracle).
    MissingLowering,
    /// A semantics-preserving transform changed observable behaviour (metamorphic oracle).
    MetamorphicDivergence,
}

impl FindingKind {
    #[must_use]
    pub const fn default_severity(self) -> Severity {
        match self {
            Self::CompilerPanic | Self::DroppedCheck | Self::MissingLowering | Self::MetamorphicDivergence => {
                Severity::Critical
            }
            Self::HonestRunFailed | Self::HonestRunPanicked | Self::ViolationPanicked | Self::CompileRejected => {
                Severity::High
            }
            Self::InconsistentVariant => Severity::Info,
        }
    }

    #[must_use]
    pub const fn slug(self) -> &'static str {
        match self {
            Self::CompilerPanic => "compiler_panic",
            Self::DroppedCheck => "dropped_check",
            Self::HonestRunFailed => "honest_failed",
            Self::HonestRunPanicked => "honest_panicked",
            Self::ViolationPanicked => "violation_panicked",
            Self::CompileRejected => "compile_rejected",
            Self::InconsistentVariant => "inconsistent_variant",
            Self::MissingLowering => "missing_lowering",
            Self::MetamorphicDivergence => "metamorphic_divergence",
        }
    }
}

/// A single reproducible finding.
#[derive(Debug, Clone, Serialize)]
pub struct Finding {
    pub kind: FindingKind,
    pub severity: Severity,
    pub seed: u64,
    pub gadget: Option<usize>,
    pub check: Option<String>,
    pub detail: String,
    pub source: String,
    /// The witness buffers that reproduce the finding (canonical integers), if applicable.
    pub buffers: Option<Vec<Vec<u64>>>,
}

impl Finding {
    #[must_use]
    pub fn new(kind: FindingKind, seed: u64, detail: impl Into<String>, source: impl Into<String>) -> Self {
        Self {
            kind,
            severity: kind.default_severity(),
            seed,
            gadget: None,
            check: None,
            detail: detail.into(),
            source: source.into(),
            buffers: None,
        }
    }

    #[must_use]
    pub fn with_gadget(mut self, gadget: usize, check: impl Into<String>) -> Self {
        self.gadget = Some(gadget);
        self.check = Some(check.into());
        self
    }

    #[must_use]
    pub fn with_buffers(mut self, buffers: Vec<Vec<u64>>) -> Self {
        self.buffers = Some(buffers);
        self
    }

    /// A short one-line summary for console output.
    #[must_use]
    pub fn summary(&self) -> String {
        let g = self.gadget.map_or_else(String::new, |i| format!(" g{i}"));
        format!(
            "[{:?}/{:?}] seed={}{g}: {}",
            self.severity, self.kind, self.seed, self.detail
        )
    }

    fn file_stem(&self) -> String {
        match self.gadget {
            Some(i) => format!("{:020}_{}_g{i}", self.seed, self.kind.slug()),
            None => format!("{:020}_{}", self.seed, self.kind.slug()),
        }
    }

    /// Persist the finding under `dir` as a `.py` (the program) plus a `.json` (metadata +
    /// repro). Returns the path of the `.py`.
    pub fn write_to_dir(&self, dir: &Path) -> io::Result<PathBuf> {
        fs::create_dir_all(dir)?;
        let stem = self.file_stem();
        let py = dir.join(format!("{stem}.py"));
        let json = dir.join(format!("{stem}.json"));
        fs::write(&py, &self.source)?;
        fs::write(&json, serde_json::to_vec_pretty(self).expect("serialize finding"))?;
        Ok(py)
    }
}
