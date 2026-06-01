//! The campaign driver: generate program after program from consecutive seeds, run every
//! oracle, and collect findings. Single-threaded and fully deterministic — seed `s` always
//! produces the same program and the same verdict.

use std::path::PathBuf;

use crate::generators::{GenConfig, gen_program};
use crate::harness::StderrGag;
use crate::oracles;
use crate::rng::Rng;
use crate::triage::{Finding, Severity};

/// Configuration for a fuzzing campaign.
#[derive(Debug, Clone)]
pub struct CampaignConfig {
    /// First seed (inclusive). Successive iterations use `start_seed + k`.
    pub start_seed: u64,
    /// Number of programs to generate and test.
    pub iterations: u64,
    /// Program-shape knobs.
    pub gen_config: GenConfig,
    /// If set, write each finding's reproducer here.
    pub out_dir: Option<PathBuf>,
    /// Print a one-line summary per finding as it is discovered.
    pub verbose: bool,
    /// Stop the campaign as soon as a `Critical` finding appears.
    pub stop_on_critical: bool,
}

impl Default for CampaignConfig {
    fn default() -> Self {
        Self {
            start_seed: 0,
            iterations: 1000,
            gen_config: GenConfig::default(),
            out_dir: None,
            verbose: false,
            stop_on_critical: false,
        }
    }
}

/// The outcome of a campaign.
#[derive(Debug, Default)]
pub struct CampaignReport {
    pub iterations_run: u64,
    pub findings: Vec<Finding>,
}

impl CampaignReport {
    #[must_use]
    pub fn count(&self, severity: Severity) -> usize {
        self.findings.iter().filter(|f| f.severity == severity).count()
    }

    #[must_use]
    pub fn criticals(&self) -> usize {
        self.count(Severity::Critical)
    }

    #[must_use]
    pub fn highs(&self) -> usize {
        self.count(Severity::High)
    }

    /// Findings worth failing a CI run on (Critical or High).
    pub fn actionable(&self) -> impl Iterator<Item = &Finding> {
        self.findings.iter().filter(|f| f.severity >= Severity::High)
    }
}

/// Run a campaign to completion (or until a critical finding if `stop_on_critical`).
#[must_use]
pub fn run_campaign(cfg: &CampaignConfig) -> CampaignReport {
    // Gag the runner's per-error stderr trace for the whole campaign; reproducers and the
    // summary are written via stdout / the out_dir, both unaffected.
    let _gag = StderrGag::new();

    let mut report = CampaignReport::default();
    for k in 0..cfg.iterations {
        let seed = cfg.start_seed.wrapping_add(k);
        report.iterations_run += 1;

        let mut rng = Rng::new(seed);
        let prog = gen_program(&mut rng, &cfg.gen_config);
        let findings = oracles::evaluate(&prog, &mut rng, seed);

        let mut hit_critical = false;
        for f in findings {
            if f.severity == Severity::Critical {
                hit_critical = true;
            }
            if cfg.verbose {
                // Temporarily lift the gag so the summary reaches the real stderr-free stdout.
                println!("{}", f.summary());
            }
            if let Some(dir) = &cfg.out_dir
                && let Err(e) = f.write_to_dir(dir)
            {
                println!("warning: failed to write finding for seed {seed}: {e}");
            }
            report.findings.push(f);
        }

        if cfg.stop_on_critical && hit_critical {
            break;
        }
    }
    report
}
