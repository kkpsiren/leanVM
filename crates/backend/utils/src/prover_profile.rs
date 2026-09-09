//! Optional diagnostic hooks. No clock reads or allocations unless an observer is installed.
//! Observers must not re-enter proving, and must tolerate calls from worker threads.
use std::sync::OnceLock;

#[derive(Clone, Copy, Debug)]
pub enum ProverProfileEvent {
    Enter(&'static str, &'static str),
    Exit(&'static str, &'static str),
    Value(&'static str, &'static str, usize),
}

static OBSERVER: OnceLock<fn(ProverProfileEvent)> = OnceLock::new();

pub fn set_prover_profile_observer(observer: fn(ProverProfileEvent)) {
    OBSERVER.set(observer).expect("prover profile observer already installed");
}

/// Guard dimension calculations that would allocate or do other work without an observer.
#[inline]
pub fn prover_profile_enabled() -> bool {
    OBSERVER.get().is_some()
}

#[derive(Debug)]
pub struct ProverProfileSpan(Option<(&'static str, &'static str)>);

#[inline]
pub fn prover_profile_span(phase: &'static str, table: &'static str) -> ProverProfileSpan {
    if let Some(observer) = OBSERVER.get() {
        observer(ProverProfileEvent::Enter(phase, table));
        ProverProfileSpan(Some((phase, table)))
    } else {
        ProverProfileSpan(None)
    }
}

impl Drop for ProverProfileSpan {
    fn drop(&mut self) {
        if let Some((phase, table)) = self.0 {
            OBSERVER.get().unwrap()(ProverProfileEvent::Exit(phase, table));
        }
    }
}

#[inline]
pub fn prover_profile_value(kind: &'static str, table: &'static str, value: usize) {
    if let Some(observer) = OBSERVER.get() {
        observer(ProverProfileEvent::Value(kind, table, value));
    }
}
