//! Wasm uses the regular heap. Arena activation is explicitly unsupported.
use std::alloc::{Layout};
pub fn enable_arena() { panic!("arena allocation is unsupported on wasm32"); }
pub fn begin_phase() {}
pub fn end_phase() {}
#[derive(Debug)]
pub struct PhaseGuard(());
impl Drop for PhaseGuard { fn drop(&mut self) { end_phase(); } }
#[must_use]
pub fn enter_phase() -> PhaseGuard { begin_phase(); PhaseGuard(()) }
pub(crate) unsafe fn raw_alloc(size: usize, align: usize) -> *mut u8 {
    assert!(!parallel::parallelism_forbidden(), "ArenaVec allocation on a thread where parallelism is forbidden");
    unsafe { crate::observed_system_alloc(Layout::from_size_align_unchecked(size, align)) }
}
pub(crate) unsafe fn raw_dealloc(ptr: *mut u8, size: usize, align: usize) {
    unsafe { crate::observed_system_dealloc(ptr, Layout::from_size_align_unchecked(size, align)) }
}
