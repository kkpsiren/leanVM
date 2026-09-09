//! Bump-pointer arena, used explicitly (never as a `#[global_allocator]`). One mmap region split
//! into per-thread slabs: alloc bumps a thread-local pointer, free is a no-op, `begin_phase()`
//! resets every slab. Proof data lives in [`ArenaVec`]; `raw_dealloc` picks arena-vs-system by
//! pointer range, so `ArenaVec` carries no allocator parameter.

mod arena_cow;
mod arena_vec;
#[cfg(not(target_arch = "wasm32"))]
mod syscall;

pub use arena_cow::ArenaCow;
pub use arena_vec::{ArenaVec, OwnedBuffer};

// ArenaVec's System calls bypass #[global_allocator]. Diagnostics must observe them explicitly.
static SYSTEM_OBSERVER: std::sync::OnceLock<fn(usize, bool)> = std::sync::OnceLock::new();

/// Observe System allocation requests (`true`) and frees (`false`). Called before allocation,
/// with a matching free notification on failure. The callback must not allocate or panic.
/// Arena bump allocations are excluded; use only with the arena disabled for live-heap accounting.
pub fn set_system_allocation_observer(observer: fn(usize, bool)) {
    SYSTEM_OBSERVER.set(observer).expect("allocation observer already installed");
}

unsafe fn observed_system_alloc(layout: std::alloc::Layout) -> *mut u8 {
    use std::alloc::GlobalAlloc;
    if let Some(observer) = SYSTEM_OBSERVER.get() { observer(layout.size(), true); }
    let ptr = unsafe { std::alloc::System.alloc(layout) };
    if ptr.is_null() {
        if let Some(observer) = SYSTEM_OBSERVER.get() { observer(layout.size(), false); }
    }
    ptr
}

unsafe fn observed_system_dealloc(ptr: *mut u8, layout: std::alloc::Layout) {
    use std::alloc::GlobalAlloc;
    unsafe { std::alloc::System.dealloc(ptr, layout); }
    if let Some(observer) = SYSTEM_OBSERVER.get() { observer(layout.size(), false); }
}

/// Build an [`ArenaVec`], mirroring [`std::vec!`]:
#[macro_export]
macro_rules! arena_vec {
    () => { $crate::ArenaVec::new() };
    ($elem:expr; $n:expr) => { $crate::ArenaVec::filled($elem, $n) };
    ($($x:expr),+ $(,)?) => { $crate::ArenaVec::from_iter([$($x),+]) };
}

#[cfg(not(target_arch = "wasm32"))]
mod native;
#[cfg(not(target_arch = "wasm32"))]
pub use native::*;
#[cfg(not(target_arch = "wasm32"))]
use native::{raw_alloc, raw_dealloc};
#[cfg(target_arch = "wasm32")]
mod heap;
#[cfg(target_arch = "wasm32")]
pub use heap::*;
#[cfg(target_arch = "wasm32")]
use heap::{raw_alloc, raw_dealloc};
