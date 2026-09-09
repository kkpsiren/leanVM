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
