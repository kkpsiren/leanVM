use std::{cell::Cell, marker::PhantomData};
thread_local! { static FORBIDDEN: Cell<bool> = const { Cell::new(false) }; }
pub fn num_threads() -> usize { 1 }
pub fn recommended_chunk_size(n: usize) -> usize { n.div_ceil(4).max(1) }
pub(crate) fn current_worker_id() -> usize { 0 }
pub fn is_in_pool_task() -> bool { false }
pub fn init() {}
pub fn parallelism_forbidden() -> bool { cfg!(feature = "forbid-parallelism") && FORBIDDEN.get() }
#[derive(Debug)]
pub struct ForbidParallelismGuard { prev: bool, _not_send: PhantomData<*const ()> }
pub fn forbid_parallelism() -> ForbidParallelismGuard {
    ForbidParallelismGuard { prev: cfg!(feature = "forbid-parallelism") && FORBIDDEN.replace(true), _not_send: PhantomData }
}
impl Drop for ForbidParallelismGuard {
    fn drop(&mut self) { if cfg!(feature = "forbid-parallelism") { FORBIDDEN.set(self.prev); } }
}
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n: usize, f: F) {
    assert!(!parallelism_forbidden(), "pool dispatch while parallelism is forbidden");
    if n > 0 { f(0, n); }
}
