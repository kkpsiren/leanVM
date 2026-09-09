//! Dependency-free C/Wasm ABI over the existing envelope verifier. See include/fb_verifier.h.
use std::alloc::{GlobalAlloc, Layout, System};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};
use lean_prover::ed25519_leaf::SigRow;
use rec_aggregation::{ed25519_envelope::BlobProofEnvelope, init_aggregation_bytecode_pinned};

const MAX_BUFFER: usize = 32 * 1024 * 1024;
const VK_HASH: [u32; 8] = [1153961582, 1250141101, 1638904970, 1982146112,
    763994888, 2126617202, 1686598344, 1973457087];
static READY: AtomicBool = AtomicBool::new(false);
static POISONED: AtomicBool = AtomicBool::new(false);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
struct Metered;
fn account(n: usize) { let live = LIVE.fetch_add(n, Relaxed) + n; PEAK.fetch_max(live, Relaxed); }
// Track requested heap bytes, not allocator overhead or process RSS.
unsafe impl GlobalAlloc for Metered {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) }; if !p.is_null() { account(l.size()); } p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) }; if !p.is_null() { account(l.size()); } p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l); } LIVE.fetch_sub(l.size(), Relaxed);
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, n) };
        if !q.is_null() { LIVE.fetch_sub(l.size(), Relaxed); account(n); } q
    }
}
#[global_allocator]
static ALLOCATOR: Metered = Metered;

fn boundary(f: impl FnOnce() -> i32) -> i32 {
    if POISONED.load(Relaxed) { return 4; }
    // Native unwinding is caught. On raw Wasm panic=abort traps: the host must discard the instance.
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(code) => code,
        Err(_) => { POISONED.store(true, Relaxed); 4 }
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn fb_abi_version() -> u32 { 1 }
#[unsafe(no_mangle)]
pub extern "C" fn fb_heap_live() -> usize { LIVE.load(Relaxed) }
#[unsafe(no_mangle)]
pub extern "C" fn fb_heap_peak() -> usize { PEAK.load(Relaxed) }
#[unsafe(no_mangle)]
pub extern "C" fn fb_heap_reset_peak() { PEAK.store(LIVE.load(Relaxed), Relaxed); }
#[unsafe(no_mangle)]
pub extern "C" fn fb_alloc(n: usize) -> *mut u8 {
    if n == 0 || n > MAX_BUFFER { return std::ptr::null_mut(); }
    // Initialized bytes avoid exposing uninitialized native memory to the caller.
    Box::into_raw(vec![0u8; n].into_boxed_slice()).cast()
}
/// # Safety
/// p/n must be exactly one live allocation returned by fb_alloc. Free it once, after calls finish.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fb_free(p: *mut u8, n: usize) {
    if !p.is_null() && n != 0 { unsafe { drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut(p, n))); } }
}
/// # Safety
/// p/n is a live, immutable readable buffer for this call; calls on this library are serialized.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fb_init(p: *const u8, n: usize) -> i32 {
    boundary(|| {
        if p.is_null() || n == 0 || n > MAX_BUFFER { return 2; }
        if READY.load(Relaxed) { return 5; }
        let bytes = unsafe { std::slice::from_raw_parts(p, n) };
        match init_aggregation_bytecode_pinned(bytes, VK_HASH) {
            Ok(()) => { READY.store(true, Relaxed); 0 },
            Err(_) => 1,
        }
    })
}
/// # Safety
/// All buffers are readable and immutable for this call. rows is n_rows consecutive 52-byte
/// records (pubkey[32], digest[20]) in blob order; blob_id points to exactly 32 bytes.
/// Native callers must serialize calls, including metric resets and initialization.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fb_verify(
    envelope: *const u8, envelope_len: usize, rows: *const u8, rows_len: usize, blob_id: *const u8,
) -> i32 {
    boundary(|| {
        if !READY.load(Relaxed) { return 3; }
        if envelope.is_null() || rows.is_null() || blob_id.is_null() || envelope_len == 0
            || envelope_len > 16 * 1024 * 1024 || rows_len == 0 || rows_len > MAX_BUFFER
            || !rows_len.is_multiple_of(52) { return 2; }
        let bytes = unsafe { std::slice::from_raw_parts(envelope, envelope_len) };
        let id: &[u8; 32] = unsafe { &*blob_id.cast() };
        let env = match BlobProofEnvelope::decode(bytes) { Ok(e) => e, Err(_) => return 1 };
        if env.version != 3 || env.check_statement(rows_len / 52, id).is_err() { return 1; }
        let rows = unsafe { std::slice::from_raw_parts(rows, rows_len) }.chunks_exact(52)
            .map(|r| SigRow { pubkey: r[..32].try_into().unwrap(), digest: r[32..].try_into().unwrap(), sig: [0; 64] })
            .collect::<Vec<_>>();
        match env.verify(&rows, id) { Ok(()) => 0, Err(_) => 1 }
    })
}
