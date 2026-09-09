use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use zk_alloc::{ArenaVec, set_system_allocation_observer};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

#[test]
fn system_observer_counts_growth_overlap_without_counting_std_vec() {
    set_system_allocation_observer(|size, allocating| {
        if allocating {
            PEAK.fetch_max(LIVE.fetch_add(size, Relaxed) + size, Relaxed);
        } else {
            LIVE.fetch_sub(size, Relaxed);
        }
    });
    // This observer complements, rather than duplicates, the global allocator's counters.
    let ordinary = vec![7_u64; 100];
    assert_eq!(LIVE.load(Relaxed), 0);
    let mut v = ArenaVec::<u64>::with_capacity(8);
    v.extend(0..8);
    assert_eq!(LIVE.load(Relaxed), 64);
    v.push(8);
    assert_eq!(LIVE.load(Relaxed), 128);
    assert_eq!(PEAK.load(Relaxed), 192); // old and new buffers overlap during the move
    assert_eq!(v.iter().sum::<u64>(), 36);
    drop(v);
    assert_eq!(LIVE.load(Relaxed), 0);
    assert_eq!(ordinary.len(), 100);
}
