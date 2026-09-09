//! Offline, single-leaf diagnostic. Uses an existing FULL bytecode cache; never compiles it.
//! Arguments: CACHE DATASET N LOG_INV_RATE [PROOF_OUT]. Default heap/RSS limits are 3.5/4 GB.
//! PROFILE_HEAP_LIMIT / PROFILE_RSS_LIMIT may be raised only by the operator on a suitable machine.
//! Counting allocator overhead is included in timings. No arena is enabled here (same as fb-zk).
//! PROFILE_TRACE_ONLY=1 measures witness/trace construction without proving.
//! PROFILE_VERIFY_ONLY=1 reads PROOF_OUT as an existing proof and checks it without proving.
use backend::*;
use lean_prover::ed25519_leaf::rows_from_json;
use lean_vm::F;
use rec_aggregation::ed25519::{prove_ed25519_leaf, verify_ed25519_leaf_for};
use std::{alloc::{GlobalAlloc, Layout, System}, collections::BTreeMap, sync::{Mutex, OnceLock, atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed}}, time::Instant};

const SLOTS: usize = 256;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);
static CURRENT: AtomicUsize = AtomicUsize::new(0);
static LIMIT: AtomicUsize = AtomicUsize::new(3_500_000_000);
static HEAP: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];
static LARGEST: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];
static RSS: [AtomicUsize; SLOTS] = [const { AtomicUsize::new(0) }; SLOTS];
static DONE: AtomicBool = AtomicBool::new(false);

struct Counting;
fn allocated(n: usize) {
    let live = LIVE.fetch_add(n, Relaxed) + n;
    let id = CURRENT.load(Relaxed);
    PEAK.fetch_max(live, Relaxed);
    HEAP[id].fetch_max(live, Relaxed);
    LARGEST[id].fetch_max(n, Relaxed);
    // The RSS monitor handles physical residency separately. Avoid allocating an error message here.
    if live > LIMIT.load(Relaxed) { std::process::abort(); }
}
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        // Account before allocation so the diagnostic guard cannot allocate beyond its budget.
        allocated(layout.size());
        let p = unsafe { System.alloc(layout) };
        if p.is_null() { LIVE.fetch_sub(layout.size(), Relaxed); }
        p
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        allocated(layout.size());
        let p = unsafe { System.alloc_zeroed(layout) };
        if p.is_null() { LIVE.fetch_sub(layout.size(), Relaxed); }
        p
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout); }
        LIVE.fetch_sub(layout.size(), Relaxed);
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // Preserve System realloc behavior. Requested heap excludes any allocator-internal overlap.
        let growth = new_size.saturating_sub(layout.size());
        allocated(growth);
        let p = unsafe { System.realloc(ptr, layout, new_size) };
        if p.is_null() { LIVE.fetch_sub(growth, Relaxed); }
        else if new_size < layout.size() { LIVE.fetch_sub(layout.size() - new_size, Relaxed); }
        p
    }
}
#[global_allocator]
static ALLOCATOR: Counting = Counting;

// MACH_TASK_BASIC_INFO, from the local macOS SDK. RSS samples are process residency, not heap.
#[cfg(target_os = "macos")]
fn rss() -> (usize, usize) {
    #[repr(C)]
    struct Info { virtual_size: u64, resident_size: u64, resident_max: u64, times: [i32; 4], policy: i32, suspend: i32 }
    unsafe extern "C" { static mach_task_self_: u32; fn task_info(task: u32, flavor: u32, info: *mut i32, count: *mut u32) -> i32; }
    let mut info: Info = unsafe { std::mem::zeroed() };
    let mut count = (std::mem::size_of::<Info>() / 4) as u32;
    let ok = unsafe { task_info(mach_task_self_, 20, (&raw mut info).cast(), &raw mut count) };
    assert_eq!(ok, 0, "task_info failed");
    (info.resident_size as usize, info.resident_max as usize)
}
#[cfg(not(target_os = "macos"))]
fn rss() -> (usize, usize) { (0, 0) } // Explicitly unavailable; heap still measured.

#[derive(Default)]
struct Stat { id: usize, calls: usize, ns: u128, self_ns: u128, enter_heap: usize, exit_heap: usize }
struct Frame { key: (&'static str, &'static str), start: Instant, children_ns: u128 }
#[derive(Default)]
struct State { stats: BTreeMap<(&'static str, &'static str), Stat>, stack: Vec<Frame>, values: BTreeMap<(&'static str, &'static str), usize> }
static STATE: OnceLock<Mutex<State>> = OnceLock::new();

fn observe(event: ProverProfileEvent) {
    let mut state = STATE.get_or_init(Default::default).lock().unwrap();
    match event {
        ProverProfileEvent::Enter(phase, table) => {
            let id = state.stats.len() + 1;
            assert!(id < SLOTS);
            let stat = state.stats.entry((phase, table)).or_insert_with(|| Stat { id, ..Default::default() });
            stat.enter_heap = stat.enter_heap.max(LIVE.load(Relaxed));
            CURRENT.store(stat.id, Relaxed);
            HEAP[stat.id].fetch_max(LIVE.load(Relaxed), Relaxed);
            state.stack.push(Frame { key: (phase, table), start: Instant::now(), children_ns: 0 });
        }
        ProverProfileEvent::Exit(phase, table) => {
            let frame = state.stack.pop().unwrap();
            assert_eq!(frame.key, (phase, table), "diagnostic scopes must be serial");
            let elapsed = frame.start.elapsed().as_nanos();
            let stat = state.stats.get_mut(&frame.key).unwrap();
            stat.calls += 1;
            stat.ns += elapsed;
            stat.self_ns += elapsed.saturating_sub(frame.children_ns);
            stat.exit_heap = stat.exit_heap.max(LIVE.load(Relaxed));
            if table == "all" || phase == "trace_pad" {
                eprintln!("phase={phase} table={table} seconds={:.6} heap={} heap_peak={} rss={} rss_max={}",
                    elapsed as f64 / 1e9, LIVE.load(Relaxed), PEAK.load(Relaxed), rss().0, rss().1);
            }
            if let Some(parent) = state.stack.last_mut() { parent.children_ns += elapsed; }
            let parent = state.stack.last().map(|p| state.stats[&p.key].id).unwrap_or(0);
            CURRENT.store(parent, Relaxed);
        }
        ProverProfileEvent::Value(kind, table, value) => { state.values.insert((kind, table), value); }
    }
}

fn emit_profile(extra: serde_json::Value) {
    let state = STATE.get_or_init(Default::default).lock().unwrap();
    let stats: Vec<_> = state.stats.iter().map(|(&(phase, table), s)| serde_json::json!({
        "phase": phase, "table": table, "calls": s.calls, "seconds": s.ns as f64 / 1e9,
        "self_seconds": s.self_ns as f64 / 1e9, "enter_heap": s.enter_heap, "exit_heap": s.exit_heap,
        "heap_peak": HEAP[s.id].load(Relaxed), "largest_allocation": LARGEST[s.id].load(Relaxed),
        "rss_sample_peak": RSS[s.id].load(Relaxed)
    })).collect();
    let values: Vec<_> = state.values.iter().map(|(&(kind, table), &value)| serde_json::json!({"kind": kind, "table": table, "value": value})).collect();
    let in_progress: Vec<_> = state.stack.iter().map(|s| serde_json::json!({"phase": s.key.0, "table": s.key.1,
        "elapsed_s": s.start.elapsed().as_secs_f64()})).collect();
    let mut result = extra.as_object().unwrap().clone();
    result.extend(serde_json::json!({"heap_peak": PEAK.load(Relaxed), "os_peak_rss": rss().1,
        "stats": stats, "values": values, "in_progress": in_progress}).as_object().unwrap().clone());
    println!("{}", serde_json::Value::Object(result));
}

fn trace_only(rows: &[lean_prover::ed25519_leaf::SigRow], blob_id: &[F; 9]) {
    use lean_prover::ed25519_leaf::leaf_hint_buffers;
    use lean_vm::*;
    let bc = rec_aggregation::get_aggregation_bytecode();
    let hints_span = prover_profile_span("leaf_hints", "all");
    let (sorted, _, meta, root, buffers) = leaf_hint_buffers(rows, 0, blob_id).unwrap();
    let data = rec_aggregation::ed25519::ed25519_leaf_input_data(sorted.len(), &meta, &root);
    let mut hints = Hints::default();
    hints.insert(bc, "input_data_num_chunks", arena_vec![arena_vec![F::from_usize(data.len() / DIGEST_LEN)]]);
    hints.insert(bc, "input_data", arena_vec![ArenaVec::from_slice(&data)]);
    for (name, v) in &buffers { hints.insert(bc, name, arena_vec![ArenaVec::from_slice(v)]); }
    let witness = ExecutionWitness { preamble_memory_len: rec_aggregation::PREAMBLE_MEMORY_LEN, hints, min_table_log_n_rows: Default::default() };
    drop(hints_span);
    let execution = {
        let _p = prover_profile_span("execute", "all");
        try_execute_bytecode(bc, &poseidon_hash_slice(&data), &witness, false).unwrap()
    };
    let trace = {
        let _p = prover_profile_span("trace", "all");
        lean_prover::trace_gen::get_execution_trace(bc, execution, &witness.min_table_log_n_rows)
    };
    let memory_len = trace.memory.len().max(1 << MIN_LOG_MEMORY_SIZE).max(1 << bc.log_size());
    let max_table_log = trace.traces.values().map(|t| t.log_n_rows).max().unwrap();
    let mut cells = 2 * memory_len + (1 << bytecode_block_log(bc.log_size(), max_table_log)) + (1 << range_region_log(max_table_log));
    let mut trace_bytes = 0;
    for (table, t) in &trace.traces {
        cells += table.n_columns() << t.log_n_rows;
        trace_bytes += t.columns.iter().map(|c| c.capacity() * std::mem::size_of::<F>()).sum::<usize>();
    }
    prover_profile_value("memory_cells", "all", memory_len);
    prover_profile_value("trace_capacity_bytes", "all", trace_bytes);
    prover_profile_value("pcs_active_cells", "all", cells);
    prover_profile_value("pcs_padded_cells", "all", cells.next_power_of_two());
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    assert!((5..=6).contains(&args.len()), "CACHE DATASET N LOG_INV_RATE [PROOF_OUT]");
    if let Ok(v) = std::env::var("PROFILE_HEAP_LIMIT") { LIMIT.store(v.parse().unwrap(), Relaxed); }
    let rss_limit = std::env::var("PROFILE_RSS_LIMIT").map(|v| v.parse().unwrap()).unwrap_or(4_000_000_000);
    let monitor = std::thread::spawn(move || {
        while !DONE.load(Relaxed) {
            let (resident, _) = rss();
            RSS[CURRENT.load(Relaxed)].fetch_max(resident, Relaxed);
            if resident > rss_limit {
                eprintln!("diagnostic RSS budget exceeded: {resident}");
                emit_profile(serde_json::json!({"status": "rss_budget_exceeded"}));
                std::process::exit(86);
            }
            std::thread::sleep(std::time::Duration::from_millis(5));
        }
    });
    set_system_allocation_observer(|n, alloc| { if alloc { allocated(n); } else { LIVE.fetch_sub(n, Relaxed); } });
    set_prover_profile_observer(observe);
    {
        let _p = prover_profile_span("startup", "all");
        let bytes = std::fs::read(&args[1]).unwrap();
        assert!(!bytes.starts_with(lean_vm::VERIFIER_ARTIFACT_MAGIC), "proving needs a full instruction cache");
        rec_aggregation::init_aggregation_bytecode_pinned(&bytes, rec_aggregation::verifier_artifact::VK_HASH).unwrap();
    }
    let n: usize = args[3].parse().unwrap();
    let rate: usize = args[4].parse().unwrap();
    let mut rows = rows_from_json(&args[2]);
    assert!(n > 0 && n <= rows.len());
    rows.truncate(n);
    let blob_id = [F::ZERO; 9];
    let start = Instant::now();
    if std::env::var_os("PROFILE_VERIFY_ONLY").is_some() {
        let path = args.get(5).expect("PROFILE_VERIFY_ONLY requires an existing proof path");
        let proof = Proof::from_bytes(&std::fs::read(path).unwrap()).unwrap();
        let mut leaf = rec_aggregation::ed25519::Ed25519LeafProof {
            input_data: rec_aggregation::ed25519::expected_leaf_input_data(&rows, 0, &blob_id).unwrap(),
            n_seg: n, n_groups: 0,
            proof: lean_prover::prove_execution::ExecutionProof { proof, metadata: None },
        };
        verify_ed25519_leaf_for(&leaf, &rows, 0, &blob_id).unwrap();
        let mut changed = rows.clone();
        changed[0].digest[0] ^= 1;
        assert!(verify_ed25519_leaf_for(&leaf, &changed, 0, &blob_id).is_err());
        // Change one canonical transcript field while preserving the complete wire structure.
        let mut wire = leaf.proof.proof.to_bytes();
        let transcript_len = u32::from_le_bytes(wire[..4].try_into().unwrap()) as usize;
        let middle = 4 + (transcript_len / 2) * 4;
        let cell = F::from_u32(u32::from_le_bytes(wire[middle..middle + 4].try_into().unwrap())) + F::ONE;
        wire[middle..middle + 4].copy_from_slice(&cell.as_canonical_u32().to_le_bytes());
        leaf.proof.proof = Proof::from_bytes(&wire).unwrap();
        assert!(verify_ed25519_leaf_for(&leaf, &rows, 0, &blob_id).is_err());
        DONE.store(true, Relaxed);
        monitor.join().unwrap();
        emit_profile(serde_json::json!({"status": "verified_existing", "n": n,
            "verify_and_tamper_s": start.elapsed().as_secs_f64()}));
        return;
    }
    if std::env::var_os("PROFILE_TRACE_ONLY").is_some() {
        trace_only(&rows, &blob_id);
        DONE.store(true, Relaxed);
        monitor.join().unwrap();
        emit_profile(serde_json::json!({"status": "trace_only", "n": n, "log_inv_rate": rate,
            "trace_s": start.elapsed().as_secs_f64()}));
        return;
    }
    let leaf = prove_ed25519_leaf(&rows, 0, &blob_id, rate).unwrap();
    let prove_s = start.elapsed().as_secs_f64();
    let start = Instant::now();
    verify_ed25519_leaf_for(&leaf, &rows, 0, &blob_id).unwrap();
    let verify_s = start.elapsed().as_secs_f64();
    let mut changed = rows.clone();
    changed[0].digest[0] ^= 1;
    assert!(verify_ed25519_leaf_for(&leaf, &changed, 0, &blob_id).is_err());
    let proof_bytes = leaf.proof.proof.to_bytes();
    if let Some(path) = args.get(5) { std::fs::write(path, &proof_bytes).unwrap(); }
    DONE.store(true, Relaxed);
    monitor.join().unwrap();
    emit_profile(serde_json::json!({"status": "complete", "n": n, "log_inv_rate": rate,
        "prove_s": prove_s, "verify_s": verify_s, "proof_bytes": proof_bytes.len()}));
}
