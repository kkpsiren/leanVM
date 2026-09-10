//! OWNER RUN: four distinct real leaves, then reuse their saved proofs to isolate a node.
//! No compilation, network, keys, arena or counting allocator. NODE_PROFILE=1 installs
//! phase timing/dimension hooks; production mode has no installed observer.
//! CACHE DATASET FIXTURE_DIR prepare N | check | full | terminal
//! `prepare` and both proving modes exceed the agent's 4 GB budget. Run serially.
use backend::*;
use lean_prover::ed25519_leaf::{SigRow, blob_id_cells, rows_from_json};
use lean_prover::prove_execution::ExecutionProof;
use lean_prover::verify_execution::verify_execution_with_profile;
use lean_vm::{F, PROFILE_FULL, PROFILE_TERMINAL, Profile};
use rec_aggregation::ed25519::*;
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, path::Path, sync::{Mutex, OnceLock}, time::Instant};

const CHILDREN: usize = 4;
const BLOB_ID: [u8; 32] = [1; 32]; // fixed synthetic versioned hash, not packed/onchain data

#[derive(Serialize, Deserialize)]
struct Manifest { n: usize, children: usize, leaf_rate: usize, blob_id: [u8; 32], dataset_sha512: Vec<u8> }
#[derive(Default, Serialize)]
struct Stat { calls: usize, seconds: f64, self_seconds: f64 }
struct Frame { key: (&'static str, &'static str), start: Instant, child_seconds: f64 }
#[derive(Default)]
struct ProfileState {
    stack: Vec<Frame>,
    stats: BTreeMap<(&'static str, &'static str), Stat>,
    values: BTreeMap<(&'static str, &'static str), usize>,
}
static PROFILE: OnceLock<Mutex<ProfileState>> = OnceLock::new();

fn observe(event: ProverProfileEvent) {
    let mut state = PROFILE.get_or_init(Default::default).lock().unwrap();
    match event {
        ProverProfileEvent::Enter(phase, table) => state.stack.push(Frame { key: (phase, table), start: Instant::now(), child_seconds: 0.0 }),
        ProverProfileEvent::Exit(phase, table) => {
            let frame = state.stack.pop().unwrap();
            assert_eq!(frame.key, (phase, table), "phase scopes must be serial");
            let elapsed = frame.start.elapsed().as_secs_f64();
            let stat = state.stats.entry(frame.key).or_default();
            stat.calls += 1;
            stat.seconds += elapsed;
            stat.self_seconds += (elapsed - frame.child_seconds).max(0.0);
            if let Some(parent) = state.stack.last_mut() { parent.child_seconds += elapsed; }
        }
        ProverProfileEvent::Value(kind, table, value) => { state.values.insert((kind, table), value); }
    }
}

fn profile_json() -> serde_json::Value {
    let state = PROFILE.get_or_init(Default::default).lock().unwrap();
    assert!(state.stack.is_empty());
    serde_json::json!({
        "stats": state.stats.iter().map(|(&(phase, table), stat)| serde_json::json!({
            "phase": phase, "table": table, "calls": stat.calls,
            "seconds": stat.seconds, "self_seconds": stat.self_seconds,
        })).collect::<Vec<_>>(),
        "dimensions": state.values.iter().map(|(&(kind, table), value)| serde_json::json!({
            "kind": kind, "table": table, "value": value,
        })).collect::<Vec<_>>(),
        "memory_scope": "OS peak RSS is recorded by the external process harness; no phase RSS/heap attribution",
    })
}

// Benchmark-only full-profile verification, using the public low-level verifier.
// Recompute every child digest and the bytecode value; never trust the node's carried value.
fn verify_node(profile: &Profile, node: &Ed25519NodeProof, rows: &[SigRow], n: usize) -> bool {
    let bc = rec_aggregation::get_aggregation_verifier_program();
    if node.bytecode_claim.point.len() != bc.cumulated_n_vars() { return false; }
    let mut claim = node.bytecode_claim.point.0.clone();
    claim.push(bc.evaluate(&node.bytecode_claim.point));
    let blob_id = blob_id_cells(&BLOB_ID);
    let digests: Vec<_> = rows.chunks(n).enumerate().map(|(k, r)| expected_leaf_digest(r, k, &blob_id).unwrap()).collect();
    let input = ed25519_node_input_data(&digests, &flatten_scalars_to_base::<F, lean_vm::EF>(&claim));
    if input != node.input_data { return false; }
    verify_execution_with_profile(profile, bc, &poseidon_hash_slice(&input), node.proof.proof.clone()).is_ok()
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() == 2 && args[1] == "--help" {
        println!("CACHE DATASET FIXTURE_DIR prepare N | check | full | terminal\nOWNER ONLY for prepare/full/terminal (>4 GB). NODE_PROFILE=1 for diagnostic phases. No builds or network.");
        return;
    }
    assert!((5..=6).contains(&args.len()), "see --help");
    let mode = args[4].as_str();
    assert!(["prepare", "check", "full", "terminal"].contains(&mode));
    assert_eq!(args.len(), if mode == "prepare" { 6 } else { 5 });
    let cache = std::fs::read(&args[1]).unwrap();
    // Refuse fallback/compilation: this benchmark requires the audited full release bytes.
    rec_aggregation::prover_artifact::load_prover_cache(&cache).expect("authenticated full release cache");
    let start = Instant::now();
    rec_aggregation::init_aggregation_bytecode_pinned(&cache, rec_aggregation::verifier_artifact::VK_HASH).unwrap();
    let startup_s = start.elapsed().as_secs_f64();
    drop(cache);
    let dataset_digest = lean_vm::ed25519::sha512_table::sha512_bytes(&std::fs::read(&args[2]).unwrap());
    let mut rows = rows_from_json(&args[2]);
    let dir = Path::new(&args[3]);
    let blob_id = blob_id_cells(&BLOB_ID);
    if mode == "prepare" {
        let n: usize = args[5].parse().unwrap();
        assert!((1..=lean_prover::ed25519_leaf::MAX_LEAF_SIGS).contains(&n));
        assert!(rows.len() >= CHILDREN * n);
        std::fs::create_dir(dir).expect("fixture directory must be new; partial runs are not reusable");
        let mut samples = Vec::new();
        for k in 0..CHILDREN {
            let chunk = &rows[k * n..(k + 1) * n];
            let start = Instant::now();
            let leaf = prove_ed25519_leaf(chunk, k, &blob_id, 1).unwrap();
            let prove_s = start.elapsed().as_secs_f64();
            verify_ed25519_leaf_for(&leaf, chunk, k, &blob_id).unwrap();
            let wire = leaf.proof.proof.to_bytes();
            std::fs::write(dir.join(format!("leaf-{k}.proof")), &wire).unwrap();
            samples.push(serde_json::json!({"leaf": k, "rows": n, "signers": leaf.n_groups, "prove_s": prove_s, "proof_bytes": wire.len()}));
        }
        let manifest = Manifest { n, children: CHILDREN, leaf_rate: 1, blob_id: BLOB_ID, dataset_sha512: dataset_digest.to_vec() };
        std::fs::write(dir.join("manifest.json"), serde_json::to_vec_pretty(&manifest).unwrap()).unwrap();
        println!("{}", serde_json::json!({"classification": "measured production fixture preparation", "startup_s": startup_s, "leaves": samples}));
        return;
    }
    let manifest: Manifest = serde_json::from_slice(&std::fs::read(dir.join("manifest.json")).unwrap()).unwrap();
    assert_eq!(manifest.dataset_sha512, dataset_digest);
    assert_eq!(manifest.children, CHILDREN);
    assert_eq!(manifest.leaf_rate, 1);
    assert_eq!(manifest.blob_id, BLOB_ID);
    let n = manifest.n;
    assert!((1..=lean_prover::ed25519_leaf::MAX_LEAF_SIGS).contains(&n) && rows.len() >= CHILDREN * n);
    rows.truncate(CHILDREN * n);
    let mut leaves = Vec::new();
    for (k, chunk) in rows.chunks(n).enumerate() {
        let wire = std::fs::read(dir.join(format!("leaf-{k}.proof"))).unwrap();
        let leaf = Ed25519LeafProof { input_data: expected_leaf_input_data(chunk, k, &blob_id).unwrap(), n_seg: n, n_groups: 0,
            proof: ExecutionProof { proof: Proof::from_bytes(&wire).unwrap(), metadata: None } };
        // `check` and actual proving modes both validate the frozen fixtures before timing.
        verify_ed25519_leaf_for(&leaf, chunk, k, &blob_id).unwrap();
        leaves.push(leaf);
    }
    if mode == "check" {
        println!("{}", serde_json::json!({"classification": "measured fixture verification only", "children": CHILDREN, "rows_per_child": n, "startup_s": startup_s}));
        return;
    }
    let diagnostic = std::env::var_os("NODE_PROFILE").is_some();
    if diagnostic { set_prover_profile_observer(observe); }
    let (profile, rate) = if mode == "full" { (&PROFILE_FULL, 1) } else { (&PROFILE_TERMINAL, 3) };
    let children: Vec<_> = leaves.iter().map(Ed25519Child::Leaf).collect();
    let start = Instant::now();
    let mut node = prove_ed25519_node_with(profile, &children, rate).unwrap();
    let node_s = start.elapsed().as_secs_f64(); // includes production child verification and hint preparation
    let start = Instant::now();
    assert!(verify_node(profile, &node, &rows, n));
    let verify_s = start.elapsed().as_secs_f64();
    // Signature-free reader: signatures are irrelevant to statement reconstruction.
    for row in &mut rows { row.sig = [0; 64]; }
    assert!(verify_node(profile, &node, &rows, n));
    rows[0].digest[0] ^= 1;
    assert!(!verify_node(profile, &node, &rows, n), "changed statement accepted");
    rows[0].digest[0] ^= 1;
    let wire = node.proof.proof.to_bytes();
    if mode == "terminal" {
        let envelope = rec_aggregation::ed25519_envelope::encode_ed25519_blob(&node, rows.len(), n, BLOB_ID).unwrap();
        rec_aggregation::ed25519_envelope::BlobProofEnvelope::decode(&envelope).unwrap().verify(&rows, &BLOB_ID).unwrap();
    }
    // Preserve valid framing, change one canonical transcript field.
    let mut bad = wire.clone();
    let count = u32::from_le_bytes(bad[..4].try_into().unwrap()) as usize;
    let middle = 4 + (count / 2) * 4;
    let field = F::from_u32(u32::from_le_bytes(bad[middle..middle + 4].try_into().unwrap())) + F::ONE;
    bad[middle..middle + 4].copy_from_slice(&field.as_canonical_u32().to_le_bytes());
    node.proof.proof = Proof::from_bytes(&bad).unwrap();
    assert!(!verify_node(profile, &node, &rows, n), "changed proof accepted");
    println!("{}", serde_json::json!({"classification": if diagnostic { "measured diagnostic (phase hooks, no counting allocator)" } else { "measured production (no observer or counting allocator)" },
        "children": CHILDREN, "child_kind": "four distinct leaves", "rows_per_child": n, "profile": mode, "log_inv_rate": rate,
        "startup_s": startup_s, "node_s": node_s, "verify_s": verify_s, "proof_bytes": wire.len(),
        "cycles": node.proof.metadata.as_ref().map(|m| m.cycles), "valid_verified": true, "changed_statement_rejected": true, "changed_proof_rejected": true,
        "diagnostic": if diagnostic { profile_json() } else { serde_json::Value::Null }}));
}
