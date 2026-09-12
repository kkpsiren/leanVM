//! `fb-zk` — the relayer's prover and the reader's verifier for one Farcaster blob, as a CLI.
//!
//!   fb-zk prove  --rows rows.json --blob-id <32-byte hex> --out proof.bin
//!                [--leaf-size 2048] [--leaf-rate 1] [--top-rate 3]
//!   fb-zk verify --rows rows.json --blob-id <32-byte hex> --proof proof.bin
//!   fb-zk info   --proof proof.bin
//!
//! rows.json = the blob's signed messages IN BLOB ORDER: `[{"signer": hex32, "digest": hex20,
//! "sig": hex64}, …]`. `sig` is needed to prove and ignored to verify (a reader has no signatures:
//! that is the point). `--blob-id` is the blob's KZG versioned hash (docs/zk-reader-contract.md §5).
//! The proof file is the envelope of docs/zk-reader-contract.md §10 (postcard): version, leaf scheme, VK identifier, leaf size,
//! row count, blob id, top bytecode-claim point, canonical pre-order inner claims, and the top
//! proof (terminal profile). Writers and readers use v4; pre-mainnet v2/v3 are rejected. Verification needs the rows, the blob
//! id, the leaf size (in the envelope) and the proof — nothing from the prover is trusted.

use lean_prover::ed25519_leaf::{SigRow, blob_id_cells};
use rec_aggregation::init_aggregation_bytecode_cached;
use rec_aggregation::ed25519::*;
use rec_aggregation::ed25519_envelope::{BlobProofEnvelope, encode_ed25519_blob};
use std::time::Instant;
use std::io::Read;

fn read_envelope(path: &str) -> Result<Vec<u8>, String> {
    let mut bytes = Vec::new();
    std::fs::File::open(path).map_err(|e| format!("{path}: {e}"))?
        .take(rec_aggregation::ed25519_envelope::MAX_ENVELOPE_BYTES as u64 + 1)
        .read_to_end(&mut bytes).map_err(|e| format!("{path}: {e}"))?;
    Ok(bytes)
}

fn hex(s: &str) -> Result<Vec<u8>, String> {
    let s = s.strip_prefix("0x").unwrap_or(s);
    if s.len() % 2 != 0 { return Err("odd hex length".into()); }
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).map_err(|e| e.to_string())).collect()
}
fn rows_from(path: &str, need_sig: bool) -> Result<Vec<SigRow>, String> {
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).map_err(|e| format!("{path}: {e}"))?).map_err(|e| format!("{path}: {e}"))?;
    let arr = v.as_array().ok_or("rows.json must be an array")?;
    arr.iter().enumerate().map(|(i, r)| {
        let field = |k: &str| r.get(k).and_then(|x| x.as_str()).ok_or(format!("row {i}: missing {k}"));
        let pubkey: [u8; 32] = hex(field("signer")?)?.try_into().map_err(|_| format!("row {i}: signer must be 32 bytes"))?;
        let digest: [u8; 20] = hex(field("digest").or_else(|_| field("hash"))?)?.try_into().map_err(|_| format!("row {i}: digest must be 20 bytes"))?;
        let sig: [u8; 64] = match r.get("sig").or_else(|| r.get("signature")).and_then(|x| x.as_str()) {
            Some(s) => hex(s)?.try_into().map_err(|_| format!("row {i}: sig must be 64 bytes"))?,
            None if need_sig => return Err(format!("row {i}: sig is required to prove")),
            None => [0u8; 64],
        };
        Ok(SigRow { pubkey, digest, sig })
    }).collect()
}
fn arg(args: &[String], k: &str) -> Option<String> { args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned()) }
fn arg_n(args: &[String], k: &str, d: usize) -> Result<usize, String> { match arg(args, k) { Some(v) => v.parse().map_err(|_| format!("{k}: not a number")), None => Ok(d) } }

fn main() {
    if let Err(e) = run() { eprintln!("error: {e}"); std::process::exit(1); }
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    let cmd = args.get(1).map(String::as_str).unwrap_or("");
    match cmd {
        "prove" => {
            let rows = rows_from(&arg(&args, "--rows").ok_or("--rows")?, true)?;
            let vh: [u8; 32] = hex(&arg(&args, "--blob-id").ok_or("--blob-id")?)?.try_into().map_err(|_| "--blob-id must be 32 bytes")?;
            let out = arg(&args, "--out").ok_or("--out")?;
            let leaf_size = arg_n(&args, "--leaf-size", DEFAULT_LEAF_SIGS)?;
            let leaf_rate = arg_n(&args, "--leaf-rate", DEFAULT_LEAF_LOG_INV_RATE)?;
            let top_rate = arg_n(&args, "--top-rate", DEFAULT_TOP_LOG_INV_RATE)?;
            eprintln!("fb-zk prove: {} rows, leaves of {leaf_size}, leaf rate 1/{}, top rate 1/{} (terminal profile)", rows.len(), 1 << leaf_rate, 1 << top_rate);
            let t = Instant::now();
            let hit = init_aggregation_bytecode_cached(&cache_dir());
            eprintln!("  recursion bytecode ready ({:.1} s, cache {})", t.elapsed().as_secs_f32(), if hit { "hit" } else { "miss -> written" });
            let t = Instant::now();
            let top = prove_ed25519_blob(&rows, &blob_id_cells(&vh), leaf_size, leaf_rate, top_rate, &|m| eprintln!("  {m}"))?;
            let bytes = encode_ed25519_blob(&top, rows.len(), leaf_size, vh)?;
            std::fs::write(&out, &bytes).map_err(|e| format!("{out}: {e}"))?;
            eprintln!("  proved in {:.1} s; envelope {} bytes ({} KiB) -> {out}", t.elapsed().as_secs_f32(), bytes.len(), bytes.len() / 1024);
            Ok(())
        }
        "verify" => {
            let rows = rows_from(&arg(&args, "--rows").ok_or("--rows")?, false)?;
            let vh: [u8; 32] = hex(&arg(&args, "--blob-id").ok_or("--blob-id")?)?.try_into().map_err(|_| "--blob-id must be 32 bytes")?;
            let path = arg(&args, "--proof").ok_or("--proof")?;
            let bytes = read_envelope(&path)?;
            let env = BlobProofEnvelope::decode(&bytes)?;
            env.check_statement(rows.len(), &vh)?;
            let leaf_size = env.leaf_size;
            let t = Instant::now();
            init_aggregation_bytecode_cached(&cache_dir());
            let t_bc = t.elapsed().as_secs_f32();
            let t = Instant::now();
            env.verify(&rows, &vh)?;
            println!("OK: every one of the {} messages in blob 0x{} is validly signed by its signer (leaf size {leaf_size}, envelope {} KiB; bytecode {:.1} s, verify {:.3} s)", rows.len(), hexs(&vh), bytes.len() / 1024, t_bc, t.elapsed().as_secs_f32());
            Ok(())
        }
        "info" => {
            let path = arg(&args, "--proof").ok_or("--proof")?;
            let bytes = read_envelope(&path)?;
            let env = BlobProofEnvelope::decode(&bytes)?;
            println!("leaf scheme {} ({}), vk {}", env.scheme_id, lean_prover::ed25519_leaf::ED25519_SCHEME_NAME, hexs(&env.vk_id));
            let proof: backend::Proof<lean_vm::F> = backend::Proof::from_bytes(&env.proof_bytes).map_err(|e| format!("bad proof bytes: {e}"))?;
            println!("envelope v{}: blob 0x{}, {} rows, leaf size {}, {} leaves, {} inner nodes, proof {} field elements ({} KiB), file {} bytes ({} KiB)", env.version, hexs(&env.blob_id), env.n_rows, env.leaf_size, env.n_leaves, env.n_inner_nodes, proof.proof_size_fe(), proof.proof_size_fe() * 4 / 1024, bytes.len(), bytes.len() / 1024);
            Ok(())
        }
        _ => Err("usage: fb-zk prove --rows rows.json --blob-id <hex32> --out proof.bin [--leaf-size N] [--leaf-rate R] [--top-rate R]\n       fb-zk verify --rows rows.json --blob-id <hex32> --proof proof.bin\n       fb-zk info --proof proof.bin".into()),
    }
}
/// FB_ZK_CACHE, else ~/.cache/fb-zk. Must hold the authenticated prover-bytecode-v1.bin written by
/// the prepare-prover-cache example; nothing is compiled or cached implicitly.
fn cache_dir() -> std::path::PathBuf {
    if let Ok(d) = std::env::var("FB_ZK_CACHE") { return d.into(); }
    let home = std::env::var("HOME").unwrap_or_else(|_| ".".into());
    std::path::PathBuf::from(home).join(".cache/fb-zk")
}
fn hexs(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
