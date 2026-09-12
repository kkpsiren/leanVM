//! Standalone, offline dictionary -> decoded cells -> Poseidon release linkage audit.
//! This never loads a prover cache, compiles bytecode, creates a proof, or trusts the stored VK.
use backend::*;
use lean_vm::{DictionaryProgram, VerifierProgram};
use lean_vm::ed25519::sha512_table::sha512_bytes;
use rec_aggregation::verifier_artifact::{ARTIFACT_SHA512, VK_HASH};
use std::io::Read;

fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args_os().collect();
    if args.len() != 2 { return Err("usage: rehash-verifier-artifact PACKAGED-VK.bin".into()); }
    let mut bytes = Vec::new();
    std::fs::File::open(&args[1]).map_err(|e| e.to_string())?
        .take(32 * 1024 * 1024 + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() > 32 * 1024 * 1024 { return Err("artifact exceeds byte limit".into()); }
    let digest = sha512_bytes(&bytes);
    if digest != ARTIFACT_SHA512 { return Err("artifact SHA-512 differs from frozen release pin".into()); }
    let dictionary = DictionaryProgram::from_pinned_bytes(&bytes, &ARTIFACT_SHA512, VK_HASH)?;
    if dictionary.log_size() != 20 { return Err("unexpected release table dimensions".into()); }
    // The runtime loader checks the stored identity; this separate computation checks its linkage.
    let cells = dictionary.expand_for_audit();
    let computed = poseidon_hash_slice(&cells).map(|f| f.as_canonical_u32());
    if computed != VK_HASH { return Err(format!("decoded table Poseidon mismatch: {computed:?}")); }
    let sha512 = digest.iter().map(|b| format!("{b:02x}")).collect::<String>();
    println!("{{\"status\":\"pass\",\"artifactBytes\":{},\"decodedCells\":{},\"sha512\":\"{}\",\"poseidonVk\":{:?},\"claim\":\"decoded dictionary table matches pinned Poseidon identity; not a circuit soundness audit\"}}", bytes.len(), cells.len(), sha512, computed);
    Ok(())
}
fn main() {
    if let Err(error) = run() { eprintln!("rehash failed: {error}"); std::process::exit(1); }
}
