//! ed25519 leaves and blobs as modes of the recursion program (Phase E part 2).
//!
//! Leaf input data: `[LEAF_FLAG, n_seg, 0×6] ‖ zero bytecode claim (padded) ‖ fiat-shamir domsep ‖ meta ‖ root_seg`
//! (public input = its Poseidon hash). Blob input data: `[BLOB_FLAG, K, 0×6] ‖ reduced claim ‖ domsep ‖
//! K leaf digests ‖ [n_total, blob_id×4, 0×3]`; the program verifies each leaf proof (seg_index = position,
//! same blob_id, version, Σ n_seg = n_total) and reduces their bytecode claims.

use crate::bytecode_claims::{flatten_bytecode_claim, reduce_bytecode_claims};
use crate::compilation::{BYTECODE_CLAIM_OFFSET, ED25519_BLOB_FLAG, ED25519_LEAF_FLAG, MAX_RECURSIONS, PREAMBLE_MEMORY_LEN, get_aggregation_bytecode};
use crate::single_message_aggregation::{extract_merkle_hint_blobs, rebuild_bytecode_claim};
use crate::{InnerVerified, verify_inner};
use backend::*;
use lean_prover::ed25519_leaf::{SigRow, leaf_hint_buffers, leaf_meta, root_seg};
use lean_prover::prove_execution::{ExecutionProof, prove_execution};
use lean_prover::*;
use lean_vm::*;

pub struct Ed25519LeafProof {
    pub input_data: Vec<F>,
    pub n_seg: usize,
    pub n_groups: usize,
    pub proof: ExecutionProof,
}
pub struct Ed25519BlobProof {
    pub input_data: Vec<F>,
    pub bytecode_claim: Evaluation<EF>,
    pub proof: ExecutionProof,
}

fn zero_bytecode_claim_flat() -> Vec<F> {
    let bytecode = get_aggregation_bytecode();
    let point = MultilinearPoint(vec![EF::ZERO; bytecode.cumulated_n_vars()]);
    flatten_bytecode_claim(&rebuild_bytecode_claim(point).expect("zero claim"))
}

/// The leaf's input data (what the reader recomputes from the decoded columns and the leaf parameters).
pub fn ed25519_leaf_input_data(n_seg: usize, meta: &[F; 8], root: &[F; 8]) -> Vec<F> {
    let bytecode = get_aggregation_bytecode();
    let claim = zero_bytecode_claim_flat();
    let mut data = Vec::new();
    data.push(F::from_usize(ED25519_LEAF_FLAG));
    data.push(F::from_usize(n_seg));
    data.resize(DIGEST_LEN, F::ZERO);
    data.extend_from_slice(&claim);
    data.extend(std::iter::repeat_n(F::ZERO, claim.len().next_multiple_of(DIGEST_LEN) - claim.len()));
    data.extend_from_slice(&fiat_shamir_domain_sep(bytecode));
    data.extend_from_slice(meta);
    data.extend_from_slice(root);
    data
}
/// Reader side: the leaf input data from the rows (sorted by signer) and the leaf parameters.
pub fn expected_leaf_input_data(rows: &[SigRow], seg_index: usize, blob_id: &[F; 4]) -> Vec<F> {
    let mut sorted = rows.to_vec(); sorted.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
    ed25519_leaf_input_data(sorted.len(), &leaf_meta(sorted.len(), seg_index, blob_id), &root_seg(&sorted))
}

pub fn prove_ed25519_leaf(rows: &[SigRow], seg_index: usize, blob_id: &[F; 4], log_inv_rate: usize) -> Result<Ed25519LeafProof, String> {
    let bytecode = get_aggregation_bytecode();
    let (rows, n_groups, meta, root, buffers) = leaf_hint_buffers(rows, seg_index, blob_id)?;
    let input_data = ed25519_leaf_input_data(rows.len(), &meta, &root);
    let public_input = poseidon_hash_slice(&input_data);
    let mut hints = Hints::default();
    hints.insert(bytecode, "input_data_num_chunks", arena_vec![arena_vec![F::from_usize(input_data.len() / DIGEST_LEN)]]);
    hints.insert(bytecode, "input_data", arena_vec![ArenaVec::from_slice(&input_data)]);
    for (name, v) in &buffers { hints.insert(bytecode, name, arena_vec![ArenaVec::from_slice(v)]); }
    let witness = ExecutionWitness { preamble_memory_len: PREAMBLE_MEMORY_LEN, hints, min_table_log_n_rows: Default::default() };
    let proof = prove_execution(bytecode, &public_input, &witness, &default_whir_config(log_inv_rate), false).map_err(|e| format!("{e:?}"))?;
    Ok(Ed25519LeafProof { input_data, n_seg: rows.len(), n_groups, proof })
}
/// Verify a leaf proof WITHOUT binding it to a statement: proves only that SOME (rows, seg_index,
/// blob_id) produced a valid leaf. Blob mode re-binds seg_index/blob_id/count in-circuit, so it uses
/// this internally; a standalone caller who cares which rows were signed must use
/// `verify_ed25519_leaf_for`.
pub fn verify_ed25519_leaf(leaf: &Ed25519LeafProof) -> Result<InnerVerified, ProofError> {
    if leaf.input_data.first() != Some(&F::from_usize(ED25519_LEAF_FLAG)) { return Err(ProofError::InvalidProof); }
    verify_inner(leaf.input_data.clone(), leaf.proof.proof.clone())
}

/// Verify a leaf proof AND bind it to the caller's statement: the proof must be for exactly these
/// rows at this seg_index and blob_id (codex finding #5).
pub fn verify_ed25519_leaf_for(leaf: &Ed25519LeafProof, rows: &[SigRow], seg_index: usize, blob_id: &[F; 4]) -> Result<InnerVerified, ProofError> {
    if leaf.input_data != expected_leaf_input_data(rows, seg_index, blob_id) { return Err(ProofError::InvalidProof); }
    verify_ed25519_leaf(leaf)
}

pub fn ed25519_blob_input_data(digests: &[[F; DIGEST_LEN]], n_total: usize, blob_id: &[F; 4], bytecode_claim_flat: &[F]) -> Vec<F> {
    let claim_padded = bytecode_claim_flat.len().next_multiple_of(DIGEST_LEN);
    let domsep_offset = BYTECODE_CLAIM_OFFSET + claim_padded;
    let digests_offset = domsep_offset + DIGEST_LEN;
    let mut data = vec![F::ZERO; digests_offset + (digests.len() + 1) * DIGEST_LEN];
    data[0] = F::from_usize(ED25519_BLOB_FLAG);
    data[1] = F::from_usize(digests.len());
    data[BYTECODE_CLAIM_OFFSET..][..bytecode_claim_flat.len()].copy_from_slice(bytecode_claim_flat);
    data[domsep_offset..][..DIGEST_LEN].copy_from_slice(&fiat_shamir_domain_sep(get_aggregation_bytecode()));
    for (i, d) in digests.iter().enumerate() { data[digests_offset + i * DIGEST_LEN..][..DIGEST_LEN].copy_from_slice(d); }
    let trailer = digests_offset + digests.len() * DIGEST_LEN;
    data[trailer] = F::from_usize(n_total);
    data[trailer + 1..trailer + 5].copy_from_slice(blob_id);
    data
}

pub fn prove_ed25519_blob(leaves: &[Ed25519LeafProof], blob_id: &[F; 4], log_inv_rate: usize) -> Result<Ed25519BlobProof, String> {
    if leaves.is_empty() || leaves.len() > MAX_RECURSIONS { return Err("blob: 1..=MAX_RECURSIONS leaves".into()); }
    let bytecode = get_aggregation_bytecode();
    let verified: Vec<InnerVerified> = leaves.iter().map(|l| verify_ed25519_leaf(l).map_err(|e| format!("leaf: {e:?}"))).collect::<Result<_, _>>()?;
    let n_total: usize = leaves.iter().map(|l| l.n_seg).sum();
    let reduced = reduce_bytecode_claims(&verified);
    let digests: Vec<[F; DIGEST_LEN]> = verified.iter().map(|v| v.input_data_hash).collect();
    let input_data = ed25519_blob_input_data(&digests, n_total, blob_id, &flatten_bytecode_claim(&reduced.final_claim));
    let public_input = poseidon_hash_slice(&input_data);
    let bytecode_value_hint_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(v.bytecode_evaluation.value.as_basis_coefficients_slice())).collect();
    let component_layout_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(&v.input_data)).collect();
    let proof_transcript_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(&v.raw_proof.transcript)).collect();
    let table_sort_perm_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| v.sorted_table_perm.iter().map(|&i| F::from_usize(i)).collect()).collect();
    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(verified.iter().map(|v| &v.raw_proof));
    let mut hints = Hints::default();
    hints.insert(bytecode, "input_data_num_chunks", arena_vec![arena_vec![F::from_usize(input_data.len() / DIGEST_LEN)]]);
    hints.insert(bytecode, "input_data", arena_vec![ArenaVec::from_slice(&input_data)]);
    hints.insert(bytecode, "bytecode_value_hint", bytecode_value_hint_blobs);
    hints.insert(bytecode, "component_layout", component_layout_blobs);
    hints.insert(bytecode, "proof_transcript_size", proof_transcript_blobs.iter().map(|b| arena_vec![F::from_usize(b.len())]).collect());
    hints.insert(bytecode, "proof_transcript", proof_transcript_blobs);
    hints.insert(bytecode, "table_sort_perm", table_sort_perm_blobs);
    hints.insert(bytecode, "merkle_leaf", merkle_leaf_blobs);
    hints.insert(bytecode, "merkle_path", merkle_path_blobs);
    hints.insert(bytecode, "bytecode_sumcheck_proof", arena_vec![ArenaVec::from_slice(&reduced.sumcheck_transcript)]);
    let witness = ExecutionWitness { preamble_memory_len: PREAMBLE_MEMORY_LEN, hints, min_table_log_n_rows: Default::default() };
    let proof = prove_execution(bytecode, &public_input, &witness, &default_whir_config(log_inv_rate), false).map_err(|e| format!("{e:?}"))?;
    Ok(Ed25519BlobProof { input_data, bytecode_claim: reduced.final_claim, proof })
}

/// Verify a blob proof against reader-recomputed leaf digests: the reduced bytecode claim's value is
/// recomputed from the real bytecode (never trusted), then the input data is rebuilt and the proof verified.
pub fn verify_ed25519_blob(blob: &Ed25519BlobProof, leaf_digests: &[[F; DIGEST_LEN]], n_total: usize, blob_id: &[F; 4]) -> Result<InnerVerified, ProofError> {
    let claim = rebuild_bytecode_claim(blob.bytecode_claim.point.clone()).map_err(|_| ProofError::InvalidProof)?;
    let input_data = ed25519_blob_input_data(leaf_digests, n_total, blob_id, &flatten_bytecode_claim(&claim));
    if input_data != blob.input_data { return Err(ProofError::InvalidProof); }
    verify_inner(input_data, blob.proof.proof.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::init_aggregation_bytecode;
    use lean_prover::ed25519_leaf::rows_from_json;

    /// Two real leaves (16 signatures each) proven in leaf mode, then a blob proof verifying both in-circuit,
    /// verified natively against reader-recomputed leaf digests.
    // The leaf half proves+verifies+binds; the blob half runs the recursion verifier in-circuit, which
    // is currently blocked for 9 wide tables (recursion `powers()` caps at 400 WHIR statements, and the
    // proof exceeds ~8 GB). Ignored until the recursion/WHIR verifier is scaled. Run with --ignored.
    #[test]
    #[ignore = "blob mode blocked on recursion powers() cap + RAM for 9 wide tables; leaf half is exercised by lean_prover::ed25519_leaf tests"]
    fn test_ed25519_leaves_then_blob() {
        init_aggregation_bytecode();
        let path = format!("{}/.cache/fb-stacks/datasets/sigs-25k-diverse.json", std::env::var("HOME").unwrap());
        let rows = rows_from_json(&path);
        let per_leaf: usize = std::env::var("BLOB_LEAF_N").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
        let k: usize = std::env::var("BLOB_K").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
        let blob_id = [F::from_usize(9), F::from_usize(8), F::from_usize(7), F::from_usize(6)];
        let mut leaves = vec![];
        for c in 0..k {
            let chunk = &rows[c * per_leaf..(c + 1) * per_leaf];
            let t = std::time::Instant::now();
            let leaf = prove_ed25519_leaf(chunk, c, &blob_id, 1).expect("leaf proof");
            println!("leaf {c}: {} sigs, {} signers, proof {:.1} s", leaf.n_seg, leaf.n_groups, t.elapsed().as_secs_f32());
            assert_eq!(leaf.input_data, expected_leaf_input_data(chunk, c, &blob_id), "reader-side leaf input data");
            verify_ed25519_leaf_for(&leaf, chunk, c, &blob_id).expect("leaf verifies and binds to its statement");
            leaves.push(leaf);
        }
        let t = std::time::Instant::now();
        let blob = prove_ed25519_blob(&leaves, &blob_id, 1).expect("blob proof");
        println!("blob of {k} leaves: proof {:.1} s, {} cycles", t.elapsed().as_secs_f32(), blob.proof.metadata.as_ref().map(|m| m.cycles).unwrap_or(0));
        let digests: Vec<[F; DIGEST_LEN]> = (0..k).map(|c| poseidon_hash_slice(&expected_leaf_input_data(&rows[c * per_leaf..(c + 1) * per_leaf], c, &blob_id))).collect();
        let n_total: usize = leaves.iter().map(|l| l.n_seg).sum();
        verify_ed25519_blob(&blob, &digests, n_total, &blob_id).expect("blob verifies");
        // a wrong blob_id must not verify
        assert!(verify_ed25519_blob(&blob, &digests, n_total, &[F::ZERO; 4]).is_err());
    }
}
