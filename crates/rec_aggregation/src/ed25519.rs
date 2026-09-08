//! ed25519 leaves and nodes as modes of the recursion program (Phase E part 2).
//!
//! Leaf input data: `[LEAF_FLAG, n_seg, 0×6] ‖ zero bytecode claim (padded) ‖ fiat-shamir domsep ‖ meta ‖ root_seg`
//! (public input = its Poseidon hash; `meta` binds n_seg, seg_index, version and blob_id).
//!
//! Node input data: `[NODE_FLAG, K, 0×6] ‖ reduced claim ‖ domsep ‖ K child digests`, where each child is
//! a LEAF or a NODE proof (any depth, any mix). The node verifies each child proof in-circuit and reduces
//! their bytecode claims; it does NOT bind positions or blob ids — the READER does (spec F7): it
//! recomputes every leaf digest from its own (rows_k, seg_index = k, blob_id) and rebuilds the tree of
//! node digests (`verify_ed25519_node`), so a reordered, duplicated, foreign or missing leaf is rejected
//! there. This is what makes the tree shape free: a 49-leaf blob is e.g. 49 → 13 → 4 → 1 at fan-in 4,
//! and an epoch is a node over per-blob nodes.

use crate::bytecode_claims::{flatten_bytecode_claim, reduce_bytecode_claims};
use crate::compilation::{BYTECODE_CLAIM_OFFSET, ED25519_LEAF_FLAG, ED25519_NODE_FLAG, MAX_RECURSIONS, PREAMBLE_MEMORY_LEN, get_aggregation_bytecode};
use crate::single_message_aggregation::{extract_merkle_hint_blobs, rebuild_bytecode_claim};
use crate::{InnerVerified, verify_inner, verify_inner_with};
use backend::*;
use lean_prover::ed25519_leaf::{MAX_LEAF_SIGS, SigRow, canonical_rows, leaf_hint_buffers, leaf_meta, root_seg};
use lean_prover::prove_execution::{ExecutionProof, prove_execution, prove_execution_with_profile};
use lean_prover::*;
use lean_vm::*;

pub struct Ed25519LeafProof {
    pub input_data: Vec<F>,
    pub n_seg: usize,
    pub n_groups: usize,
    pub proof: ExecutionProof,
}

fn zero_bytecode_claim_flat() -> Vec<F> {
    let bytecode = get_aggregation_bytecode();
    let point = MultilinearPoint(vec![EF::ZERO; bytecode.cumulated_n_vars()]);
    flatten_bytecode_claim(&rebuild_bytecode_claim(point).expect("zero claim"))
}

/// The leaf's input data (what the reader recomputes from the decoded columns and the leaf parameters).
pub fn ed25519_leaf_input_data(n_seg: usize, meta: &[F; 16], root: &[F; 8]) -> Vec<F> {
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
/// Reader side: the leaf input data from the rows (canonical order) and the leaf parameters.
/// Bounded integers: `F::from_usize` reduces mod p, so counts/indices are validated here, on every
/// reader entry point, or N and N + p would alias.
pub fn expected_leaf_input_data(rows: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Result<Vec<F>, ProofError> {
    if rows.is_empty() || rows.len() > MAX_LEAF_SIGS || seg_index >= (1 << 30) { return Err(ProofError::InvalidProof); }
    let sorted = canonical_rows(rows);
    Ok(ed25519_leaf_input_data(sorted.len(), &leaf_meta(sorted.len(), seg_index, blob_id), &root_seg(&sorted)))
}
/// Reader side: the leaf digest (what a parent node's input data carries for this leaf).
pub fn expected_leaf_digest(rows: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Result<[F; DIGEST_LEN], ProofError> {
    Ok(poseidon_hash_slice(&expected_leaf_input_data(rows, seg_index, blob_id)?))
}

pub fn prove_ed25519_leaf(rows: &[SigRow], seg_index: usize, blob_id: &[F; 9], log_inv_rate: usize) -> Result<Ed25519LeafProof, String> {
    let bytecode = get_aggregation_bytecode();
    let (rows, n_groups, meta, root, buffers) = leaf_hint_buffers(rows, seg_index, blob_id)?;
    let input_data = ed25519_leaf_input_data(rows.len(), &meta, &root);
    let public_input = poseidon_hash_slice(&input_data);
    let mut hints = Hints::default();
    hints.insert(bytecode, "input_data_num_chunks", arena_vec![arena_vec![F::from_usize(input_data.len() / DIGEST_LEN)]]);
    hints.insert(bytecode, "input_data", arena_vec![ArenaVec::from_slice(&input_data)]);
    for (name, v) in &buffers { hints.insert(bytecode, name, arena_vec![ArenaVec::from_slice(v)]); }
    let witness = ExecutionWitness { preamble_memory_len: PREAMBLE_MEMORY_LEN, hints, min_table_log_n_rows: Default::default() };
    let proof = prove_execution(bytecode, &public_input, &witness, &default_whir_config(log_inv_rate), vm_profiler()).map_err(|e| format!("{e:?}"))?;
    Ok(Ed25519LeafProof { input_data, n_seg: rows.len(), n_groups, proof })
}
/// Verify a leaf proof WITHOUT binding it to a statement: proves only that SOME (rows, seg_index,
/// blob_id) produced a valid leaf. Used by the node prover (the node's reader re-binds every leaf);
/// a caller who cares which rows were signed must use `verify_ed25519_leaf_for`.
pub(crate) fn verify_ed25519_leaf(leaf: &Ed25519LeafProof) -> Result<InnerVerified, ProofError> {
    if leaf.input_data.first() != Some(&F::from_usize(ED25519_LEAF_FLAG)) { return Err(ProofError::InvalidProof); }
    verify_inner(leaf.input_data.clone(), leaf.proof.proof.clone())
}

/// Verify a leaf proof AND bind it to the caller's statement: the proof must be for exactly these
/// rows at this seg_index and blob_id.
pub fn verify_ed25519_leaf_for(leaf: &Ed25519LeafProof, rows: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Result<InnerVerified, ProofError> {
    if leaf.input_data != expected_leaf_input_data(rows, seg_index, blob_id)? { return Err(ProofError::InvalidProof); }
    verify_ed25519_leaf(leaf)
}

/// `ED_VM_PROFILE=1` turns on the VM's per-function cycle profiler (report in `proof.metadata.profiling_report`).
fn vm_profiler() -> bool { std::env::var("ED_VM_PROFILE").is_ok() }

// ============================ node: K child proofs (leaves or nodes) ============================

/// The shape a reader needs to rebuild a node's digest: a leaf contributes nothing (its digest comes
/// from data), an inner node contributes its bytecode claim (point AND value, used as carried: each
/// inner claim sits inside the child's input data that the parent hashed and verified in-circuit, and
/// every inner value is folded by the parent's reduction into the top claim, whose value the verifier
/// recomputes from the real bytecode) and its own children's shapes.
#[derive(Clone)]
pub enum NodeShape {
    Leaf,
    Node { claim: Evaluation<EF>, children: Vec<NodeShape> },
}

pub struct Ed25519NodeProof {
    pub input_data: Vec<F>,
    pub bytecode_claim: Evaluation<EF>,
    /// One entry per child, in input-data order.
    pub shape: Vec<NodeShape>,
    pub proof: ExecutionProof,
}

pub enum Ed25519Child<'a> {
    Leaf(&'a Ed25519LeafProof),
    Node(&'a Ed25519NodeProof),
}

/// Reader-side statement tree: what the reader believes each child is. Leaves carry the rows the
/// reader decoded from the blob, in blob order, with their position and blob id.
pub enum Statement<'a> {
    Leaf { rows: &'a [SigRow], seg_index: usize, blob_id: [F; 9] },
    Node(Vec<Statement<'a>>),
}

/// Leaf statements from explicit per-leaf slices (tests; a reader uses `verify_ed25519_blob`, which
/// derives the leaves from the full decoded row list so no subset can be verified by accident).
pub(crate) fn leaf_statements<'a>(rows_per_leaf: &[&'a [SigRow]], blob_id: &[F; 9]) -> Vec<Statement<'a>> {
    rows_per_leaf.iter().enumerate().map(|(k, rows)| Statement::Leaf { rows, seg_index: k, blob_id: *blob_id }).collect()
}

/// READER API for one blob. `rows` = every decoded signed message of the blob, in blob order;
/// leaf k = rows[k·S, (k+1)·S). The leaves are assigned to the proof's tree shape in pre-order, so
/// leaf k always gets seg_index k whatever the shape; a shape with a different number of leaves is
/// rejected, so every decoded row is covered by exactly one leaf.
pub fn blob_statement_tree<'a>(rows: &'a [SigRow], leaf_size: usize, blob_id: &[F; 9], shape: &[NodeShape]) -> Result<Vec<Statement<'a>>, ProofError> {
    if rows.is_empty() || leaf_size == 0 || leaf_size > MAX_LEAF_SIGS { return Err(ProofError::InvalidProof); }
    let chunks: Vec<&'a [SigRow]> = rows.chunks(leaf_size).collect();
    const MAX_DEPTH: usize = 16; // an attacker-chosen shape must not drive the reader's recursion
    fn build<'a>(shape: &NodeShape, chunks: &[&'a [SigRow]], next: &mut usize, blob_id: &[F; 9], depth: usize) -> Result<Statement<'a>, ProofError> {
        if depth > MAX_DEPTH { return Err(ProofError::InvalidProof); }
        match shape {
            NodeShape::Leaf => { let k = *next; *next += 1; let rows = *chunks.get(k).ok_or(ProofError::InvalidProof)?; Ok(Statement::Leaf { rows, seg_index: k, blob_id: *blob_id }) }
            NodeShape::Node { children, .. } => {
                if children.is_empty() || children.len() > MAX_RECURSIONS { return Err(ProofError::InvalidProof); }
                Ok(Statement::Node(children.iter().map(|c| build(c, chunks, next, blob_id, depth + 1)).collect::<Result<_, _>>()?))
            }
        }
    }
    if shape.is_empty() || shape.len() > MAX_RECURSIONS { return Err(ProofError::InvalidProof); }
    let mut next = 0;
    let stmts = shape.iter().map(|s| build(s, &chunks, &mut next, blob_id, 1)).collect::<Result<Vec<_>, _>>()?;
    if next != chunks.len() { return Err(ProofError::InvalidProof); }
    Ok(stmts)
}
/// Verify a node proof as the proof of one whole blob (see `blob_statement_tree`).
pub fn verify_ed25519_blob(node: &Ed25519NodeProof, rows: &[SigRow], leaf_size: usize, blob_id: &[F; 9]) -> Result<InnerVerified, ProofError> {
    let stmts = blob_statement_tree(rows, leaf_size, blob_id, &node.shape)?;
    verify_ed25519_node(node, &stmts)
}

pub fn ed25519_node_input_data(child_digests: &[[F; DIGEST_LEN]], bytecode_claim_flat: &[F]) -> Vec<F> {
    let claim_padded = bytecode_claim_flat.len().next_multiple_of(DIGEST_LEN);
    let domsep_offset = BYTECODE_CLAIM_OFFSET + claim_padded;
    let digests_offset = domsep_offset + DIGEST_LEN;
    let mut data = vec![F::ZERO; digests_offset + child_digests.len() * DIGEST_LEN];
    data[0] = F::from_usize(ED25519_NODE_FLAG);
    data[1] = F::from_usize(child_digests.len());
    data[BYTECODE_CLAIM_OFFSET..][..bytecode_claim_flat.len()].copy_from_slice(bytecode_claim_flat);
    data[domsep_offset..][..DIGEST_LEN].copy_from_slice(&fiat_shamir_domain_sep(get_aggregation_bytecode()));
    for (i, d) in child_digests.iter().enumerate() { data[digests_offset + i * DIGEST_LEN..][..DIGEST_LEN].copy_from_slice(d); }
    data
}

/// Reader side: the digest of a statement subtree, given the shape carried by the proof.
pub fn expected_digest(stmt: &Statement<'_>, shape: &NodeShape) -> Result<[F; DIGEST_LEN], ProofError> {
    match (stmt, shape) {
        (Statement::Leaf { rows, seg_index, blob_id }, NodeShape::Leaf) => expected_leaf_digest(rows, *seg_index, blob_id),
        (Statement::Node(children), NodeShape::Node { claim, children: shapes }) => {
            if children.len() != shapes.len() || children.is_empty() || children.len() > MAX_RECURSIONS { return Err(ProofError::InvalidProof); }
            if claim.point.0.len() != get_aggregation_bytecode().cumulated_n_vars() { return Err(ProofError::InvalidProof); }
            let digests: Vec<[F; DIGEST_LEN]> = children.iter().zip(shapes).map(|(c, s)| expected_digest(c, s)).collect::<Result<_, _>>()?;
            // the carried inner (point, value) is what the child committed to; a wrong pair changes this
            // digest (rejected at the top), and a false value would propagate into the top value, which
            // `verify_ed25519_node` recomputes. No bytecode evaluation is needed for inner nodes.
            Ok(poseidon_hash_slice(&ed25519_node_input_data(&digests, &flatten_bytecode_claim(claim))))
        }
        _ => Err(ProofError::InvalidProof),
    }
}

/// Reader-side verification of the PUBLISHED top node against the reader's own statement tree:
/// rebuilds every child digest (leaves from data, inner nodes from their children + carried claim
/// point with the value recomputed), the node's input data and its reduced claim, then verifies the
/// proof under the TERMINAL profile (three base tables; a top node never runs an ed25519
/// precompile). A proof made under the full profile does not verify here, by domain separation.
pub fn verify_ed25519_node(node: &Ed25519NodeProof, children: &[Statement<'_>]) -> Result<InnerVerified, ProofError> {
    verify_ed25519_node_with(&PROFILE_TERMINAL, node, children)
}

pub(crate) fn verify_ed25519_node_with(profile: &Profile, node: &Ed25519NodeProof, children: &[Statement<'_>]) -> Result<InnerVerified, ProofError> {
    if children.len() != node.shape.len() || children.is_empty() || children.len() > MAX_RECURSIONS { return Err(ProofError::InvalidProof); }
    let digests: Vec<[F; DIGEST_LEN]> = children.iter().zip(&node.shape).map(|(c, s)| expected_digest(c, s)).collect::<Result<_, _>>()?;
    let claim = rebuild_bytecode_claim(node.bytecode_claim.point.clone()).map_err(|_| ProofError::InvalidProof)?;
    let input_data = ed25519_node_input_data(&digests, &flatten_bytecode_claim(&claim));
    if input_data != node.input_data { return Err(ProofError::InvalidProof); }
    verify_inner_with(profile, input_data, node.proof.proof.clone())
}

/// Verify a node proof against the statement its own input data encodes (the node prover uses it for
/// its children; the parent's reader re-binds everything).
pub(crate) fn verify_ed25519_node_self(node: &Ed25519NodeProof) -> Result<InnerVerified, ProofError> {
    if node.input_data.first() != Some(&F::from_usize(ED25519_NODE_FLAG)) { return Err(ProofError::InvalidProof); }
    let claim = rebuild_bytecode_claim(node.bytecode_claim.point.clone()).map_err(|_| ProofError::InvalidProof)?;
    let flat = flatten_bytecode_claim(&claim);
    if node.input_data.get(BYTECODE_CLAIM_OFFSET..BYTECODE_CLAIM_OFFSET + flat.len()) != Some(&flat[..]) { return Err(ProofError::InvalidProof); }
    verify_inner(node.input_data.clone(), node.proof.proof.clone())
}

/// Production defaults (measured 2026-09-07, M3 Max): a 2,048-signature leaf proves in ≈ 28 s at
/// ≈ 13 GB peak RSS (13.8 ms/signature; 256-signature leaves cost 25.8 ms/signature); the top node at
/// WHIR rate 1/8 is 443 KiB (588 KiB at rate 1/2) for 1.8× its proving time, and nobody verifies it
/// in-circuit, so only the published proof pays. Inner nodes stay at the leaf rate.
pub const DEFAULT_LEAF_SIGS: usize = 2048;
pub const DEFAULT_LEAF_LOG_INV_RATE: usize = 1;
pub const DEFAULT_TOP_LOG_INV_RATE: usize = 3;
pub const NODE_FAN_IN: usize = 4;

/// PROVER API for one blob (the relayer's entry point): `rows` = every signed message of the blob in
/// blob order, `blob_id` = `blob_id_cells(versioned_hash)`. Leaves of `leaf_size` rows (the last one
/// shorter) are proved in order, then reduced by nodes of `NODE_FAN_IN` children until one node
/// remains, which is proved at `top_log_inv_rate`. The returned node's shape is exactly what
/// `verify_ed25519_blob(node, rows, leaf_size, blob_id)` rebuilds on the reader side (pre-order
/// leaf assignment), so the reader needs nothing from the prover but the proof and `leaf_size`.
/// A single leaf still gets a top node, so the published artifact is always a node proof.
pub fn prove_ed25519_blob(rows: &[SigRow], blob_id: &[F; 9], leaf_size: usize, leaf_log_inv_rate: usize, top_log_inv_rate: usize, log: &dyn Fn(String)) -> Result<Ed25519NodeProof, String> {
    if rows.is_empty() { return Err("prove_ed25519_blob: no rows".into()); }
    if leaf_size == 0 || leaf_size > MAX_LEAF_SIGS { return Err(format!("prove_ed25519_blob: leaf_size must be 1..={MAX_LEAF_SIGS}")); }
    let leaves: Vec<Ed25519LeafProof> = rows.chunks(leaf_size).enumerate().map(|(k, chunk)| {
        let t = std::time::Instant::now();
        let leaf = prove_ed25519_leaf(chunk, k, blob_id, leaf_log_inv_rate)?;
        log(format!("leaf {k}: {} sigs, {} signers, {:.1} s, {} KiB", leaf.n_seg, leaf.n_groups, t.elapsed().as_secs_f32(), leaf.proof.proof.proof_size_fe() * 4 / 1024));
        Ok(leaf)
    }).collect::<Result<_, String>>()?;
    // level 0 = the leaves; each further level groups NODE_FAN_IN consecutive children into a node
    let mut level: Vec<Ed25519NodeProof> = Vec::new();
    let mut first = true;
    loop {
        let n_children = if first { leaves.len() } else { level.len() };
        let top = n_children <= NODE_FAN_IN;
        let rate = if top { top_log_inv_rate } else { leaf_log_inv_rate };
        let mut next: Vec<Ed25519NodeProof> = Vec::new();
        for g in 0..n_children.div_ceil(NODE_FAN_IN) {
            let lo = g * NODE_FAN_IN;
            let hi = (lo + NODE_FAN_IN).min(n_children);
            let children: Vec<Ed25519Child<'_>> = if first { leaves[lo..hi].iter().map(Ed25519Child::Leaf).collect() } else { level[lo..hi].iter().map(Ed25519Child::Node).collect() };
            let t = std::time::Instant::now();
            let node = if top { prove_ed25519_top(&children, rate)? } else { prove_ed25519_node(&children, rate)? };
            log(format!("node over {} {}: rate 1/{}, {:.1} s, {} cycles, {} KiB{}", hi - lo, if first { "leaves" } else { "nodes" }, 1 << rate, t.elapsed().as_secs_f32(), node.proof.metadata.as_ref().map(|m| m.cycles).unwrap_or(0), node.proof.proof.proof_size_fe() * 4 / 1024, if top { " (top, terminal profile)" } else { "" }));
            next.push(node);
        }
        first = false;
        if next.len() == 1 { return Ok(next.pop().unwrap()); }
        level = next;
    }
}

/// An INNER node (full profile: it is verified in-circuit by its parent).
pub fn prove_ed25519_node(children: &[Ed25519Child<'_>], log_inv_rate: usize) -> Result<Ed25519NodeProof, String> {
    prove_ed25519_node_with(&PROFILE_FULL, children, log_inv_rate)
}

/// The PUBLISHED top node (terminal profile: verified natively by readers, never in-circuit).
pub fn prove_ed25519_top(children: &[Ed25519Child<'_>], log_inv_rate: usize) -> Result<Ed25519NodeProof, String> {
    prove_ed25519_node_with(&PROFILE_TERMINAL, children, log_inv_rate)
}

pub fn prove_ed25519_node_with(profile: &Profile, children: &[Ed25519Child<'_>], log_inv_rate: usize) -> Result<Ed25519NodeProof, String> {
    if children.is_empty() || children.len() > MAX_RECURSIONS { return Err(format!("node: 1..={MAX_RECURSIONS} children")); }
    let mut verified = Vec::with_capacity(children.len());
    let mut shape = Vec::with_capacity(children.len());
    for (i, child) in children.iter().enumerate() {
        match child {
            Ed25519Child::Leaf(l) => { verified.push(verify_ed25519_leaf(l).map_err(|e| format!("child {i} (leaf): {e:?}"))?); shape.push(NodeShape::Leaf); }
            Ed25519Child::Node(n) => { verified.push(verify_ed25519_node_self(n).map_err(|e| format!("child {i} (node): {e:?}"))?); shape.push(NodeShape::Node { claim: n.bytecode_claim.clone(), children: n.shape.clone() }); }
        }
    }
    prove_node_from_verified(profile, verified, shape, log_inv_rate)
}

/// The node prover proper, from natively verified children. Separate so a test can feed it a
/// tampered child and check the IN-CIRCUIT verifier rejects it. Children are always verified under
/// the FULL profile (their transcripts are re-verified in-circuit by the full-set recursion program);
/// `profile` is the profile of THIS node's proof.
pub(crate) fn prove_node_from_verified(profile: &Profile, verified: Vec<InnerVerified>, shape: Vec<NodeShape>, log_inv_rate: usize) -> Result<Ed25519NodeProof, String> {
    if verified.len() != shape.len() || verified.is_empty() || verified.len() > MAX_RECURSIONS { return Err("node: children and shape must match, 1..=MAX_RECURSIONS".into()); }
    for v in &verified { assert_eq!(v.sorted_table_perm.len(), N_TABLES, "a child must be a full-profile proof"); }
    let bytecode = get_aggregation_bytecode();
    let reduced = reduce_bytecode_claims(&verified);
    let digests: Vec<[F; DIGEST_LEN]> = verified.iter().map(|v| v.input_data_hash).collect();
    let input_data = ed25519_node_input_data(&digests, &flatten_bytecode_claim(&reduced.final_claim));
    let public_input = poseidon_hash_slice(&input_data);
    let bytecode_value_hint_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(v.bytecode_evaluation.value.as_basis_coefficients_slice())).collect();
    let component_num_chunks_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| arena_vec![F::from_usize(v.input_data.len() / DIGEST_LEN)]).collect();
    let component_layout_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(&v.input_data)).collect();
    let proof_transcript_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| ArenaVec::from_slice(&v.raw_proof.transcript)).collect();
    let table_sort_perm_blobs: ArenaVec<ArenaVec<F>> = verified.iter().map(|v| v.sorted_table_perm.iter().map(|&i| F::from_usize(i)).collect()).collect();
    let (merkle_leaf_blobs, merkle_path_blobs) = extract_merkle_hint_blobs(verified.iter().map(|v| &v.raw_proof));
    let mut hints = Hints::default();
    hints.insert(bytecode, "input_data_num_chunks", arena_vec![arena_vec![F::from_usize(input_data.len() / DIGEST_LEN)]]);
    hints.insert(bytecode, "input_data", arena_vec![ArenaVec::from_slice(&input_data)]);
    hints.insert(bytecode, "bytecode_value_hint", bytecode_value_hint_blobs);
    hints.insert(bytecode, "component_num_chunks", component_num_chunks_blobs);
    hints.insert(bytecode, "component_layout", component_layout_blobs);
    hints.insert(bytecode, "proof_transcript_size", proof_transcript_blobs.iter().map(|b| arena_vec![F::from_usize(b.len())]).collect());
    hints.insert(bytecode, "proof_transcript", proof_transcript_blobs);
    hints.insert(bytecode, "table_sort_perm", table_sort_perm_blobs);
    hints.insert(bytecode, "merkle_leaf", merkle_leaf_blobs);
    hints.insert(bytecode, "merkle_path", merkle_path_blobs);
    hints.insert(bytecode, "bytecode_sumcheck_proof", arena_vec![ArenaVec::from_slice(&reduced.sumcheck_transcript)]);
    let witness = ExecutionWitness { preamble_memory_len: PREAMBLE_MEMORY_LEN, hints, min_table_log_n_rows: Default::default() };
    let proof = prove_execution_with_profile(profile, bytecode, &public_input, &witness, &default_whir_config(log_inv_rate), vm_profiler()).map_err(|e| format!("{e:?}"))?;
    Ok(Ed25519NodeProof { input_data, bytecode_claim: reduced.final_claim, shape, proof })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compilation::init_aggregation_bytecode;
    use lean_prover::ed25519_leaf::rows_from_json;

    fn dataset() -> Vec<SigRow> { rows_from_json(&format!("{}/.cache/fb-stacks/datasets/sigs-25k-diverse.json", std::env::var("HOME").unwrap())) }
    fn env(name: &str, default: usize) -> usize { std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default) }
    fn per_for_neg(rows: &[SigRow], per_leaf: usize, k: usize) -> Vec<&[SigRow]> { (0..k).map(|c| &rows[c * per_leaf..(c + 1) * per_leaf]).collect() }
    fn prove_leaves(rows: &[SigRow], per_leaf: usize, k: usize, first: usize, blob_id: &[F; 9]) -> Vec<Ed25519LeafProof> {
        (0..k).map(|c| {
            let chunk = &rows[(first + c) * per_leaf..(first + c + 1) * per_leaf];
            let t = std::time::Instant::now();
            let leaf = prove_ed25519_leaf(chunk, c, blob_id, env("LEAF_RATE", 1)).expect("leaf proof");
            println!("leaf {c}: {} sigs, {} signers, proof {:.1} s, {} cycles, {} KiB", leaf.n_seg, leaf.n_groups, t.elapsed().as_secs_f32(), leaf.proof.metadata.as_ref().map(|m| m.cycles).unwrap_or(0), leaf.proof.proof.proof_size_fe() * 4 / 1024);
            let tv = std::time::Instant::now();
            verify_ed25519_leaf_for(&leaf, chunk, c, blob_id).expect("leaf verifies and binds to its statement");
            println!("verify leaf {c} (native, reader-side): {:.3} s", tv.elapsed().as_secs_f32());
            leaf
        }).collect()
    }

    /// K leaf proofs → one node (NODE_K children, NODE_LEAF_N sigs each). Reader-verified; every way of
    /// lying about the statement is rejected at the reader.
    #[test]
    fn test_ed25519_node_of_leaves() {
        init_aggregation_bytecode();
        let rows = dataset();
        let per_leaf = env("NODE_LEAF_N", 16);
        let k = env("NODE_K", 2);
        let blob_id = std::array::from_fn(|i| F::from_usize(9 + i));
        let leaves = prove_leaves(&rows, per_leaf, k, 0, &blob_id);
        let t = std::time::Instant::now();
        let children: Vec<Ed25519Child<'_>> = leaves.iter().map(Ed25519Child::Leaf).collect();
        let node = prove_ed25519_top(&children, env("NODE_RATE", 1)).expect("node proof");
        // a full-profile proof of the same statement must NOT verify as a published top (domain separation)
        let inner = prove_ed25519_node(&children, 1).expect("inner node proof");
        assert!(verify_ed25519_node(&inner, &leaf_statements(&per_for_neg(&rows, per_leaf, k), &blob_id)).is_err(), "a full-profile proof must not pass the terminal verifier");
        println!("full-profile node (inner): {} KiB; terminal top: {} KiB", inner.proof.proof.proof_size_fe() * 4 / 1024, node.proof.proof.proof_size_fe() * 4 / 1024);
        println!("node of {k} leaves (rate 1/{}): proof {:.1} s, {} cycles, {} KiB", 1 << env("NODE_RATE", 1), t.elapsed().as_secs_f32(), node.proof.metadata.as_ref().map(|m| m.cycles).unwrap_or(0), node.proof.proof.proof_size_fe() * 4 / 1024);
        if let Some(report) = node.proof.metadata.as_ref().and_then(|m| m.profiling_report.as_ref()) { println!("=== VM PROFILE (node) ===\n{report}\n=== END PROFILE ==="); }
        let per: Vec<&[SigRow]> = (0..k).map(|c| &rows[c * per_leaf..(c + 1) * per_leaf]).collect();
        let tv = std::time::Instant::now();
        verify_ed25519_node(&node, &leaf_statements(&per, &blob_id)).expect("node verifies from reader-recomputed leaf digests");
        println!("verify node (native, reader-side, incl. leaf digests + top bytecode claim): {:.3} s", tv.elapsed().as_secs_f32());
        verify_ed25519_blob(&node, &rows[..k * per_leaf], per_leaf, &blob_id).expect("the blob reader API verifies from the full row list");
        assert!(verify_ed25519_blob(&node, &rows[..k * per_leaf - 1], per_leaf, &blob_id).is_err(), "a missing row must be rejected");
        assert!(verify_ed25519_blob(&node, &rows[1..k * per_leaf + 1], per_leaf, &blob_id).is_err(), "shifted rows must be rejected");
        assert!(verify_ed25519_blob(&node, &rows[..(k + 1) * per_leaf], per_leaf, &blob_id).is_err(), "extra rows (an uncovered leaf) must be rejected");
        // wrong blob_id
        assert!(verify_ed25519_node(&node, &leaf_statements(&per, &[F::ZERO; 9])).is_err(), "blob_id must be bound");
        if k >= 2 {
            // two leaves swapped (positions are bound through seg_index in each leaf digest)
            let mut swapped = per.clone(); swapped.swap(0, 1);
            assert!(verify_ed25519_node(&node, &leaf_statements(&swapped, &blob_id)).is_err(), "leaf position must be bound");
            // the same leaf twice
            let dup: Vec<&[SigRow]> = (0..k).map(|_| per[0]).collect();
            assert!(verify_ed25519_node(&node, &leaf_statements(&dup, &blob_id)).is_err(), "a duplicated leaf must be rejected");
        }
        // one row missing from a leaf (wrong n)
        let mut short = per.clone(); short[0] = &per[0][..per[0].len() - 1];
        assert!(verify_ed25519_node(&node, &leaf_statements(&short, &blob_id)).is_err(), "row count must be bound");
        // wrong child count
        assert!(verify_ed25519_node(&node, &leaf_statements(&per[..k - 1], &blob_id)).is_err() || k == 1, "child count must be bound");
    }

    /// Three levels with a mixed node: 4 leaves → A = (l0, l1), B = (l2, l3) → top = (A, B); and a
    /// mixed top' = (A, l2, l3). Reader-verified through the statement tree; subtree swap and a mutated
    /// inner claim point are rejected.
    #[test]
    fn test_ed25519_node_tree() {
        init_aggregation_bytecode();
        let rows = dataset();
        let per_leaf = env("NODE_LEAF_N", 16);
        let blob_id: [F; 9] = std::array::from_fn(|i| F::from_usize(100 + i));
        let leaves = prove_leaves(&rows, per_leaf, 4, 0, &blob_id);
        let t = std::time::Instant::now();
        let a = prove_ed25519_node(&[Ed25519Child::Leaf(&leaves[0]), Ed25519Child::Leaf(&leaves[1])], 1).expect("node A");
        let b = prove_ed25519_node(&[Ed25519Child::Leaf(&leaves[2]), Ed25519Child::Leaf(&leaves[3])], 1).expect("node B");
        let top = prove_ed25519_top(&[Ed25519Child::Node(&a), Ed25519Child::Node(&b)], 1).expect("top node");
        println!("tree 4 leaves → 2 nodes → top: {:.1} s (top {} cycles, {} KiB)", t.elapsed().as_secs_f32(), top.proof.metadata.as_ref().map(|m| m.cycles).unwrap_or(0), top.proof.proof.proof_size_fe() * 4 / 1024);
        let per: Vec<&[SigRow]> = (0..4).map(|c| &rows[c * per_leaf..(c + 1) * per_leaf]).collect();
        let leaf = |k: usize| Statement::Leaf { rows: per[k], seg_index: k, blob_id };
        let stmt = vec![Statement::Node(vec![leaf(0), leaf(1)]), Statement::Node(vec![leaf(2), leaf(3)])];
        verify_ed25519_node(&top, &stmt).expect("tree verifies from reader-recomputed digests");
        verify_ed25519_blob(&top, &rows[..4 * per_leaf], per_leaf, &blob_id).expect("blob reader API assigns leaves to the tree in pre-order");
        // subtrees swapped
        let swapped = vec![Statement::Node(vec![leaf(2), leaf(3)]), Statement::Node(vec![leaf(0), leaf(1)])];
        assert!(verify_ed25519_node(&top, &swapped).is_err(), "subtree order must be bound");
        // a flat statement against a nested proof
        assert!(verify_ed25519_node(&top, &[leaf(0), leaf(1)]).is_err(), "shape must match");
        // a mutated inner claim point must not verify
        let mut top = top;
        if let NodeShape::Node { claim, .. } = &mut top.shape[0] { claim.point.0[0] += EF::ONE; }
        assert!(verify_ed25519_node(&top, &stmt).is_err(), "inner claim point must be bound");
        if let NodeShape::Node { claim, .. } = &mut top.shape[0] { claim.point.0[0] -= EF::ONE; }
        verify_ed25519_node(&top, &stmt).expect("restored");
        // a mutated inner claim VALUE (the carried value is used as-is for inner digests) must not verify
        if let NodeShape::Node { claim, .. } = &mut top.shape[0] { claim.value += EF::ONE; }
        assert!(verify_ed25519_node(&top, &stmt).is_err(), "inner claim value must be bound");
        if let NodeShape::Node { claim, .. } = &mut top.shape[0] { claim.value -= EF::ONE; }
        verify_ed25519_node(&top, &stmt).expect("restored again");
        // mixed node: (A, l2, l3)
        let t = std::time::Instant::now();
        let mixed = prove_ed25519_top(&[Ed25519Child::Node(&a), Ed25519Child::Leaf(&leaves[2]), Ed25519Child::Leaf(&leaves[3])], 1).expect("mixed node");
        println!("mixed node (A, l2, l3): {:.1} s", t.elapsed().as_secs_f32());
        verify_ed25519_node(&mixed, &[Statement::Node(vec![leaf(0), leaf(1)]), leaf(2), leaf(3)]).expect("mixed tree verifies");
    }

    /// Golden vectors for the TypeScript reader port (docs/zk-reader-contract.md). Writes
    /// `$FB_VECTORS_OUT` (default ~/projects/farcaster-blobs/zk-aggregate/vectors/leaf-v2.json).
    #[test]
    #[ignore = "writes the reader vector file; run on purpose"]
    fn write_reader_vectors() {
        use lean_prover::ed25519_leaf::{blob_id_cells, leaf_meta, pack11, pack7};
        init_aggregation_bytecode();
        let bytecode = get_aggregation_bytecode();
        let cells = |v: &[F]| format!("[{}]", v.iter().map(|x| x.as_canonical_u32().to_string()).collect::<Vec<_>>().join(","));
        let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();
        let rows = dataset();
        let seg: &[SigRow] = &rows[32..48]; // the 2-signer leaf of the diverse dataset
        let mut vh = [0u8; 32]; vh[0] = 0x01; for i in 1..32 { vh[i] = (i * 37 % 251) as u8; }
        let blob_id = blob_id_cells(&vh);
        let canon = canonical_rows(seg);
        // canonical_order[i] = index in rows_blob_order of the i-th canonical row (stable sort of indices)
        let order = { let mut idx: Vec<usize> = (0..seg.len()).collect(); idx.sort_by(|a, b| seg[*a].pubkey.cmp(&seg[*b].pubkey)); idx };
        // a second leaf with THREE signers interleaved (A B C A B C A B C A B: 11 rows, seg_index 3) so a
        // port that inverts the permutation, sorts unstably, or sorts by (pubkey, digest) is caught
        let mut by_key: std::collections::BTreeMap<[u8; 32], Vec<&SigRow>> = std::collections::BTreeMap::new();
        for r in &rows { by_key.entry(r.pubkey).or_default().push(r); }
        let groups: Vec<&Vec<&SigRow>> = by_key.values().filter(|g| g.len() >= 4).take(3).collect();
        assert_eq!(groups.len(), 3, "dataset must have 3 signers with >= 4 rows");
        let seg2: Vec<SigRow> = (0..11).map(|i| SigRow { pubkey: groups[i % 3][i / 3].pubkey, digest: groups[i % 3][i / 3].digest, sig: groups[i % 3][i / 3].sig }).collect();
        let order2 = { let mut idx: Vec<usize> = (0..seg2.len()).collect(); idx.sort_by(|a, b| seg2[*a].pubkey.cmp(&seg2[*b].pubkey)); idx };
        let canon2 = canonical_rows(&seg2);
        let leaf2_in = expected_leaf_input_data(&seg2, 3, &blob_id).unwrap();
        let leaf2_digest = expected_leaf_digest(&seg2, 3, &blob_id).unwrap();
        let root = root_seg(&canon);
        let meta = leaf_meta(canon.len(), 0, &blob_id);
        let leaf_in = expected_leaf_input_data(seg, 0, &blob_id).unwrap();
        let leaf_digest = expected_leaf_digest(seg, 0, &blob_id).unwrap();
        let zero_claim = zero_bytecode_claim_flat();
        let p16_in: Vec<F> = (0..16).map(F::from_usize).collect();
        let p16_out = poseidon16_permute(p16_in.clone().try_into().unwrap());
        // a real node over this leaf, for the claim point / recomputed value and the node layout
        let leaf = prove_ed25519_leaf(seg, 0, &blob_id, 1).expect("leaf proof");
        let node = prove_ed25519_top(&[Ed25519Child::Leaf(&leaf)], DEFAULT_TOP_LOG_INV_RATE).expect("node proof");
        let claim = rebuild_bytecode_claim(node.bytecode_claim.point.clone()).unwrap();
        let point_cells: Vec<F> = claim.point.0.iter().flat_map(|e| e.as_basis_coefficients_slice().to_vec()).collect();
        let json = format!(r#"{{
  "contract": "docs/zk-reader-contract.md v2",
  "vk": {{ "n_vars": {}, "claim_len": {}, "claim_len_padded": {}, "domsep": {}, "zero_eval": {}, "leaf_version": {}, "max_leaf_sigs": {}, "bytecode_hash": {} }},
  "conventions": {{ "canonical_order": "canonical_order[i] = index in rows_blob_order of the i-th canonical row (stable sort by pubkey bytes, ties keep blob order)", "zero_eval": "read from vk, never hardcode" }},
  "poseidon16": {{ "input": {}, "output": {} }},
  "pack11": {{ "bytes": "{}", "cells": {} }},
  "pack7": {{ "bytes": "{}", "cells": {} }},
  "leaf": {{
    "blob_versioned_hash": "{}", "blob_id": {}, "seg_index": 0,
    "rows_blob_order": [{}],
    "canonical_order": {:?},
    "root_seg": {}, "meta": {}, "input_data": {}, "digest": {},
    "proof_kib_rate_half": {}
  }},
  "leaf_interleaved": {{
    "blob_id": {}, "seg_index": 3,
    "rows_blob_order": [{}],
    "canonical_order": {:?},
    "root_seg": {}, "meta": {}, "input_data": {}, "digest": {}
  }},
  "node": {{
    "child_digests": [{}], "claim_point": {}, "claim_value": {}, "input_data": {}, "digest": {},
    "proof_kib_rate_half": {}
  }}
}}
"#,
            bytecode.cumulated_n_vars(), zero_claim.len(), zero_claim.len().next_multiple_of(DIGEST_LEN), cells(&fiat_shamir_domain_sep(bytecode)), cells(&zero_claim[zero_claim.len() - 5..]), lean_prover::ed25519_leaf::LEAF_VERSION, lean_prover::ed25519_leaf::MAX_LEAF_SIGS, cells(bytecode.hash()),
            cells(&p16_in), cells(&p16_out),
            hex(&seg[0].pubkey), cells(&pack11(&seg[0].pubkey)),
            hex(&seg[0].digest), cells(&pack7(&seg[0].digest)),
            hex(&vh), cells(&blob_id),
            seg.iter().map(|r| format!("{{\"pubkey\":\"{}\",\"digest\":\"{}\",\"sig\":\"{}\"}}", hex(&r.pubkey), hex(&r.digest), hex(&r.sig))).collect::<Vec<_>>().join(",\n      "),
            order,
            cells(&root), cells(&meta), cells(&leaf_in), cells(&leaf_digest),
            leaf.proof.proof.proof_size_fe() * 4 / 1024,
            cells(&blob_id),
            seg2.iter().map(|r| format!("{{\"pubkey\":\"{}\",\"digest\":\"{}\",\"sig\":\"{}\"}}", hex(&r.pubkey), hex(&r.digest), hex(&r.sig))).collect::<Vec<_>>().join(",\n      "),
            order2,
            cells(&root_seg(&canon2)), cells(&leaf_meta(canon2.len(), 3, &blob_id)), cells(&leaf2_in), cells(&leaf2_digest),
            cells(&leaf_digest), cells(&point_cells), cells(claim.value.as_basis_coefficients_slice()), cells(&node.input_data), cells(&poseidon_hash_slice(&node.input_data)),
            node.proof.proof.proof_size_fe() * 4 / 1024,
        );
        let out = std::env::var("FB_VECTORS_OUT").unwrap_or(format!("{}/projects/farcaster-blobs/zk-aggregate/vectors/leaf-v2.json", std::env::var("HOME").unwrap()));
        std::fs::create_dir_all(std::path::Path::new(&out).parent().unwrap()).unwrap();
        std::fs::write(&out, json).unwrap();
        println!("wrote {out}");
    }

    /// One whole blob through the production driver: BLOB_N rows (default one blob's worth) at
    /// DEFAULT_LEAF_SIGS, top at DEFAULT_TOP_LOG_INV_RATE; reader-verified through `verify_ed25519_blob`
    /// with nothing but the proof and the leaf size; a shifted row list is rejected.
    #[test]
    fn test_ed25519_prove_blob() {
        init_aggregation_bytecode();
        let rows = dataset();
        let n = env("BLOB_N", 6745).min(rows.len());
        let leaf_size = env("LEAF_SIZE", DEFAULT_LEAF_SIGS);
        let top_rate = env("TOP_RATE", DEFAULT_TOP_LOG_INV_RATE);
        let blob_id: [F; 9] = std::array::from_fn(|i| F::from_usize(0x1234 + i));
        let t = std::time::Instant::now();
        let top = prove_ed25519_blob(&rows[..n], &blob_id, leaf_size, DEFAULT_LEAF_LOG_INV_RATE, top_rate, &|m| println!("  {m}")).expect("blob proof");
        println!("BLOB {n} rows, leaves of {leaf_size}: proved in {:.1} s, published proof {} KiB", t.elapsed().as_secs_f32(), top.proof.proof.proof_size_fe() * 4 / 1024);
        let tv = std::time::Instant::now();
        verify_ed25519_blob(&top, &rows[..n], leaf_size, &blob_id).expect("reader verifies the blob from the proof + leaf size");
        println!("BLOB verified reader-side in {:.3} s", tv.elapsed().as_secs_f32());
        assert!(verify_ed25519_blob(&top, &rows[1..n + 1], leaf_size, &blob_id).is_err(), "shifted rows must be rejected");
        assert!(verify_ed25519_blob(&top, &rows[..n], leaf_size + 1, &blob_id).is_err(), "a wrong leaf size must be rejected");
    }

    /// IN-CIRCUIT negative: a child proof tampered after native verification must be rejected by the
    /// recursion program itself (not only by the native pre-check). Tampers a cell in the middle of the
    /// transcript, then a cell inside an 8-cell region shaped like a padded opening ([v v v v v 0 0 0];
    /// the transcript is not globally 8-aligned, so this is "a cell the batched path may read as a
    /// pad", not a guaranteed pad-assert hit — either way the in-circuit verifier must fail).
    #[test]
    fn test_ed25519_node_rejects_tampered_child_in_circuit() {
        init_aggregation_bytecode();
        let rows = dataset();
        let blob_id = std::array::from_fn(|i| F::from_usize(9 + i));
        let leaf = prove_ed25519_leaf(&rows[..16], 0, &blob_id, 1).expect("leaf proof");
        let good = verify_ed25519_leaf(&leaf).expect("honest leaf verifies natively");
        let n = good.raw_proof.transcript.len();
        // (a) a value cell in the middle of the transcript
        let mut v = verify_ed25519_leaf(&leaf).unwrap();
        v.raw_proof.transcript[n / 2] += F::ONE;
        assert!(prove_node_from_verified(&PROFILE_FULL, vec![v], vec![NodeShape::Leaf], 1).is_err(), "a tampered transcript value must not prove");
        // (b) a pad cell of an 8-cell chunk shaped [v v v v v 0 0 0] (a One-bus opening in a range run)
        let mut v = verify_ed25519_leaf(&leaf).unwrap();
        let tr = &v.raw_proof.transcript;
        let pad = (n / 4..n - 8).step_by(8).find(|&i| tr[i + 5] == F::ZERO && tr[i + 6] == F::ZERO && tr[i + 7] == F::ZERO && tr[i..i + 5].iter().all(|x| *x != F::ZERO)).expect("a padded EF chunk in the transcript");
        v.raw_proof.transcript[pad + 7] = F::ONE;
        assert!(prove_node_from_verified(&PROFILE_FULL, vec![v], vec![NodeShape::Leaf], 1).is_err(), "a nonzero pad cell must not prove");
        // control: the untampered child still proves
        let node = prove_node_from_verified(&PROFILE_TERMINAL, vec![good], vec![NodeShape::Leaf], 1).expect("honest child proves");
        verify_ed25519_node(&node, &leaf_statements(&[&rows[..16]], &blob_id)).expect("and verifies");
    }
}
