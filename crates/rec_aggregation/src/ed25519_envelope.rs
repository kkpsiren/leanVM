//! Versioned, bounded postcard transport for single-blob proofs. New writers emit v3; v2 remains
//! readable. V3 contains no shape or top input data, but MUST retain transcript-dependent inner
//! claims. Its claim cells are canonical integers (v2 used serde's internal Montgomery integers).
use backend::*;
use lean_prover::ed25519_leaf::{SigRow, blob_id_cells};
use lean_prover::prove_execution::ExecutionProof;
use lean_vm::*;
use serde::{Deserialize, Serialize};

use crate::bytecode_claims::flatten_bytecode_claim;
use crate::ed25519::*;
use crate::ed25519_tree::{BlobTreeLayout, MAX_BLOB_TREE_DEPTH};
use crate::get_aggregation_bytecode;
use crate::single_message_aggregation::rebuild_bytecode_claim;

pub const ENVELOPE_VERSION: u32 = 3;
// Transport bounds, checked before allocation/recursion. The actual claim dimension must also
// equal the loaded VK's dimension before any digest or bytecode evaluation is performed.
pub const MAX_ENVELOPE_BYTES: usize = 16 * 1024 * 1024;
const MAX_POINT_CELLS: usize = 64 * 5;
const MAX_CLAIM_CELLS: usize = MAX_POINT_CELLS + 5;
const MAX_INPUT_CELLS: usize = 8 + MAX_CLAIM_CELLS.next_multiple_of(8) + 8 + 16 * 8;

#[derive(Serialize)]
struct WireV3 {
    version: u32,
    leaf_size: u32,
    n_rows: u32,
    blob_id: [u8; 32],
    top_point: Vec<u32>,
    inner_claims: Vec<Vec<u32>>,
    proof_bytes: Vec<u8>,
}

enum Payload {
    Legacy {
        input_data: Vec<F>,
        top_claim: Evaluation<EF>,
        shape: Vec<NodeShape>,
    },
    Canonical {
        top_point: MultilinearPoint<EF>,
        shape: Vec<NodeShape>,
    },
}

#[allow(missing_debug_implementations)]
pub struct BlobProofEnvelope {
    pub version: u32,
    pub leaf_size: usize,
    pub n_rows: usize,
    pub blob_id: [u8; 32],
    pub n_leaves: usize,
    pub n_inner_nodes: usize,
    pub proof_bytes: Vec<u8>,
    payload: Payload,
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn release_profile_is_johnson_bound() {
        assert!(!lean_prover::PROX_GAPS_CONJECTURE);
        assert!(matches!(lean_prover::default_whir_config(1).soundness_type,
            backend::SecurityAssumption::JohnsonBound));
    }

    #[test]
    fn signature_profile_rejects_torsion_before_proving() {
        use lean_prover::ed25519_leaf::{SigRow, leaf_hint_buffers};
        let fixture: serde_json::Value = serde_json::from_str(include_str!("../test-vectors/ed25519-profile.json")).unwrap();
        let hex = |s: &str| -> Vec<u8> { (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect() };
        for v in fixture["rows"].as_array().unwrap() {
            let row = SigRow {
                pubkey: hex(v["signer"].as_str().unwrap()).try_into().unwrap(),
                digest: hex(v["digest"].as_str().unwrap()).try_into().unwrap(),
                sig: hex(v["signature"].as_str().unwrap()).try_into().unwrap(),
            };
            let result = leaf_hint_buffers(&[row], 0, &[F::ZERO; 9]);
            if v["accepted"].as_bool().unwrap() {
                assert!(result.is_ok(), "{}", v["name"]);
            } else {
                assert!(result.unwrap_err().contains("torsion component"), "{}", v["name"]);
            }
        }
        // This is witness-profile preflight, not a proof-verification or soundness test.
    }

    // Frozen v2 field order and serde cell representation, retained only to exercise compatibility.
    #[derive(Serialize)]
    struct ShapeV2 {
        claim_flat: Option<Vec<F>>,
        children: Vec<ShapeV2>,
    }
    #[derive(Serialize)]
    struct WireV2 {
        version: u32,
        leaf_size: u32,
        n_rows: u32,
        blob_id: [u8; 32],
        input_data: Vec<F>,
        top_claim_flat: Vec<F>,
        shape: Vec<ShapeV2>,
        proof_bytes: Vec<u8>,
    }
    fn shape_v2(s: &NodeShape) -> ShapeV2 {
        match s {
            NodeShape::Leaf => ShapeV2 {
                claim_flat: None,
                children: vec![],
            },
            NodeShape::Node { claim, children } => ShapeV2 {
                claim_flat: Some(flatten_bytecode_claim(claim)),
                children: children.iter().map(shape_v2).collect(),
            },
        }
    }
    pub(crate) fn encode_v2(node: &Ed25519NodeProof, n: usize, s: usize, id: [u8; 32]) -> Vec<u8> {
        postcard::to_allocvec(&WireV2 {
            version: 2,
            leaf_size: s as u32,
            n_rows: n as u32,
            blob_id: id,
            input_data: node.input_data.clone(),
            top_claim_flat: flatten_bytecode_claim(&node.bytecode_claim),
            shape: node.shape.iter().map(shape_v2).collect(),
            proof_bytes: node.proof.proof.to_bytes(),
        })
        .unwrap()
    }

    /// Reuses an already-proved blob: no extra prover process/work for transport round trips.
    pub(crate) fn roundtrips(node: &Ed25519NodeProof, rows: &[SigRow], leaf_size: usize, id: [u8; 32]) {
        let old = encode_v2(node, rows.len(), leaf_size, id);
        let new = encode_ed25519_blob(node, rows.len(), leaf_size, id).unwrap();
        println!(
            "ENVELOPE measured: v2={} bytes, v3={} bytes, saved={} bytes; rows={}, leaves={}, inner={}",
            old.len(),
            new.len(),
            old.len() as isize - new.len() as isize,
            rows.len(),
            BlobTreeLayout::new(rows.len(), leaf_size).unwrap().n_leaves(),
            BlobTreeLayout::new(rows.len(), leaf_size).unwrap().n_inner_nodes()
        );
        let reader_rows: Vec<_> = rows
            .iter()
            .map(|r| SigRow {
                sig: [0; 64],
                ..r.clone()
            })
            .collect();
        for bytes in [&old, &new] {
            BlobProofEnvelope::decode(bytes)
                .unwrap()
                .verify(&reader_rows, &id)
                .expect("signature-free reader verifies");
            let mut bad_id = id;
            bad_id[31] ^= 128;
            assert!(
                BlobProofEnvelope::decode(bytes)
                    .unwrap()
                    .verify(&reader_rows, &bad_id)
                    .is_err()
            );
            assert!(
                BlobProofEnvelope::decode(bytes)
                    .unwrap()
                    .verify(&reader_rows[..reader_rows.len() - 1], &id)
                    .is_err()
            );
            let mut bad_rows = reader_rows.clone();
            bad_rows[0].digest[0] ^= 1;
            assert!(
                BlobProofEnvelope::decode(bytes)
                    .unwrap()
                    .verify(&bad_rows, &id)
                    .is_err()
            );
        }
        let mutate = |f: &dyn Fn(&mut BlobProofEnvelope)| {
            let mut env = BlobProofEnvelope::decode(&new).unwrap();
            f(&mut env);
            assert!(env.verify(&reader_rows, &id).is_err());
        };
        mutate(&|e| {
            if let Payload::Canonical { top_point, .. } = &mut e.payload {
                top_point.0[0] += EF::ONE;
            }
        });
        mutate(&|e| {
            if let Payload::Canonical { top_point, .. } = &mut e.payload {
                top_point.0.pop();
            }
        });
        if BlobTreeLayout::new(rows.len(), leaf_size).unwrap().n_inner_nodes() > 0 {
            mutate(&|e| {
                if let Payload::Canonical { shape, .. } = &mut e.payload {
                    if let NodeShape::Node { claim, .. } = &mut shape[0] {
                        claim.point.0[0] += EF::ONE;
                    }
                }
            });
            mutate(&|e| {
                if let Payload::Canonical { shape, .. } = &mut e.payload {
                    if let NodeShape::Node { claim, .. } = &mut shape[0] {
                        claim.value += EF::ONE;
                    }
                }
            });
            mutate(&|e| {
                if let Payload::Canonical { shape, .. } = &mut e.payload {
                    // V3 carries claims only: reorder those, keeping the derived topology intact.
                    if let [
                        NodeShape::Node { claim: first, .. },
                        NodeShape::Node { claim: second, .. },
                        ..,
                    ] = shape.as_mut_slice()
                    {
                        std::mem::swap(first, second);
                    } else {
                        panic!("a canonical tree with inner nodes has at least two node children");
                    }
                }
            });
        }
    }

    fn wire() -> WireV3 {
        WireV3 {
            version: 3,
            leaf_size: 16,
            n_rows: 65,
            blob_id: [1; 32],
            top_point: vec![0; 120],
            inner_claims: vec![vec![0; 125]; 2],
            proof_bytes: vec![0; 8],
        }
    }

    #[test]
    fn rejects_malformed_envelopes_before_bytecode_initialization() {
        let good = postcard::to_allocvec(&wire()).unwrap();
        assert!(BlobProofEnvelope::decode(&good).is_ok()); // framing only; empty proof is not verified
        for i in 0..good.len() {
            assert!(BlobProofEnvelope::decode(&good[..i]).is_err(), "truncation {i}");
        }
        let mut trailing = good.clone();
        trailing.push(0);
        assert!(BlobProofEnvelope::decode(&trailing).is_err());
        for mutate in [
            |w: &mut WireV3| w.version = 4,
            |w: &mut WireV3| w.leaf_size = 0,
            |w: &mut WireV3| w.leaf_size = 2671,
            |w: &mut WireV3| w.n_rows = 0,
            |w: &mut WireV3| w.n_rows = u32::MAX,
            |w: &mut WireV3| {
                w.inner_claims.pop();
            },
            |w: &mut WireV3| w.inner_claims.push(vec![0; 125]),
            |w: &mut WireV3| w.top_point[0] = u32::MAX,
            |w: &mut WireV3| w.inner_claims[0][0] = u32::MAX,
            |w: &mut WireV3| {
                w.top_point.pop();
            },
            |w: &mut WireV3| {
                w.inner_claims[0].pop();
            },
            |w: &mut WireV3| w.top_point = vec![0; MAX_POINT_CELLS + 5],
            |w: &mut WireV3| w.proof_bytes = vec![255; 8],
        ] {
            let mut w = wire();
            mutate(&mut w);
            assert!(BlobProofEnvelope::decode(&postcard::to_allocvec(&w).unwrap()).is_err());
        }
        // Hostile length prefix, not a huge allocation.
        let mut huge = postcard::to_allocvec(&(3u32, 16u32, 65u32, [1u8; 32])).unwrap();
        huge.extend(postcard::to_allocvec(&u32::MAX).unwrap());
        assert!(BlobProofEnvelope::decode(&huge).is_err());
        assert!(BlobProofEnvelope::decode(&vec![0; MAX_ENVELOPE_BYTES + 1]).is_err());
    }

    #[test]
    fn legacy_parser_bounds_depth_and_leaf_shape() {
        let mut leaf = ShapeV2 {
            claim_flat: None,
            children: vec![],
        };
        for _ in 0..MAX_BLOB_TREE_DEPTH {
            leaf = ShapeV2 {
                claim_flat: Some(vec![F::ZERO; 125]),
                children: vec![leaf],
            };
        }
        let mut w = WireV2 {
            version: 2,
            leaf_size: 16,
            n_rows: 16,
            blob_id: [0; 32],
            input_data: vec![],
            top_claim_flat: vec![F::ZERO; 125],
            shape: vec![leaf],
            proof_bytes: vec![0; 8],
        };
        assert!(BlobProofEnvelope::decode(&postcard::to_allocvec(&w).unwrap()).is_err());
        w.shape = vec![ShapeV2 {
            claim_flat: None,
            children: vec![ShapeV2 {
                claim_flat: None,
                children: vec![],
            }],
        }];
        assert!(BlobProofEnvelope::decode(&postcard::to_allocvec(&w).unwrap()).is_err());
        w.shape = vec![ShapeV2 {
            claim_flat: None,
            children: vec![],
        }];
        assert!(BlobProofEnvelope::decode(&postcard::to_allocvec(&w).unwrap()).is_ok());
    }
}

fn cells(v: &[F]) -> Vec<u32> {
    v.iter().map(PrimeField32::as_canonical_u32).collect()
}
fn point_flat(point: &MultilinearPoint<EF>) -> Vec<F> {
    point
        .0
        .iter()
        .flat_map(|x| x.as_basis_coefficients_slice().to_vec())
        .collect()
}
fn point_from(flat: &[F]) -> Result<MultilinearPoint<EF>, String> {
    if flat.is_empty() || flat.len() % 5 != 0 {
        return Err("bad claim point length".into());
    }
    Ok(MultilinearPoint(
        flat.chunks_exact(5)
            .map(|c| EF::from_basis_coefficients_slice(c).ok_or_else(|| "bad claim element".to_string()))
            .collect::<Result<_, _>>()?,
    ))
}
fn claim_from(flat: &[F]) -> Result<Evaluation<EF>, String> {
    if flat.len() < 10 {
        return Err("bad claim length".into());
    }
    let point = point_from(&flat[..flat.len() - 5])?;
    let value = EF::from_basis_coefficients_slice(&flat[flat.len() - 5..]).ok_or("bad claim value")?;
    Ok(Evaluation::new(point, value))
}

/// Encode a canonical proof without repeating the reader-reconstructible top input data/value.
pub fn encode_ed25519_blob(
    node: &Ed25519NodeProof,
    n_rows: usize,
    leaf_size: usize,
    blob_id: [u8; 32],
) -> Result<Vec<u8>, String> {
    let layout = BlobTreeLayout::new(n_rows, leaf_size)?;
    let claims = layout.claims(&node.shape)?;
    let n_vars = get_aggregation_bytecode().cumulated_n_vars();
    if node.bytecode_claim.point.0.len() != n_vars || claims.iter().any(|c| c.point.0.len() != n_vars) {
        return Err("claim dimension differs from VK".into());
    }
    let wire = WireV3 {
        version: ENVELOPE_VERSION,
        leaf_size: leaf_size as u32,
        n_rows: n_rows as u32,
        blob_id,
        top_point: cells(&point_flat(&node.bytecode_claim.point)),
        inner_claims: claims.iter().map(|c| cells(&flatten_bytecode_claim(c))).collect(),
        proof_bytes: node.proof.proof.to_bytes(),
    };
    let bytes = postcard::to_allocvec(&wire).map_err(|e| e.to_string())?;
    if bytes.len() > MAX_ENVELOPE_BYTES {
        return Err("envelope exceeds transport limit".into());
    }
    Ok(bytes)
}

// Decode incrementally: validate lengths against protocol bounds AND remaining bytes before
// allocating. In particular, never let serde recursively deserialize an attacker-selected tree.
struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take<T: Deserialize<'a>>(&mut self) -> Result<T, String> {
        let (v, rest) = postcard::take_from_bytes(self.0).map_err(|e| format!("bad envelope: {e}"))?;
        self.0 = rest;
        Ok(v)
    }
    fn len(&mut self, max: usize) -> Result<usize, String> {
        let n: usize = self.take()?;
        if n > max || n > self.0.len() {
            return Err("envelope length exceeds bounds/input".into());
        }
        Ok(n)
    }
    fn cells(&mut self, max: usize, canonical: bool) -> Result<Vec<F>, String> {
        let n = self.len(max)?;
        (0..n)
            .map(|_| {
                if !canonical {
                    return self.take::<F>();
                }
                let x: u32 = self.take()?;
                let f = F::from_u32(x);
                if f.as_canonical_u32() != x {
                    return Err("noncanonical claim cell".into());
                }
                Ok(f)
            })
            .collect()
    }
    fn legacy_shape(
        &mut self,
        depth: usize,
        leaves: &mut usize,
        inner: &mut usize,
        expected_leaves: usize,
    ) -> Result<Vec<NodeShape>, String> {
        if depth > MAX_BLOB_TREE_DEPTH {
            return Err("legacy tree is too deep".into());
        }
        let n = self.len(crate::MAX_RECURSIONS)?;
        if n == 0 {
            return Err("a node needs children".into());
        }
        (0..n)
            .map(|_| {
                // postcard Option tag, followed by a Vec<F> only for Some.
                match self.take::<u8>()? {
                    0 => {
                        let children: usize = self.take()?;
                        if children != 0 {
                            return Err("a leaf has no children".into());
                        }
                        *leaves += 1;
                        if *leaves > expected_leaves {
                            return Err("too many leaves".into());
                        }
                        Ok(NodeShape::Leaf)
                    }
                    1 => {
                        let claim = claim_from(&self.cells(MAX_CLAIM_CELLS, false)?)?;
                        *inner += 1;
                        let children = self.legacy_shape(depth + 1, leaves, inner, expected_leaves)?;
                        Ok(NodeShape::Node { claim, children })
                    }
                    _ => Err("invalid legacy shape tag".into()),
                }
            })
            .collect()
    }
}

impl BlobProofEnvelope {
    pub fn decode(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() > MAX_ENVELOPE_BYTES {
            return Err("envelope exceeds transport limit".into());
        }
        let mut r = Reader(bytes);
        let version = r.take()?;
        if version != 2 && version != ENVELOPE_VERSION {
            return Err(format!("unsupported envelope version {version}"));
        }
        let leaf_size = r.take::<u32>()? as usize;
        let n_rows = r.take::<u32>()? as usize;
        let blob_id = r.take()?;
        let layout = BlobTreeLayout::new(n_rows, leaf_size)?;
        let (payload, n_leaves, n_inner_nodes) = if version == 2 {
            let input_data = r.cells(MAX_INPUT_CELLS, false)?;
            let top_claim = claim_from(&r.cells(MAX_CLAIM_CELLS, false)?)?;
            let (mut leaves, mut inner) = (0, 0);
            let shape = r.legacy_shape(1, &mut leaves, &mut inner, layout.n_leaves())?;
            if leaves != layout.n_leaves() {
                return Err("wrong legacy leaf count".into());
            }
            (
                Payload::Legacy {
                    input_data,
                    top_claim,
                    shape,
                },
                leaves,
                inner,
            )
        } else {
            let top_point = point_from(&r.cells(MAX_POINT_CELLS, true)?)?;
            let n = r.len(layout.n_inner_nodes())?;
            if n != layout.n_inner_nodes() {
                return Err("wrong inner claim count".into());
            }
            let claims = (0..n)
                .map(|_| claim_from(&r.cells(MAX_CLAIM_CELLS, true)?))
                .collect::<Result<Vec<_>, String>>()?;
            let shape = layout.shape(&claims)?;
            (
                Payload::Canonical { top_point, shape },
                layout.n_leaves(),
                layout.n_inner_nodes(),
            )
        };
        let n = r.len(MAX_ENVELOPE_BYTES)?;
        let proof_bytes = r.0[..n].to_vec();
        r.0 = &r.0[n..];
        if !r.0.is_empty() {
            return Err("trailing envelope bytes".into());
        }
        // The fixed-width proof decoder bounds nested lengths and rejects noncanonical cells.
        Proof::<F>::from_bytes(&proof_bytes).map_err(|e| format!("bad proof bytes: {e}"))?;
        Ok(Self {
            version,
            leaf_size,
            n_rows,
            blob_id,
            n_leaves,
            n_inner_nodes,
            proof_bytes,
            payload,
        })
    }

    pub fn check_statement(&self, n_rows: usize, blob_id: &[u8; 32]) -> Result<(), String> {
        if self.blob_id != *blob_id {
            return Err("the envelope names a different blob".into());
        }
        if self.n_rows != n_rows {
            return Err(format!(
                "the envelope claims {} rows, the blob has {n_rows}",
                self.n_rows
            ));
        }
        Ok(())
    }

    /// The bytecode must be initialized first. No input data or top value supplied by the writer
    /// is used for v3; all child digests and the top value are reconstructed by this reader.
    pub fn verify(self, rows: &[SigRow], blob_id: &[u8; 32]) -> Result<(), String> {
        self.check_statement(rows.len(), blob_id)?;
        let n_vars = crate::get_aggregation_verifier_program().cumulated_n_vars();
        let proof = ExecutionProof {
            proof: Proof::from_bytes(&self.proof_bytes).map_err(str::to_string)?,
            metadata: None,
        };
        let blob_cells = blob_id_cells(blob_id);
        let result = match self.payload {
            Payload::Legacy {
                input_data,
                top_claim,
                shape,
            } => {
                if top_claim.point.0.len() != n_vars {
                    return Err("claim dimension differs from VK".into());
                }
                let node = Ed25519NodeProof {
                    input_data,
                    bytecode_claim: top_claim,
                    shape,
                    proof,
                };
                verify_ed25519_blob_legacy(&node, rows, self.leaf_size, &blob_cells)
            }
            Payload::Canonical { top_point, shape } => {
                if top_point.0.len() != n_vars {
                    return Err("claim dimension differs from VK".into());
                }
                let layout = BlobTreeLayout::new(rows.len(), self.leaf_size)?;
                let stmts = layout.statements(rows, &blob_cells)?;
                let digests = stmts
                    .iter()
                    .zip(&shape)
                    .map(|(stmt, s)| expected_digest(stmt, s))
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| format!("bad inner claim: {e:?}"))?;
                let claim = rebuild_bytecode_claim(top_point).map_err(|e| format!("bad top claim: {e:?}"))?;
                let input_data = ed25519_node_input_data(&digests, &flatten_bytecode_claim(&claim));
                crate::verify_inner_with(&PROFILE_TERMINAL, input_data, proof.proof)
            }
        };
        result.map(|_| ()).map_err(|e| format!("PROOF REJECTED: {e:?}"))
    }
}
