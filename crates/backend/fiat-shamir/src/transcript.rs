use field::Field;
use serde::{Deserialize, Serialize};

use crate::PrunedMerklePaths;

pub const DIGEST_LEN_FE: usize = 8;

#[derive(Debug, Clone)]
pub struct MerkleOpening<F> {
    pub leaf_data: Vec<F>,
    pub path: Vec<[F; DIGEST_LEN_FE]>,
}

/// "RawProof": the format which is used in the zkVM recursion program (no Merkle pruning, no sumcheck optimization to send less data, etc)
#[derive(Clone)]
pub struct RawProof<F> {
    pub transcript: Vec<F>,
    pub merkle_openings: Vec<MerkleOpening<F>>,
}

#[derive(Debug, Clone)]
pub struct MerklePath<Data, F> {
    pub leaf_data: Vec<Data>,
    pub sibling_hashes: Vec<[F; DIGEST_LEN_FE]>,
    // does not appear in the proof itself, but useful for Merkle pruning
    pub leaf_index: usize,
}

#[derive(Debug, Clone)]
pub struct MerklePaths<Data, F>(pub(crate) Vec<MerklePath<Data, F>>);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Proof<F> {
    pub(crate) transcript: Vec<F>,
    pub(crate) merkle_paths: Vec<PrunedMerklePaths<F, F>>,
}

/// Fixed-width wire encoding of a proof for a 31/32-bit base field: every cell is 4 bytes
/// little-endian and every length a u32, so the bytes on the wire equal `4 × proof_size_fe()` plus
/// a few length prefixes (a generic varint encoding costs ≈ +20 % on random 31-bit cells).
/// Layout: n_transcript ‖ cells ‖ n_paths ‖ per path: n_leaf_groups ‖ (len ‖ cells)* ‖ n_siblings ‖
/// (8 cells)*. Decoding is strict: every cell must be canonical and no trailing bytes are allowed.
impl<F: field::PrimeField32> Proof<F> {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(4 * self.proof_size_fe() + 64);
        let push_len = |out: &mut Vec<u8>, n: usize| out.extend_from_slice(&u32::try_from(n).expect("length fits u32").to_le_bytes());
        let push_cells = |out: &mut Vec<u8>, cells: &[F]| for c in cells { out.extend_from_slice(&c.as_canonical_u32().to_le_bytes()); };
        push_len(&mut out, self.transcript.len());
        push_cells(&mut out, &self.transcript);
        push_len(&mut out, self.merkle_paths.len());
        for p in &self.merkle_paths {
            push_len(&mut out, p.leaf_data.len());
            for group in &p.leaf_data { push_len(&mut out, group.len()); push_cells(&mut out, group); }
            push_len(&mut out, p.sibling_hashes.len());
            for h in &p.sibling_hashes { push_cells(&mut out, h); }
        }
        out
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        struct R<'a> { b: &'a [u8], p: usize }
        impl<'a> R<'a> {
            fn u32(&mut self) -> Result<u32, &'static str> { let s = self.b.get(self.p..self.p + 4).ok_or("truncated")?; self.p += 4; Ok(u32::from_le_bytes(s.try_into().unwrap())) }
            fn len(&mut self) -> Result<usize, &'static str> { let n = self.u32()? as usize; if n > self.b.len() / 4 { return Err("length exceeds input"); } Ok(n) }
            fn cell<F: field::PrimeField32>(&mut self) -> Result<F, &'static str> { let v = self.u32()?; let f = F::from_u32(v); if f.as_canonical_u32() != v { return Err("non-canonical cell"); } Ok(f) }
            fn cells<F: field::PrimeField32>(&mut self, n: usize) -> Result<Vec<F>, &'static str> { (0..n).map(|_| self.cell()).collect() }
        }
        let mut r = R { b: bytes, p: 0 };
        let n = r.len()?;
        let transcript = r.cells::<F>(n)?;
        let n_paths = r.len()?;
        let mut merkle_paths = Vec::with_capacity(n_paths);
        for _ in 0..n_paths {
            let n_groups = r.len()?;
            let mut leaf_data = Vec::with_capacity(n_groups);
            for _ in 0..n_groups { let l = r.len()?; leaf_data.push(r.cells::<F>(l)?); }
            let n_sib = r.len()?;
            let mut sibling_hashes = Vec::with_capacity(n_sib);
            for _ in 0..n_sib { let v = r.cells::<F>(DIGEST_LEN_FE)?; sibling_hashes.push(v.try_into().map_err(|_| "digest")?); }
            merkle_paths.push(PrunedMerklePaths { leaf_data, sibling_hashes });
        }
        if r.p != bytes.len() { return Err("trailing bytes"); }
        Ok(Self { transcript, merkle_paths })
    }
}

impl<F: Field> Proof<F> {
    pub fn proof_size_fe(&self) -> usize {
        let merkle_size: usize = self
            .merkle_paths
            .iter()
            .map(|paths| {
                paths.leaf_data.iter().map(|d| d.len()).sum::<usize>() + paths.sibling_hashes.len() * DIGEST_LEN_FE
            })
            .sum();
        self.transcript.len() + merkle_size
    }
}
