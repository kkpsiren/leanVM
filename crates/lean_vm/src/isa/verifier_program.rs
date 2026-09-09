//! Read-only program interface and authenticated dictionary representation for verifiers.
//! No CodeEntry, hints, debug information, or dense 2^(log_size + 4) table is retained here.
use backend::*;
use crate::{Bytecode, EF, F, N_INSTRUCTION_COLUMNS, init_profile_mark};
use crate::ed25519::sha512_table::sha512_bytes;

/// Callers must authenticate the program before using it as a verification key.
pub trait VerifierProgram: Sync {
    fn log_size(&self) -> usize;
    fn hash(&self) -> &[F; 8];
    fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF;
    fn ending_pc(&self) -> usize { (1 << self.log_size()) - 1 }
    fn cumulated_n_vars(&self) -> usize { self.log_size() + 4 }
    fn bytecode_claim_size(&self) -> usize { (self.cumulated_n_vars() + 1) * crate::DIMENSION }
}

impl VerifierProgram for Bytecode {
    fn log_size(&self) -> usize { self.log_size() }
    fn hash(&self) -> &[F; 8] { self.hash() }
    fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF {
        assert_eq!(point.len(), self.cumulated_n_vars());
        if point.iter().all(|x| x.is_zero()) { EF::from(self.instructions_multilinear()[0]) }
        else { self.instructions_multilinear().evaluate_sequential(point) }
    }
}

pub const VERIFIER_ARTIFACT_MAGIC: &[u8; 8] = b"FBVK0001";
const HEADER_LEN: usize = 48; // magic, log_size, dictionary count, original Poseidon hash
const _: () = assert!(N_INSTRUCTION_COLUMNS == 12); // version 1 has four implicit zero columns

#[derive(Debug)]
pub struct DictionaryProgram {
    log_size: usize,
    hash: [F; 8],
    dictionary: Vec<[F; N_INSTRUCTION_COLUMNS]>,
    rows: Vec<u32>,
}

impl DictionaryProgram {
    /// Authenticate ALL bytes against a trusted release pin before parsing any artifact lengths.
    /// The caller's digest must come from a trusted table-to-Poseidon linkage check, never the file.
    pub fn from_pinned_bytes(bytes: &[u8], digest: &[u8; 64], expected_hash: [u32; 8]) -> Result<Self, String> {
        if bytes.len() < HEADER_LEN || bytes.len() > 32 * 1024 * 1024 { return Err("artifact size".into()); }
        init_profile_mark(10);
        if sha512_bytes(bytes) != *digest { return Err("artifact digest differs from release pin".into()); }
        init_profile_mark(11);
        Self::decode(bytes, expected_hash)
    }

    fn decode(bytes: &[u8], expected_hash: [u32; 8]) -> Result<Self, String> {
        if &bytes[..8] != VERIFIER_ARTIFACT_MAGIC { return Err("artifact version".into()); }
        let word = |i: usize| u32::from_le_bytes(bytes[i..i + 4].try_into().unwrap());
        let log_size = word(8) as usize;
        let count = word(12) as usize;
        if log_size > 20 || count == 0 || count > 1 << log_size { return Err("artifact dimensions".into()); }
        let n_rows = 1 << log_size;
        let data_end = HEADER_LEN + count * N_INSTRUCTION_COLUMNS * 4;
        if bytes.len() != data_end + n_rows * 4 { return Err("artifact length or trailing bytes".into()); }
        let hash = std::array::from_fn(|i| word(16 + i * 4));
        if hash != expected_hash || hash.iter().any(|&v| v >= F::ORDER_U32) { return Err("artifact VK hash".into()); }
        let mut dictionary = Vec::with_capacity(count);
        for row in bytes[HEADER_LEN..data_end].chunks_exact(N_INSTRUCTION_COLUMNS * 4) {
            let mut fields = [F::ZERO; N_INSTRUCTION_COLUMNS];
            for (field, raw) in fields.iter_mut().zip(row.chunks_exact(4)) {
                let value = u32::from_le_bytes(raw.try_into().unwrap());
                if value >= F::ORDER_U32 { return Err("noncanonical artifact field".into()); }
                *field = F::from_u32(value);
            }
            dictionary.push(fields);
        }
        let mut rows = Vec::with_capacity(n_rows);
        for raw in bytes[data_end..].chunks_exact(4) {
            let index = u32::from_le_bytes(raw.try_into().unwrap());
            if index as usize >= count { return Err("artifact dictionary index".into()); }
            rows.push(index);
        }
        init_profile_mark(12);
        Ok(Self { log_size, hash: hash.map(F::from_u32), dictionary, rows })
    }

    /// Deterministic offline encoding. The exporter must verify the original Poseidon VK hash
    /// and compare the decoded table cell-for-cell before publishing this artifact's digest.
    pub fn encode_bytecode(bytecode: &Bytecode) -> Vec<u8> {
        use std::collections::HashMap;
        assert_eq!(N_INSTRUCTION_COLUMNS.next_power_of_two(), 16);
        let mut indices = HashMap::new();
        let mut dictionary: Vec<[u32; N_INSTRUCTION_COLUMNS]> = Vec::new();
        let mut rows = Vec::with_capacity(bytecode.size());
        for row in bytecode.instructions_multilinear().chunks_exact(16) {
            assert!(row[N_INSTRUCTION_COLUMNS..].iter().all(|f| f.is_zero()));
            let key = std::array::from_fn(|i| row[i].as_canonical_u32());
            let next = dictionary.len() as u32;
            let index = *indices.entry(key).or_insert_with(|| { dictionary.push(key); next });
            rows.push(index);
        }
        let mut bytes = Vec::with_capacity(HEADER_LEN + dictionary.len() * N_INSTRUCTION_COLUMNS * 4 + rows.len() * 4);
        bytes.extend_from_slice(VERIFIER_ARTIFACT_MAGIC);
        bytes.extend_from_slice(&(bytecode.log_size() as u32).to_le_bytes());
        bytes.extend_from_slice(&(dictionary.len() as u32).to_le_bytes());
        for field in bytecode.hash() { bytes.extend_from_slice(&field.as_canonical_u32().to_le_bytes()); }
        for row in dictionary { for field in row { bytes.extend_from_slice(&field.to_le_bytes()); } }
        for index in rows { bytes.extend_from_slice(&index.to_le_bytes()); }
        bytes
    }

    /// Offline release audit only: expands for exact comparison and original Poseidon hashing.
    pub fn expand_for_audit(&self) -> Vec<F> {
        let mut dense = Vec::with_capacity(self.rows.len() * 16);
        for &id in &self.rows {
            dense.extend_from_slice(&self.dictionary[id as usize]);
            dense.resize(dense.len() + 16 - N_INSTRUCTION_COLUMNS, F::ZERO);
        }
        dense
    }
}

impl VerifierProgram for DictionaryProgram {
    fn log_size(&self) -> usize { self.log_size }
    fn hash(&self) -> &[F; 8] { &self.hash }
    fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF {
        assert_eq!(point.len(), self.cumulated_n_vars());
        if point.iter().all(|x| x.is_zero()) { return EF::from(self.dictionary[self.rows[0] as usize][0]); }
        // Coordinates are most-significant first: log_size row bits, then four column bits.
        // D_j(c) = sum_k dictionary[j][k] eq(c,k); f(r,c) = sum_i eq(r,i) D_rows[i](c).
        // Columns 12..16 are identically zero, including at non-Boolean extension-field points.
        let (row_point, col_point) = point.split_at(self.log_size);
        let column_weights = eval_eq_sequential(col_point);
        let values: Vec<EF> = self.dictionary.iter().map(|row| {
            row.iter().zip(&column_weights).map(|(&f, &w)| w * f).sum()
        }).collect();
        let mid = self.log_size / 2;
        let high = eval_eq_sequential(&row_point[..self.log_size - mid]);
        let low = eval_eq_sequential(&row_point[self.log_size - mid..]);
        self.rows.chunks_exact(1 << mid).zip(high).map(|(row, h)| {
            h * row.iter().zip(&low).map(|(&id, &w)| values[id as usize] * w).sum::<EF>()
        }).sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample(log_size: usize) -> DictionaryProgram {
        DictionaryProgram {
            log_size, hash: [F::ZERO; 8],
            dictionary: (0..3).map(|i| std::array::from_fn(|j| F::from_usize(i * 17 + j * j))).collect(),
            rows: (0..1 << log_size).map(|i| ((i * 7 + i / 3) % 3) as u32).collect(),
        }
    }

    #[test]
    fn dictionary_matches_dense_at_boolean_and_extension_points() {
        for log in 2..9 {
            let p = sample(log);
            let dense = p.expand_for_audit();
            for seed in 0..10 {
                let point = MultilinearPoint((0..log + 4).map(|i| {
                    if seed < 2 { EF::from_usize((i + seed) % 2) } else {
                        EF::from_basis_coefficients_slice(&std::array::from_fn::<_, 5, _>(|j| F::from_usize(seed * 13 + i * 7 + j))).unwrap()
                    }
                }).collect());
                assert_eq!(p.evaluate(&point), dense.evaluate_sequential(&point), "log {log} seed {seed}");
            }
            let zero = MultilinearPoint(vec![EF::ZERO; log + 4]);
            assert_eq!(p.evaluate(&zero), EF::from(dense[0]));
        }
    }

    fn wire() -> Vec<u8> {
        let p = sample(2);
        let mut bytes = VERIFIER_ARTIFACT_MAGIC.to_vec();
        for word in [2, 3].into_iter().chain([0; 8]) { bytes.extend_from_slice(&u32::to_le_bytes(word)); }
        for row in p.dictionary { for value in row { bytes.extend_from_slice(&value.as_canonical_u32().to_le_bytes()); } }
        for id in p.rows { bytes.extend_from_slice(&id.to_le_bytes()); }
        bytes
    }

    #[test]
    fn authentication_and_decoder_reject_malformed_artifacts() {
        let good = wire();
        let pin = sha512_bytes(&good);
        assert!(DictionaryProgram::from_pinned_bytes(&good, &pin, [0; 8]).is_ok());
        // Authentication of every byte, including dimensions, table, mapping and embedded VK.
        for i in 0..good.len() {
            let mut bad = good.clone(); bad[i] ^= 1;
            assert!(DictionaryProgram::from_pinned_bytes(&bad, &pin, [0; 8]).is_err());
        }
        for len in 0..good.len() { assert!(DictionaryProgram::from_pinned_bytes(&good[..len], &pin, [0; 8]).is_err()); }
        // Even with a test-only matching digest, decoding rejects invalid semantics.
        for (offset, value) in [(8, 21), (12, 0), (12, u32::MAX), (16, 1), (48, F::ORDER_U32), (good.len() - 4, 3)] {
            let mut bad = good.clone(); bad[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
            assert!(DictionaryProgram::from_pinned_bytes(&bad, &sha512_bytes(&bad), [0; 8]).is_err());
        }
        let mut trailing = good.clone(); trailing.push(0);
        assert!(DictionaryProgram::from_pinned_bytes(&trailing, &sha512_bytes(&trailing), [0; 8]).is_err());
    }
}
