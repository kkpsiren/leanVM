//! The ed25519 leaf (Phase D): a leaf statement proved by the zkDSL driver below over the VM's ed25519
//! tables. One leaf = N_seg signatures of one blob, sorted by signer.
//!
//! Transcript v1 (all Poseidon16 = leanVM's `poseidon16_permute`; `step(state, chunk) = P(state[0..8] ‖ chunk)`,
//! digests are the rate half `[8..16]` of the last state):
//!   packed cells: 32 bytes → 11 cells of 3 bytes (little-endian, last cell 2 bytes); 20 bytes → 7 cells.
//!   root_seg = chain over IV_ROOT=[DOMAIN_ROOT,0…] ‖ [n,0…], then per signature the 3 chunks
//!             [A0..A7], [A8,A9,A10,D0..D4], [D5,D6,0×6] of (A packed 11 ‖ digest packed 7).
//!   meta     = [n_seg, seg_index, version, 0 (H_excl, excl = ∅), blob_id0..3] ‖ [blob_id4..8, 0×3]
//!              (16 cells; blob_id = nine 30-bit chunks of the 32-byte versioned hash, all 256 bits — v2)
//!   H_leaf   = step(P(root_seg ‖ meta[0..8]), meta[8..16])[8..16]  = the 8-cell public input.
//!   ctx      = chain over IV_CTX=[DOMAIN_CTX,0…] ‖ root_seg, then meta, then per signature the 3 chunks
//!             [R0..R7], [R8,R9,R10,s0..s4], [s5..s10,0,0] of (R packed 11 ‖ s packed 11) — R and s are
//!             absorbed before ρ (spec §5, F2).
//!   ρ_i      = P(ctx ‖ [i, DOMAIN_RHO, 0×6])[8..12]  (4 cells, 124 bits, read by scalar_l).
//! Signer groups: hinted start flags; every signature asserts its column key equals its group's key (F8);
//! per group: ed_decompress(A), ed_sig(Q'_j) with A = 8Q' asserted cell by cell, a K chain, signer_scalar.
//! The base point record is a constant array in the bytecode (F5).

use crate::prove_execution::{ExecutionProof, prove_execution};
use crate::verify_execution::verify_execution;
use backend::*;
use curve25519_dalek::edwards::CompressedEdwardsY;
use curve25519_dalek::scalar::Scalar;
use lean_compiler::*;
use lean_vm::ed25519::curve::base_point;
use lean_vm::ed25519::decompress_table::decompress_affine;
use lean_vm::ed25519::gadgets::{P_25519, mod_sub};
use lean_vm::*;

pub const DOMAIN_ROOT: usize = 7002;
pub const DOMAIN_CTX: usize = 7001;
pub const DOMAIN_RHO: usize = 7003;
pub const LEAF_VERSION: usize = 2;
/// Largest leaf that is guaranteed to fit the table caps for ANY signer diversity. EdAdd binds:
/// worst-case rows 39·N + 26,926 (G = N distinct signers) must stay under 2^17; SHA-512 (21·N) under
/// 2^16 is looser. Raising this needs EdAdd log 19 / SHA log 17 in MAX_LOG_N_ROWS_PER_TABLE.
pub const MAX_LEAF_SIGS: usize = 2670;

/// One signature as stored in the blob columns: pubkey (32), digest (20), signature R ‖ s (64).
#[derive(Clone, Debug)]
pub struct SigRow { pub pubkey: [u8; 32], pub digest: [u8; 20], pub sig: [u8; 64] }

#[allow(missing_debug_implementations)]
pub struct LeafWitness {
    pub n_seg: usize,
    pub n_groups: usize,
    pub rows: Vec<SigRow>,       // sorted by signer
    pub public_input: [F; PUBLIC_INPUT_LEN],
    pub witness: ExecutionWitness,
}

pub fn f(x: usize) -> F { F::from_usize(x) }
fn permute(l: &[F; 8], r: &[F; 8]) -> [F; 16] { let mut inp = [F::ZERO; 16]; inp[..8].copy_from_slice(l); inp[8..].copy_from_slice(r); poseidon16_permute(inp) }
fn step(state: &[F; 16], chunk: &[F; 8]) -> [F; 16] { permute(&state[..8].try_into().unwrap(), chunk) }
fn rate(state: &[F; 16]) -> [F; 8] { state[8..].try_into().unwrap() }
pub fn pack11(b: &[u8]) -> [F; 11] { let mut o = [F::ZERO; 11]; for k in 0..10 { o[k] = f(b[3 * k] as usize + 256 * b[3 * k + 1] as usize + 65536 * b[3 * k + 2] as usize); } o[10] = f(b[30] as usize + 256 * b[31] as usize); o }
pub fn pack7(b: &[u8]) -> [F; 7] { let mut o = [F::ZERO; 7]; for k in 0..6 { o[k] = f(b[3 * k] as usize + 256 * b[3 * k + 1] as usize + 65536 * b[3 * k + 2] as usize); } o[6] = f(b[18] as usize + 256 * b[19] as usize); o }

/// meta = [n_seg, seg_index, version, 0, blob_id0..3] ‖ [blob_id4..8, 0, 0, 0] (two 8-cell blocks)
pub fn leaf_meta(n_seg: usize, seg_index: usize, blob_id: &[F; 9]) -> [F; 16] {
    [f(n_seg), f(seg_index), f(LEAF_VERSION), F::ZERO, blob_id[0], blob_id[1], blob_id[2], blob_id[3], blob_id[4], blob_id[5], blob_id[6], blob_id[7], blob_id[8], F::ZERO, F::ZERO, F::ZERO]
}
fn meta_blocks(meta: &[F; 16]) -> ([F; 8], [F; 8]) { (meta[..8].try_into().unwrap(), meta[8..].try_into().unwrap()) }

/// root_seg over the columns (what the indexer recomputes from the decoded blob).
pub fn root_seg(rows: &[SigRow]) -> [F; 8] {
    let mut iv = [F::ZERO; 8]; iv[0] = f(DOMAIN_ROOT);
    let mut hdr = [F::ZERO; 8]; hdr[0] = f(rows.len());
    let mut st = permute(&iv, &hdr);
    for r in rows {
        let a = pack11(&r.pubkey); let d = pack7(&r.digest);
        let c0: [F; 8] = a[..8].try_into().unwrap();
        let c1: [F; 8] = [a[8], a[9], a[10], d[0], d[1], d[2], d[3], d[4]];
        let c2: [F; 8] = [d[5], d[6], F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO, F::ZERO];
        st = step(&st, &c0); st = step(&st, &c1); st = step(&st, &c2);
    }
    rate(&st)
}
pub fn h_leaf(root: &[F; 8], meta: &[F; 16]) -> [F; 8] { let (m0, m1) = meta_blocks(meta); rate(&step(&permute(root, &m0), &m1)) }
fn ctx_seg(root: &[F; 8], meta: &[F; 16], rows: &[SigRow]) -> [F; 8] {
    let mut iv = [F::ZERO; 8]; iv[0] = f(DOMAIN_CTX);
    let mut st = permute(&iv, root);
    let (m0, m1) = meta_blocks(meta);
    st = step(&st, &m0); st = step(&st, &m1);
    for r in rows {
        let rp = pack11(&r.sig[..32]); let sp = pack11(&r.sig[32..]);
        let c0: [F; 8] = rp[..8].try_into().unwrap();
        let c1: [F; 8] = [rp[8], rp[9], rp[10], sp[0], sp[1], sp[2], sp[3], sp[4]];
        let c2: [F; 8] = [sp[5], sp[6], sp[7], sp[8], sp[9], sp[10], F::ZERO, F::ZERO];
        st = step(&st, &c0); st = step(&st, &c1); st = step(&st, &c2);
    }
    rate(&st)
}
fn rho_cells(ctx: &[F; 8], i: usize) -> [F; 4] { let mut r = [F::ZERO; 8]; r[0] = f(i); r[1] = f(DOMAIN_RHO); let o = permute(ctx, &r); [o[8], o[9], o[10], o[11]] }

/// The reader side: recompute the public input from the decoded columns and the leaf parameters.
/// READER CONTRACT — canonical row order. A leaf hashes its rows in this order: a STABLE sort by the
/// 32 raw pubkey bytes (lexicographic), ties keeping the input order. The input order is the blob
/// order of the segment. Every digest a reader recomputes must go through this function.
pub fn canonical_rows(rows: &[SigRow]) -> Vec<SigRow> {
    let mut sorted = rows.to_vec();
    sorted.sort_by(|a, b| a.pubkey.cmp(&b.pubkey));
    sorted
}

/// READER CONTRACT (v2) — blob id cells from the blob's 32-byte KZG versioned hash: read the 32 bytes
/// as a little-endian 256-bit integer and cut it into nine 30-bit chunks, `cell[i] = bits [30i, 30i+30)`
/// (the last chunk carries bits 240..256). All 256 bits are bound; every cell is < 2^30 < p, canonical.
/// (v1 bound only 120 bits — a 2^56 birthday bound for an attacker authoring both blobs.)
pub fn blob_id_cells(versioned_hash: &[u8; 32]) -> [F; 9] {
    std::array::from_fn(|i| {
        let mut v: u32 = 0;
        for bit in 0..30 {
            let b = 30 * i + bit;
            if b < 256 && (versioned_hash[b / 8] >> (b % 8)) & 1 == 1 { v |= 1 << bit; }
        }
        F::from_u32(v)
    })
}

/// Public input of the STANDALONE leaf program (`LEAF_PROGRAM`, tests only). The production leaf
/// digest is the recursion-mode input-data hash (`rec_aggregation::ed25519::expected_leaf_input_data`).
pub fn expected_public_input(rows: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> [F; 8] {
    let rows = canonical_rows(rows);
    h_leaf(&root_seg(&rows), &leaf_meta(rows.len(), seg_index, blob_id))
}

fn cells(b: &[u8]) -> Vec<F> { b.iter().map(|x| f(*x as usize)).collect() }

/// Build the hints and the public input for a leaf. Rows are sorted by signer (stable). Returns None
/// if a signature is malformed for the statement (s ≥ L, R/A not decodable or small-order).
pub fn build_leaf(rows_in: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Result<LeafWitness, String> {
    let (rows, n_groups, meta, root, buffers) = leaf_hint_buffers(rows_in, seg_index, blob_id)?;
    let public_input = h_leaf(&root, &meta);
    let mut hints = Hints::default();
    let bytecode = leaf_bytecode();
    hints.insert(&bytecode, "meta", arena_vec![ArenaVec::from_slice(&meta)]);
    for (name, v) in &buffers { hints.insert(&bytecode, name, arena_vec![ArenaVec::from_slice(v)]); }
    let witness = ExecutionWitness { hints, ..Default::default() };
    Ok(LeafWitness { n_seg: rows.len(), n_groups, rows, public_input, witness })
}

/// ρ_i as the driver derives it (for tests / the oracle).
pub fn leaf_rhos(rows_sorted: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Vec<[F; 4]> {
    let root = root_seg(rows_sorted); let meta = leaf_meta(rows_sorted.len(), seg_index, blob_id);
    let ctx = ctx_seg(&root, &meta, rows_sorted);
    (0..rows_sorted.len()).map(|i| rho_cells(&ctx, i)).collect()
}

/// The placeholders of the leaf driver (also used by the recursion program's leaf mode).
pub fn leaf_program_replacements() -> Vec<(String, String)> {
    let bp = base_point();
    let mut rec: Vec<usize> = vec![]; rec.extend(bp.x.iter().map(|b| *b as usize)); rec.extend(bp.y.iter().map(|b| *b as usize)); rec.push(0); rec.extend(mod_sub(&[0u8; 32], &bp.x, &P_25519).iter().map(|b| *b as usize));
    let bpt = format!("[{}]", rec.iter().map(usize::to_string).collect::<Vec<_>>().join(", "));
    vec![
        ("BPT_PLACEHOLDER".to_string(), bpt),
        ("DOMAIN_ROOT_PLACEHOLDER".to_string(), DOMAIN_ROOT.to_string()),
        ("DOMAIN_CTX_PLACEHOLDER".to_string(), DOMAIN_CTX.to_string()),
        ("DOMAIN_RHO_PLACEHOLDER".to_string(), DOMAIN_RHO.to_string()),
        ("MAX_LEAF_SIGS_PLACEHOLDER".to_string(), MAX_LEAF_SIGS.to_string()),
    ]
}
pub fn leaf_program() -> String {
    let mut src = LEAF_PROGRAM.to_string();
    for (k, v) in leaf_program_replacements() { src = src.replace(&k, &v); }
    src
}

/// The leaf's hint buffers (without `meta`), the sorted rows, meta and root — shared by the standalone
/// leaf program and the recursion program's leaf mode.
pub fn leaf_hint_buffers(rows_in: &[SigRow], seg_index: usize, blob_id: &[F; 9]) -> Result<(Vec<SigRow>, usize, [F; 16], [F; 8], Vec<(&'static str, Vec<F>)>), String> {
    let mut rows = rows_in.to_vec();
    let mut rows = canonical_rows(&rows);
    let n = rows.len();
    if n == 0 { return Err("empty leaf".into()); }
    if n > MAX_LEAF_SIGS { return Err(format!("leaf has {n} signatures; the table caps guarantee a fit only up to {MAX_LEAF_SIGS} (see MAX_LEAF_SIGS)")); }
    let inv8 = Scalar::from(8u64).invert();
    let (mut q, mut s, mut cols, mut gstart, mut qa) = (vec![], vec![], vec![], vec![], vec![]);
    let mut n_groups = 0;
    for (i, r) in rows.iter().enumerate() {
        let s_bytes: [u8; 32] = r.sig[32..].try_into().unwrap();
        let s_opt: Option<Scalar> = Scalar::from_canonical_bytes(s_bytes).into();
        s_opt.ok_or_else(|| format!("signature {i}: s >= L"))?;
        let r_pt = CompressedEdwardsY(r.sig[..32].try_into().unwrap()).decompress().ok_or_else(|| format!("signature {i}: R does not decompress"))?;
        if r_pt.compress().to_bytes() != r.sig[..32] { return Err(format!("signature {i}: R not canonical")); }
        if r_pt.is_small_order() { return Err(format!("signature {i}: R small order")); }
        if !r_pt.is_torsion_free() { return Err(format!("signature {i}: R has a torsion component (dalek verify_strict may accept it; the R = 8·Q certificate cannot)")); }
        let qp = r_pt * inv8;
        let qa_ff = decompress_affine(&qp.compress().to_bytes()).ok_or("Q decode")?;
        q.extend(cells(&qa_ff.x)); q.extend(cells(&qa_ff.y));
        s.extend(cells(&s_bytes));
        cols.extend(cells(&r.pubkey)); cols.extend(cells(&r.digest));
        let start = i == 0 || rows[i - 1].pubkey != r.pubkey;
        gstart.push(F::from_bool(start));
        if start {
            n_groups += 1;
            let a_pt = CompressedEdwardsY(r.pubkey).decompress().ok_or_else(|| format!("signer of {i}: A does not decompress"))?;
            if a_pt.is_small_order() { return Err(format!("signer of {i}: A small order")); }
            if !a_pt.is_torsion_free() { return Err(format!("signer of {i}: A has a torsion component (dalek verify_strict may accept it; the A = 8·Q' certificate cannot)")); }
            let qap = decompress_affine(&(a_pt * inv8).compress().to_bytes()).ok_or("Q' decode")?;
            qa.extend(cells(&qap.x)); qa.extend(cells(&qap.y));
        } else { qa.extend(std::iter::repeat_n(F::ZERO, 64)); }
    }
    let root = root_seg(&rows);
    let meta = leaf_meta(n, seg_index, blob_id);
    Ok((rows, n_groups, meta, root, vec![("cols", cols), ("q", q), ("s", s), ("gstart", gstart), ("qa", qa)]))
}
pub fn leaf_bytecode() -> Bytecode { compile_program_with_flags(&ProgramSource::Raw(leaf_program()), CompilationFlags::default()) }

pub fn prove_leaf(leaf: &LeafWitness, whir_config: &WhirConfigBuilder) -> Result<ExecutionProof, crate::ProverError> {
    prove_execution(&leaf_bytecode(), &leaf.public_input, &leaf.witness, whir_config, false)
}
pub fn verify_leaf(public_input: &[F; PUBLIC_INPUT_LEN], proof: Proof<F>) -> Result<(), ProofError> {
    verify_execution(&leaf_bytecode(), public_input, proof).map(|_| ())
}

/// Parse the dataset format ({signer, digest, sig} hex triples).
pub fn rows_from_json(path: &str) -> Vec<SigRow> {
    let v: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(path).expect("dataset")).expect("json");
    let hx = |s: &str| -> Vec<u8> { (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect() };
    v.as_array().unwrap().iter().map(|r| SigRow {
        pubkey: hx(r["signer"].as_str().unwrap()).try_into().unwrap(),
        digest: hx(r["digest"].as_str().unwrap()).try_into().unwrap(),
        sig: hx(r["sig"].as_str().unwrap()).try_into().unwrap(),
    }).collect()
}

pub const LEAF_PROGRAM: &str = r#"
DOMAIN_ROOT = DOMAIN_ROOT_PLACEHOLDER
DOMAIN_CTX = DOMAIN_CTX_PLACEHOLDER
DOMAIN_RHO = DOMAIN_RHO_PLACEHOLDER
BPT = BPT_PLACEHOLDER

def pack11(src, dst):
    for k in unroll(0, 10):
        dst[k] = src[3 * k] + 256 * src[3 * k + 1] + 65536 * src[3 * k + 2]
    dst[10] = src[30] + 256 * src[31]
    return

def pack7(src, dst):
    for k in unroll(0, 6):
        dst[k] = src[3 * k] + 256 * src[3 * k + 1] + 65536 * src[3 * k + 2]
    dst[6] = src[18] + 256 * src[19]
    return

def main():
    meta = Array(16)
    hint_witness("meta", meta)
    n = meta[0]
    cols = Array(52 * n)
    hint_witness("cols", cols)
    q = Array(64 * n)
    hint_witness("q", q)
    s = Array(32 * n)
    hint_witness("s", s)
    gstart = Array(n)
    hint_witness("gstart", gstart)
    qa = Array(64 * n)
    hint_witness("qa", qa)
    zeros = Array(64)
    for t in unroll(0, 64):
        zeros[t] = 0
    bpt = Array(97)
    for t in unroll(0, 97):
        bpt[t] = BPT[t]

    # ---- root over the columns
    rst = Array(16 * (3 * n + 1))
    ivr = Array(8)
    ivr[0] = DOMAIN_ROOT
    for t in unroll(1, 8):
        ivr[t] = 0
    hdr = Array(8)
    hdr[0] = n
    for t in unroll(1, 8):
        hdr[t] = 0
    poseidon16_permute(ivr, hdr, rst)
    for i in range(0, n):
        apk = Array(11)
        pack11(cols + 52 * i, apk)
        dpk = Array(7)
        pack7(cols + 52 * i + 32, dpk)
        c0 = Array(8)
        c1 = Array(8)
        c2 = Array(8)
        for t in unroll(0, 8):
            c0[t] = apk[t]
        for t in unroll(0, 3):
            c1[t] = apk[8 + t]
        for t in unroll(0, 5):
            c1[3 + t] = dpk[t]
        c2[0] = dpk[5]
        c2[1] = dpk[6]
        for t in unroll(2, 8):
            c2[t] = 0
        poseidon16_permute(rst + 16 * (3 * i), c0, rst + 16 * (3 * i + 1))
        poseidon16_permute(rst + 16 * (3 * i + 1), c1, rst + 16 * (3 * i + 2))
        poseidon16_permute(rst + 16 * (3 * i + 2), c2, rst + 16 * (3 * i + 3))
    root = rst + 16 * (3 * n) + 8

    # ---- H_leaf = the public input: P(root ‖ meta[0..8]), then absorb meta[8..16]
    hl = Array(32)
    poseidon16_permute(root, meta, hl)
    poseidon16_permute(hl, meta + 8, hl + 16)
    pub_in = 0
    for t in unroll(0, 8):
        assert pub_in[t] == hl[24 + t]

    # ---- R records (torsion certificates R = 8Q)
    rrec = Array(97 * n)
    for i in range(0, n):
        ed_sig(q + 64 * i, rrec + 97 * i, 0)

    # ---- ctx sponge: root, meta, then (R packed, s packed) per signature
    cst = Array(16 * (3 * n + 3))
    ivc = Array(8)
    ivc[0] = DOMAIN_CTX
    for t in unroll(1, 8):
        ivc[t] = 0
    poseidon16_permute(ivc, root, cst)
    poseidon16_permute(cst, meta, cst + 16)
    poseidon16_permute(cst + 16, meta + 8, cst + 32)
    for i in range(0, n):
        rb = Array(32)
        for t in unroll(0, 31):
            rb[t] = rrec[97 * i + 32 + t]
        rb[31] = rrec[97 * i + 63] + 128 * rrec[97 * i + 64]
        rpk = Array(11)
        pack11(rb, rpk)
        spk = Array(11)
        pack11(s + 32 * i, spk)
        c0 = Array(8)
        c1 = Array(8)
        c2 = Array(8)
        for t in unroll(0, 8):
            c0[t] = rpk[t]
        for t in unroll(0, 3):
            c1[t] = rpk[8 + t]
        for t in unroll(0, 5):
            c1[3 + t] = spk[t]
        for t in unroll(0, 6):
            c2[t] = spk[5 + t]
        c2[6] = 0
        c2[7] = 0
        poseidon16_permute(cst + 16 * (3 * i + 2), c0, cst + 16 * (3 * i + 3))
        poseidon16_permute(cst + 16 * (3 * i + 3), c1, cst + 16 * (3 * i + 4))
        poseidon16_permute(cst + 16 * (3 * i + 4), c2, cst + 16 * (3 * i + 5))
    ctx = cst + 16 * (3 * n + 2) + 8

    # ---- rho_i = P(ctx, [i, DOMAIN_RHO, 0..])[8..12]
    rho = Array(16 * n)
    for i in range(0, n):
        rin = Array(8)
        rin[0] = i
        rin[1] = DOMAIN_RHO
        for t in unroll(2, 8):
            rin[t] = 0
        poseidon16_permute(ctx, rin, rho + 16 * i)

    # ---- per-signature pipeline with hinted signer groups
    assert gstart[0] == 1
    gk = Array(n + 1)
    gk[0] = 0
    arec = Array(97 * n)
    qarec = Array(97 * n)
    blk = Array(128 * n)
    rec = Array(101 * n)
    out = Array(90 * n)
    sacc = Array(64 * n)
    krec = Array(34 * n)
    kout = Array(84 * n)
    for i in range(0, n):
        g = gstart[i]
        assert g * (g - 1) == 0
        if g == 1:
            gk[i + 1] = i
            ed_decompress(cols + 52 * i, arec + 97 * i, 0)
            ed_sig(qa + 64 * i, qarec + 97 * i, 0)
            for t in unroll(0, 64):
                assert arec[97 * i + t] == qarec[97 * i + t]
            for t in unroll(0, 32):
                sacc[64 * i + t] = 0
            if i == 0:
                for t in unroll(0, 32):
                    sacc[64 * i + 32 + t] = 0
            else:
                for t in unroll(0, 32):
                    sacc[64 * i + 32 + t] = out[90 * (i - 1) + 32 + t]
                for t in unroll(0, 32):
                    krec[34 * i + t] = out[90 * (i - 1) + t]
                krec[34 * i + 32] = arec + 97 * gk[i]
                krec[34 * i + 33] = 1
                signer_scalar(krec + 34 * i, kout + 84 * i, 0)
        else:
            gk[i + 1] = gk[i]
            for t in unroll(0, 32):
                assert cols[52 * i + t] == cols[52 * gk[i] + t]
        for t in unroll(0, 31):
            blk[128 * i + t] = rrec[97 * i + 32 + t]
        blk[128 * i + 31] = rrec[97 * i + 63] + 128 * rrec[97 * i + 64]
        for t in unroll(0, 32):
            blk[128 * i + 32 + t] = cols[52 * i + t]
        for t in unroll(0, 20):
            blk[128 * i + 64 + t] = cols[52 * i + 32 + t]
        blk[128 * i + 84] = 128
        for t in unroll(85, 126):
            blk[128 * i + t] = 0
        blk[128 * i + 126] = 2
        blk[128 * i + 127] = 160
        sha512(blk + 128 * i, rec + 101 * i, zeros)
        for t in unroll(0, 32):
            rec[101 * i + 64 + t] = s[32 * i + t]
        for t in unroll(0, 4):
            rec[101 * i + 96 + t] = rho[16 * i + 8 + t]
        rec[101 * i + 100] = rrec + 97 * i
        if g == 1:
            scalar_l(rec + 101 * i, sacc + 64 * i, out + 90 * i)
        else:
            scalar_l(rec + 101 * i, out + 90 * (i - 1), out + 90 * i)
    # ---- close the last group and the S row
    lk = Array(34)
    for t in unroll(0, 32):
        lk[t] = out[90 * (n - 1) + t]
    lk[32] = arec + 97 * gk[n]
    lk[33] = 1
    lkout = Array(84)
    signer_scalar(lk, lkout, 0)
    srec = Array(34)
    for t in unroll(0, 32):
        srec[t] = out[90 * (n - 1) + 32 + t]
    srec[32] = bpt
    srec[33] = 0
    sout = Array(84)
    signer_scalar(srec, sout, 0)
    return
"#;

#[cfg(test)]
mod contract_tests {
    use super::*;
    /// Canonical order: stable sort by the 32 pubkey bytes; ties keep input (blob) order, even when the
    /// repeated signer's rows are not adjacent in the input.
    #[test]
    fn canonical_order_is_a_stable_sort_by_pubkey() {
        let row = |k: u8, d: u8| SigRow { pubkey: [k; 32], digest: [d; 20], sig: [0; 64] };
        let input = vec![row(2, 1), row(1, 2), row(2, 3), row(1, 4)];
        let c = canonical_rows(&input);
        let key = |r: &SigRow| (r.pubkey[0], r.digest[0]);
        assert_eq!(c.iter().map(key).collect::<Vec<_>>(), vec![(1, 2), (1, 4), (2, 1), (2, 3)]);
        // the root depends on the order, so an unstable or unsorted reader would disagree
        assert_ne!(root_seg(&input), root_seg(&c));
    }
    /// The leaf cap is derived from the table caps: EdAdd worst case (all-distinct signers) 39·N + 26,926
    /// and SHA-512 21·N rows must fit their tables at MAX_LEAF_SIGS (and not at MAX_LEAF_SIGS + 1 for the
    /// binding one).
    #[test]
    fn leaf_cap_matches_table_caps() {
        use lean_vm::ed25519::{ed_add_table as t3, scalar_table as t4, signer_scalar_table as t7};
        let ed_add = 1usize << lean_vm::max_log_n_rows_per_table(&Table::ed_add());
        let sha = 1usize << lean_vm::max_log_n_rows_per_table(&Table::sha512());
        // worst case, all-distinct signers (G = N): ρ·R routes per signature, K·A per signer plus the S
        // row, the dense red1/red2 structure, and the Horner chain
        let ed_add_rows = |n: usize| t4::WINDOWS * n + t7::T7_WINDOWS * (n + 1) + 2 * t3::N_WINDOWS * t3::N_BUCKETS + (t3::N_WINDOWS - 1) * (t3::N_DBL + 1) + 1;
        assert_eq!(ed_add_rows(0), 26_926, "the constant model in the MAX_LEAF_SIGS doc drifted from the table constants");
        assert!(ed_add_rows(MAX_LEAF_SIGS) < ed_add, "EdAdd worst case exceeds its cap at MAX_LEAF_SIGS");
        assert!(21 * MAX_LEAF_SIGS < sha, "SHA-512 rows exceed its cap at MAX_LEAF_SIGS");
        assert!(ed_add_rows(MAX_LEAF_SIGS + 1) >= ed_add || 21 * (MAX_LEAF_SIGS + 1) >= sha, "MAX_LEAF_SIGS is not tight against the table caps");
    }
    #[test]
    fn blob_id_cells_are_30_bit_canonical_and_bind_all_256_bits() {
        let mut h = [0u8; 32]; h[0] = 0x01; h[3] = 0xFF; h[4] = 0x12; h[7] = 0x80; h[30] = 0xCD; h[31] = 0xAB;
        let c = blob_id_cells(&h);
        assert_eq!(c[0], F::from_u32(0x3F00_0001), "bits 0..30: byte0 and the low 6 bits of byte3");
        assert_eq!(c[1], F::from_u32(0x4B), "bits 30..60: the top 2 bits of byte3, then byte4 << 2");
        assert_eq!(c[2], F::from_u32(8), "bits 60..90: bit 63 (byte7 = 0x80) lands at position 3");
        for k in 3..8 { assert_eq!(c[k], F::ZERO); }
        assert_eq!(c[8], F::from_u32(0xABCD), "bits 240..256: the last two bytes, all 256 bits bound");
        // every cell is a 30-bit value
        let mut hh = [0xFFu8; 32];
        for c in blob_id_cells(&hh) { assert!(c.to_usize() < 1 << 30); }
        hh[31] = 0x7F; assert_eq!(blob_id_cells(&hh)[8], F::from_u32(0x7FFF));
    }
}
