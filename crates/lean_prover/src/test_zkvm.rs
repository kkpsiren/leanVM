use std::collections::BTreeMap;

use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};

const N: usize = 11;
const M: usize = 3;

const ALL_PRECOMPILES_PROGRAM: &str = r#"
DIM = 5
N = 11
M = 3
DIGEST_LEN = 8
HALF_DIGEST_LEN = 4
SCRATCH_SIZE = 8192
LOOP_ITERS = LOOP_ITERS_PLACEHOLDER
N_POSEIDON = N_POSEIDON_PLACEHOLDER
EXT_LEN = EXT_LEN_PLACEHOLDER
BYTECODE_PAD = BYTECODE_PAD_PLACEHOLDER

def main():
    scratch = Array(SCRATCH_SIZE)
    hint_witness("scratch", scratch)
    poseidon16_compress_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, scratch + 6 * DIGEST_LEN)

    # poseidon16_compress_quarter: only first 4 FE constrained
    full_out = scratch + 6 * DIGEST_LEN
    half_out = scratch + 80
    poseidon16_compress_quarter(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, half_out)
    for i in unroll(0, HALF_DIGEST_LEN):
        assert full_out[i] == half_out[i]

    # poseidon16_compress_half_hardcoded_left: the 4-element prefix lives at a compile-time
    # constant memory offset. Public input is the only region with such addresses, so we
    # place the prefix at public_input[0..4] (= memory address 0..4) and pass offset 0.
    hardcoded_left = scratch + 1496
    hardcoded_full_out = scratch + 1504
    poseidon16_compress_half_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_full_out,
        0
    )

    # Same, but only first 4 FE of the output are constrained.
    hardcoded_half_out = scratch + 1512
    poseidon16_compress_quarter_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_half_out,
        0
    )
    for i in unroll(0, HALF_DIGEST_LEN):
        assert hardcoded_full_out[i] == hardcoded_half_out[i]

    # poseidon16_permute: full 16-element permutation (no feed-forward), written in natural order:
    #   m[res .. res + 16] = poseidon(left || right)
    permute_out = scratch + 1600
    poseidon16_permute(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_out)

    # poseidon16_permute_half: same permutation, but only the low 8 elements are written/constrained.
    permute_half_out = scratch + 1620
    poseidon16_permute_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_half_out)
    for i in unroll(0, DIGEST_LEN):
        assert permute_half_out[i] == permute_out[i]

    # poseidon16_permute_half_hardcoded_left: permutation (low 8) with a hardcoded 4-element left prefix.
    # Uses the same input as the hardcoded compression above, so it equals the permutation of that input.
    permute_hardcoded_out = scratch + 1640
    poseidon16_permute_half_hardcoded_left(hardcoded_left, scratch + 5 * DIGEST_LEN, permute_hardcoded_out, 0)

    base_ptr = scratch + 88
    ext_a_ptr = scratch + 88 + N
    ext_b_ptr = scratch + 88 + N * (DIM + 1)

    # dot_product_be: sum_i base[i] * ext_a[i]
    dot_product_be(base_ptr, ext_a_ptr, scratch + 1000, N)

    # dot_product_ee: sum_i ext_a[i] * ext_b[i]
    dot_product_ee(ext_a_ptr, ext_b_ptr, scratch + 1000 + DIM, N)

    # add_be: sum_i (base[i] + ext_a[i])
    add_be(base_ptr, ext_a_ptr, scratch + 1200, N)

    # add_ee: sum_i (ext_a[i] + ext_b[i])
    add_ee(ext_a_ptr, ext_b_ptr, scratch + 1200 + DIM, N)

    # poly_eq_be: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with base a, ext b
    slice_a_ptr = scratch + 1100
    slice_b_ptr = scratch + 1100 + M
    poly_eq_be(slice_a_ptr, slice_b_ptr, scratch + 1100 + M + M * DIM, M)

    # poly_eq_ee: prod_i (a[i]*b[i] + (1-a[i])*(1-b[i])) with ext a, ext b
    poly_eq_ee(ext_a_ptr, ext_b_ptr, scratch + 1300, N)

    # execution table: a runtime loop (one code copy, LOOP_ITERS cycles).
    c_buf = Array(LOOP_ITERS + 1)
    c_buf[0] = 0
    for i in range(0, LOOP_ITERS):
        c_buf[i + 1] = c_buf[i] + 1
    assert c_buf[LOOP_ITERS] == LOOP_ITERS

    # bytecode size: a dead unrolled block (runtime_zero() is a real call, so the branch can't be folded).
    if runtime_zero() == 1:
        pad = Array(BYTECODE_PAD + 1)
        pad[0] = 1
        for j in unroll(0, BYTECODE_PAD):
            pad[j + 1] = pad[j] + 1

    # poseidon table: a runtime loop of N_POSEIDON poseidon calls (outputs left unread).
    pos_src = Array(16)
    hint_witness("pos_src", pos_src)
    pos_out = Array(N_POSEIDON * 8 + 16)
    for i in range(0, N_POSEIDON):
        poseidon16_permute_half(pos_src, pos_src + 8, pos_out + i * 8)

    # extension table: a single EXT_LEN-long dot product (output left unread too).
    big_a = Array(EXT_LEN * DIM)
    hint_witness("ext_a", big_a)
    big_b = Array(EXT_LEN * DIM)
    hint_witness("ext_b", big_b)
    big_res = Array(DIM)
    dot_product_ee(big_a, big_b, big_res, EXT_LEN)
    return

def runtime_zero():
    return 0
"#;

fn sweep_flags(loop_iters: usize, n_poseidon: usize, ext_len: usize, bytecode_pad: usize) -> CompilationFlags {
    let knobs = [
        ("LOOP_ITERS", loop_iters),
        ("N_POSEIDON", n_poseidon),
        ("EXT_LEN", ext_len),
        ("BYTECODE_PAD", bytecode_pad),
    ];
    CompilationFlags {
        replacements: BTreeMap::from(knobs.map(|(k, v)| (format!("{k}_PLACEHOLDER"), v.to_string()))),
    }
}

fn all_precompiles_witness(ext_len: usize, bytecode: &Bytecode) -> ([F; PUBLIC_INPUT_LEN], ExecutionWitness) {
    let mut rng = StdRng::seed_from_u64(0);
    let mut scratch = F::zero_vec(8192);

    // Poseidon test data
    let poseidon_16_compress_input: [F; 16] = rng.random();
    scratch[32..48].copy_from_slice(&poseidon_16_compress_input);
    let poseidon_output = poseidon16_compress(poseidon_16_compress_input);
    scratch[48..56].copy_from_slice(&poseidon_output[..8]);
    let poseidon_24_input: [F; 24] = rng.random();
    scratch[56..80].copy_from_slice(&poseidon_24_input);
    // poseidon16_compress_quarter output at offset 80: first 4 = hash, last 4 = arbitrary pre-existing data
    scratch[80..84].copy_from_slice(&poseidon_output[..4]);
    scratch[84..88].copy_from_slice(&[
        F::from_usize(111),
        F::from_usize(222),
        F::from_usize(333),
        F::from_usize(444),
    ]);

    // poseidon16_compress_half_hardcoded_left: prefix lives at public_input[0..4] (compile-time
    // constant offset 0), data at scratch[1496..1500], expected output at scratch[1504..1512].
    let hardcoded_prefix: [F; 4] = rng.random();
    let hardcoded_data: [F; 4] = rng.random();
    scratch[1496..1500].copy_from_slice(&hardcoded_data);
    let mut hardcoded_input = [F::ZERO; 16];
    hardcoded_input[..4].copy_from_slice(&hardcoded_prefix);
    hardcoded_input[4..8].copy_from_slice(&hardcoded_data);
    hardcoded_input[8..16].copy_from_slice(&poseidon_16_compress_input[8..16]);
    let hardcoded_output = poseidon16_compress(hardcoded_input);
    scratch[1504..1512].copy_from_slice(&hardcoded_output);
    // half output: first 4 = hash, last 4 = arbitrary pre-existing data
    scratch[1512..1516].copy_from_slice(&hardcoded_output[..4]);
    scratch[1516..1520].copy_from_slice(&[
        F::from_usize(555),
        F::from_usize(666),
        F::from_usize(777),
        F::from_usize(888),
    ]);

    // poseidon16_permute output at 1600..1616: raw permutation result.
    let permute_output = poseidon16_permute(poseidon_16_compress_input);
    scratch[1600..1616].copy_from_slice(&permute_output);

    // poseidon16_permute_half output at 1620..1628: low 8 of the same permutation.
    scratch[1620..1628].copy_from_slice(&permute_output[..8]);

    // poseidon16_permute_half_hardcoded_left output at 1640..1648: low 8 of the permutation of the
    // hardcoded-left input (same input as the hardcoded compression above).
    let permute_hardcoded_output = poseidon16_permute(hardcoded_input);
    scratch[1640..1648].copy_from_slice(&permute_hardcoded_output[..8]);

    // Extension op operands: base[N], ext_a[N], ext_b[N]
    let base_slice: [F; N] = rng.random();
    let ext_a_slice: [EF; N] = rng.random();
    let ext_b_slice: [EF; N] = rng.random();

    let ef_to_f = |slice: &[EF]| -> Vec<F> {
        slice
            .iter()
            .flat_map(|x| x.as_basis_coefficients_slice().to_vec())
            .collect()
    };

    scratch[88..][..N].copy_from_slice(&base_slice);
    scratch[88 + N..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_a_slice));
    scratch[88 + N + N * DIMENSION..][..N * DIMENSION].copy_from_slice(&ef_to_f(&ext_b_slice));

    // dot_product_be result at 1000
    let dot_product_be_result: EF = dot_product(ext_a_slice.into_iter(), base_slice.into_iter());
    scratch[1000..][..DIMENSION].copy_from_slice(dot_product_be_result.as_basis_coefficients_slice());

    // dot_product_ee result at 1005
    let dot_product_ee_result: EF = dot_product(ext_a_slice.into_iter(), ext_b_slice.into_iter());
    scratch[1000 + DIMENSION..][..DIMENSION].copy_from_slice(dot_product_ee_result.as_basis_coefficients_slice());

    // add_be result at 1200: sum_i (EF::from(base[i]) + ext_a[i])
    let add_be_result: EF = (0..N)
        .map(|i| EF::from(base_slice[i]) + ext_a_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    scratch[1200..][..DIMENSION].copy_from_slice(add_be_result.as_basis_coefficients_slice());

    // add_ee result at 1205: sum_i (ext_a[i] + ext_b[i])
    let add_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] + ext_b_slice[i])
        .fold(EF::ZERO, |a, b| a + b);
    scratch[1200 + DIMENSION..][..DIMENSION].copy_from_slice(add_ee_result.as_basis_coefficients_slice());

    // poly_eq_be operands: slice_a[M] (base), slice_b[M] (ext) at 1100
    let slice_a: [F; M] = rng.random();
    let slice_b: [EF; M] = rng.random();
    scratch[1100..][..M].copy_from_slice(&slice_a);
    scratch[1100 + M..][..M * DIMENSION].copy_from_slice(&ef_to_f(&slice_b));

    // poly_eq_be result at 1100 + M + M*DIM = 1118
    let poly_eq_be_result = MultilinearPoint(slice_b.to_vec())
        .eq_poly_outside(&MultilinearPoint(slice_a.iter().map(|&x| EF::from(x)).collect()));
    scratch[1100 + M + M * DIMENSION..][..DIMENSION].copy_from_slice(poly_eq_be_result.as_basis_coefficients_slice());

    // poly_eq_ee result at 1300: prod_i (ext_a[i]*ext_b[i] + (1-ext_a[i])*(1-ext_b[i]))
    let poly_eq_ee_result: EF = (0..N)
        .map(|i| ext_a_slice[i] * ext_b_slice[i] + (EF::ONE - ext_a_slice[i]) * (EF::ONE - ext_b_slice[i]))
        .fold(EF::ONE, |acc, x| acc * x);
    scratch[1300..][..DIMENSION].copy_from_slice(poly_eq_ee_result.as_basis_coefficients_slice());

    let mut public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    public_input[..4].copy_from_slice(&hardcoded_prefix);

    let pos_src: [F; 16] = rng.random();
    let ext_vec = |rng: &mut StdRng| ef_to_f(&(0..ext_len).map(|_| rng.random()).collect::<Vec<EF>>());
    let mut hints = Hints::default();
    hints.insert(bytecode, "scratch", arena_vec![ArenaVec::from_slice(&scratch)]);
    hints.insert(bytecode, "pos_src", arena_vec![ArenaVec::from_slice(&pos_src)]);
    hints.insert(bytecode, "ext_a", arena_vec![ArenaVec::from_slice(&ext_vec(&mut rng))]);
    hints.insert(bytecode, "ext_b", arena_vec![ArenaVec::from_slice(&ext_vec(&mut rng))]);
    let witness = ExecutionWitness {
        hints,
        ..Default::default()
    };
    (public_input, witness)
}

#[test]
fn test_zk_vm_all_precompiles() {
    // Exercises every precompile variant; the sweep knobs are kept small so it stays fast.
    let ext_len = 2;
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(100, 2, ext_len, 4),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len, &bytecode);
    test_zk_vm_helper_with_bytecode(&bytecode, &public_input, witness);
}

/// Exercise the published profile at its production rate without compiling recursion bytecode
/// or proving ed25519 leaves. Covers trace cleanup before WHIR on the three-table path.
#[test]
fn test_zk_vm_terminal_profile_memory_lifetimes() {
    let ext_len = 2;
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(100, 2, ext_len, 4),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len, &bytecode);
    let proof = crate::prove_execution::prove_execution_with_profile(
        &PROFILE_TERMINAL, &bytecode, &public_input, &witness, &default_whir_config(3), false,
    ).unwrap();
    crate::verify_execution::verify_execution_with_profile(
        &PROFILE_TERMINAL, &bytecode, &public_input, proof.proof.clone(),
    ).unwrap();
    assert!(verify_execution(&bytecode, &public_input, proof.proof).is_err());
}

// Python-verifier test vectors: compile ALL_PRECOMPILES_PROGRAM with different runtime flavours (table sizes, etc)

/// One flavour: (loop_iters, n_poseidon, ext_len, bytecode_pad, log_inv_rate).
type SweepConfig = (usize, usize, usize, usize, usize);

fn dump_vector(
    out_dir: &std::path::Path,
    index: usize,
    &(loop_iters, n_poseidon, ext_len, bytecode_pad, rate): &SweepConfig,
) -> serde_json::Value {
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(loop_iters, n_poseidon, ext_len, bytecode_pad),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len, &bytecode);
    let proof = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(rate), false)
        .unwrap()
        .proof;
    let (_details, raw) = verify_execution(&bytecode, &public_input, proof).unwrap();

    let f = |x: F| x.as_canonical_u32();
    let fe = |xs: &[F]| xs.iter().map(|&x| f(x)).collect::<Vec<_>>();
    let dir = out_dir.join(index.to_string());
    std::fs::create_dir_all(&dir).unwrap();
    let mle: Vec<u8> = bytecode
        .instructions_multilinear()
        .iter()
        .flat_map(|&v| f(v).to_le_bytes())
        .collect();
    std::fs::write(dir.join("proof.bytecode_mle.bin"), mle).unwrap();
    let opening = |o: &MerkleOpening<F>| serde_json::json!({ "leaf_data": fe(&o.leaf_data), "path": o.path.iter().map(|d| d.map(f)).collect::<Vec<_>>() });
    let proof_json = serde_json::json!({
        "bytecode_multilinear_path": "proof.bytecode_mle.bin",
        "public_input": fe(&public_input),
        "proof": { "transcript": fe(&raw.transcript), "merkle_openings": raw.merkle_openings.iter().map(opening).collect::<Vec<_>>() },
    });
    std::fs::write(dir.join("proof.json"), serde_json::to_string(&proof_json).unwrap()).unwrap();

    // The proof opens with [log_inv_rate, log_memory, <log-height per table, in ALL_TABLES order>].
    let dims: Vec<usize> = raw.transcript[..2 + N_TABLES]
        .iter()
        .map(|x| x.as_canonical_u32() as usize)
        .collect();
    let heights: serde_json::Map<_, _> = ALL_TABLES
        .iter()
        .enumerate()
        .map(|(i, t)| (t.name().to_string(), dims[2 + i].into()))
        .collect();
    serde_json::json!({
        "dir": index.to_string(), "log_inv_rate": dims[0], "log_memory": dims[1],
        "bytecode_log_size": bytecode.log_size(), "table_log_heights": heights,
    })
}

#[test]
#[ignore]
fn dump_test_vectors_for_python_verifier() {
    let out_dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(std::env::var("CARGO_TARGET_DIR").unwrap_or_else(|_| "target".into()))
        .join("zkvm_test_vectors");
    let _ = std::fs::remove_dir_all(&out_dir);
    std::fs::create_dir_all(&out_dir).unwrap();

    #[rustfmt::skip]
    let configs: [SweepConfig; 5] = [
        (5000, 0,    2,     0,    1), // execution-table dominant
        (2,    0,    2,     4000, 2), // bytecode dominant
        (0,    6000, 2,     0,    3), // poseidon-table heavy
        (0,    0,    30000, 0,    1), // extension-table dominant
        (2000, 200,  100,   300,  4), // mixed
    ];
    let vectors: Vec<_> = configs
        .iter()
        .enumerate()
        .map(|(i, cfg)| dump_vector(&out_dir, i, cfg))
        .collect();
    let manifest = serde_json::json!({ "vectors": vectors });
    std::fs::write(
        out_dir.join("manifest.json"),
        serde_json::to_string_pretty(&manifest).unwrap(),
    )
    .unwrap();
}

#[test]
fn test_small_memory() {
    let program_str = r#"
def main():
    a = Array(1)
    for i in unroll(0, 2**17):
        a[0] = 1 * 2
    return
"#;

    test_zk_vm_helper(program_str, &Default::default());
}

#[test]
fn test_prove_fibonacci() {
    if std::env::var("FIB_TRACING") == Ok("true".to_string()) {
        init_tracing();
    }
    let n = std::env::var("FIB_N")
        .unwrap_or("10000".to_string())
        .parse::<usize>()
        .unwrap();
    let program_str = r#"
N = FIB_N_PLACEHOLDER
STEPS = 10000  # N should be a multiple of STEPS
N_STEPS = N / STEPS

def main():
    x, y = fibonacci_step(0, 1, N_STEPS)
    print(x)
    return

def fibonacci_step(a, b, steps_remaining):
    if steps_remaining == 0:
        return a, b
    new_a, new_b = fibonacci_const(a, b, STEPS)
    res_a, res_b = fibonacci_step(new_a, new_b, steps_remaining - 1)
    return res_a, res_b

def fibonacci_const(a, b, n: Const):
    buff = Array(n + 2)
    buff[0] = a
    buff[1] = b
    for j in unroll(2, n + 2):
        buff[j] = buff[j - 1] + buff[j - 2]
    return buff[n], buff[n + 1]
"#;
    let flags = CompilationFlags {
        replacements: [("FIB_N_PLACEHOLDER".to_string(), n.to_string())].into_iter().collect(),
    };
    test_zk_vm_helper_with_witness(program_str, &Default::default(), ExecutionWitness::default(), flags);
}

fn test_zk_vm_helper(program_str: &str, public_input: &[F; PUBLIC_INPUT_LEN]) {
    test_zk_vm_helper_with_witness(
        program_str,
        public_input,
        ExecutionWitness::default(),
        CompilationFlags::default(),
    )
}

fn test_zk_vm_helper_with_witness(
    program_str: &str,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: ExecutionWitness,
    flags: CompilationFlags,
) {
    init_tracing();
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program_str.to_string()), flags);
    test_zk_vm_helper_with_bytecode(&bytecode, public_input, witness);
}

fn test_zk_vm_helper_with_bytecode(
    bytecode: &Bytecode,
    public_input: &[F; PUBLIC_INPUT_LEN],
    witness: ExecutionWitness,
) {
    let time = std::time::Instant::now();
    let starting_log_inv_rate = 1;
    let proof = prove_execution(
        bytecode,
        public_input,
        &witness,
        &default_whir_config(starting_log_inv_rate),
        false,
    )
    .unwrap();
    let proof_time = time.elapsed();
    verify_execution(bytecode, public_input, proof.proof).unwrap();
    println!("{}", proof.metadata.as_ref().unwrap().display());
    println!("Proof time: {:.3} s", proof_time.as_secs_f32());
}

/// `multibus-toy`: the ExtensionOp table now has three Column-multiplicity buses (the precompile bus,
/// a push of idx_a with the multiplicity, a pull of idx_a with a committed toy column). Honest: proves and
/// verifies. Tampered toy column (prover sanity assert disabled): the VERIFIER must reject.
#[cfg(feature = "multibus-toy")]
#[test]
fn test_multibus_toy_honest_and_tampered() {
    let ext_len = 2;
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(100, 2, ext_len, 4),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len, &bytecode);
    assert_eq!(lean_vm::n_column_buses(&Table::extension_op().bus_interactions()), 3);

    lean_vm::MULTIBUS_TOY_TAMPER.store(false, std::sync::atomic::Ordering::Relaxed);
    let honest = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false).unwrap();
    verify_execution(&bytecode, &public_input, honest.proof).expect("honest multibus proof must verify");

    lean_vm::MULTIBUS_TOY_TAMPER.store(true, std::sync::atomic::Ordering::Relaxed);
    let tampered = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false)
        .expect("a dishonest prover can still produce a transcript");
    lean_vm::MULTIBUS_TOY_TAMPER.store(false, std::sync::atomic::Ordering::Relaxed);
    assert!(
        verify_execution(&bytecode, &public_input, tampered.proof).is_err(),
        "an unbalanced second bus must be rejected by the verifier"
    );
}

/// `multibus-toy` range check: the ExtensionOp toy range column (255 on every row) is pushed into the U8
/// section. Honest: verifies. Tampered to 256 (no AIR constraint, prover sanity assert disabled): the
/// VERIFIER must reject — the only thing catching it is the structural range section.
#[cfg(feature = "multibus-toy")]
#[test]
fn test_range_section_rejects_out_of_range() {
    let ext_len = 2;
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        sweep_flags(100, 2, ext_len, 4),
    );
    let (public_input, witness) = all_precompiles_witness(ext_len, &bytecode);
    assert!(Table::extension_op().bus_interactions().iter().any(|b| b.range_section() == Some(lean_vm::RANGE_U8)));

    lean_vm::MULTIBUS_TOY_RANGE_TAMPER.store(false, std::sync::atomic::Ordering::Relaxed);
    let honest = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false).unwrap();
    verify_execution(&bytecode, &public_input, honest.proof).expect("honest range-checked proof must verify");

    lean_vm::MULTIBUS_TOY_RANGE_TAMPER.store(true, std::sync::atomic::Ordering::Relaxed);
    let tampered = prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false)
        .expect("a dishonest prover can still produce a transcript");
    lean_vm::MULTIBUS_TOY_RANGE_TAMPER.store(false, std::sync::atomic::Ordering::Relaxed);
    assert!(
        verify_execution(&bytecode, &public_input, tampered.proof).is_err(),
        "a 256 in a byte column must be rejected by the range section"
    );
}

/// Phase B: `sha512(block, out, zeros)` on N padded blocks; the driver asserts each 64-byte digest
/// equals the hinted native digest cell by cell (a wrong precompile fails the assert or the proof).
#[test]
fn test_zk_vm_sha512_precompile() {
    use lean_vm::ed25519::sha512_table::{block_words, digest_bytes, pad_single_block, sha512_block};
    let n: usize = std::env::var("SHA_N").ok().and_then(|v| v.parse().ok()).unwrap_or(3);
    let program = r#"
N = N_PLACEHOLDER
def main():
    blk = Array(128 * N)
    hint_witness("blk", blk)
    expect = Array(64 * N)
    hint_witness("expect", expect)
    zeros = Array(64)
    for j in unroll(0, 64):
        zeros[j] = 0
    out = Array(64 * N)
    for i in range(0, N):
        sha512(blk + 128 * i, out + 64 * i, zeros)
        for j in unroll(0, 64):
            assert out[64 * i + j] == expect[64 * i + j]
    return
"#;
    let flags = CompilationFlags { replacements: [("N_PLACEHOLDER".to_string(), n.to_string())].into_iter().collect() };
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program.to_string()), flags);
    let mut blk_cells = vec![]; let mut exp_cells = vec![];
    for i in 0..n {
        let msg: Vec<u8> = (0..(84 + (i % 20))).map(|k| ((k * 7 + i * 13) & 255) as u8).collect();
        let block = pad_single_block(&msg);
        blk_cells.extend(block.iter().map(|b| F::from_usize(*b as usize)));
        exp_cells.extend(digest_bytes(&sha512_block(&block_words(&block))).iter().map(|b| F::from_usize(*b as usize)));
    }
    let mut hints = Hints::default();
    hints.insert(&bytecode, "blk", arena_vec![ArenaVec::from_slice(&blk_cells)]);
    hints.insert(&bytecode, "expect", arena_vec![ArenaVec::from_slice(&exp_cells)]);
    let witness = ExecutionWitness { hints, ..Default::default() };
    println!("sha512 x{n}");
    test_zk_vm_helper_with_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], witness);
}

/// Phase B: N signatures through `sha512` → `scalar_l` (K/S chained by pointer) → `signer_scalar` on the
/// final K. The driver asserts K_red ‖ windows against hints; the test computes K_red independently
/// with num-bigint from (h, ρ, s), so a wrong table cannot agree with it.
#[test]
#[ignore = "superseded by test_zk_vm_ed25519_batch: with EdAdd present the routing tuples of random scalars do not form a valid batch"]
fn test_zk_vm_scalar_chain() {
    use lean_vm::ed25519::gadgets::{L_25519, limbs_to_int, modulus_int};
    use lean_vm::ed25519::scalar_table::rho_from_cells;
    use lean_vm::ed25519::sha512_table::{block_words, digest_bytes, pad_single_block, sha512_block};
    use num_bigint::BigInt;
    use num_integer::Integer;
    let n: usize = std::env::var("SCALAR_N").ok().and_then(|v| v.parse().ok()).unwrap_or(4);
    let program = r#"
N = N_PLACEHOLDER
def main():
    blk = Array(128 * N)
    hint_witness("blk", blk)
    srho = Array(36 * N)
    hint_witness("srho", srho)
    zeros = Array(64)
    for j in unroll(0, 64):
        zeros[j] = 0
    rec = Array(100 * N)
    out = Array(90 * N)
    for i in range(0, N):
        sha512(blk + 128 * i, rec + 100 * i, zeros)
        for j in unroll(0, 36):
            rec[100 * i + 64 + j] = srho[36 * i + j]
    scalar_l(rec, zeros, out)
    for i in range(1, N):
        scalar_l(rec + 100 * i, out + 90 * (i - 1), out + 90 * i)
    kout = Array(84)
    signer_scalar(out + 90 * (N - 1), kout, 0)
    expect = Array(84)
    hint_witness("expect", expect)
    for j in unroll(0, 84):
        assert kout[j] == expect[j]
    return
"#;
    let flags = CompilationFlags { replacements: [("N_PLACEHOLDER".to_string(), n.to_string())].into_iter().collect() };
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program.to_string()), flags);
    let l = modulus_int(&L_25519);
    let mut x = 0x9e3779b97f4a7c15u64; let mut nb = move || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let mut blk_cells = vec![]; let mut srho_cells = vec![];
    let mut k_total = BigInt::from(0u8);
    let mut k_wide = [0i64; 32];
    for _ in 0..n {
        let msg: Vec<u8> = (0..84).map(|_| (nb() & 255) as u8).collect();
        let block = pad_single_block(&msg);
        blk_cells.extend(block.iter().map(|b| F::from_usize(*b as usize)));
        let h = digest_bytes(&sha512_block(&block_words(&block)));
        let s_raw: Vec<u8> = (0..32).map(|_| (nb() & 255) as u8).collect();
        let s_int = limbs_to_int(&s_raw).mod_floor(&l);
        let mut s = [0u8; 32]; for (i, b) in s_int.to_bytes_le().1.iter().enumerate() { s[i] = *b; }
        let rho_cells: [u32; 4] = std::array::from_fn(|_| (nb() % F::ORDER_U64) as u32);
        srho_cells.extend(s.iter().map(|b| F::from_usize(*b as usize)));
        srho_cells.extend(rho_cells.iter().map(|c| F::from_usize(*c as usize)));
        // independent: c = h mod L, k = ρ·c mod L, K_total += k; the lazy limbs sum k's bytes
        let c = limbs_to_int(&h).mod_floor(&l);
        let rho = BigInt::from(rho_from_cells(&rho_cells));
        let k = (&rho * &c).mod_floor(&l);
        k_total += &k;
        let kb = k.to_bytes_le().1; for (i, b) in kb.iter().enumerate() { k_wide[i] += *b as i64; }
    }
    let k_red = k_total.mod_floor(&l);
    // expected output record: K_red bytes ‖ windows from the native T7 row of the same wide sum
    let t7 = lean_vm::ed25519::signer_scalar_table::make_row(&k_wide, 0, false, 0, 0);
    let mut expect: Vec<F> = t7[lean_vm::ed25519::signer_scalar_table::COL_OUT..lean_vm::ed25519::signer_scalar_table::COL_OUT + 84].to_vec();
    let mut kred_bytes = [0u8; 32]; for (i, b) in k_red.to_bytes_le().1.iter().enumerate() { kred_bytes[i] = *b; }
    for i in 0..32 { assert_eq!(expect[i], F::from_usize(kred_bytes[i] as usize), "native T7 disagrees with BigInt at limb {i}"); expect[i] = F::from_usize(kred_bytes[i] as usize); }
    let mut hints = Hints::default();
    hints.insert(&bytecode, "blk", arena_vec![ArenaVec::from_slice(&blk_cells)]);
    hints.insert(&bytecode, "srho", arena_vec![ArenaVec::from_slice(&srho_cells)]);
    hints.insert(&bytecode, "expect", arena_vec![ArenaVec::from_slice(&expect)]);
    let witness = ExecutionWitness { hints, ..Default::default() };
    println!("scalar chain x{n}");
    test_zk_vm_helper_with_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], witness);
}

/// Phase C: a real ed25519 batch end to end. N = M·G signatures (G per signer) generated natively;
/// the driver runs ed_sig (R records), ed_decompress (A records), assembles the SHA-512 blocks from
/// T1's output, chains scalar_l per signer with S carried across signers, reduces each K and S with
/// signer_scalar; the EdAdd post-pass consumes the routing tuples and its final row proves the MSM
/// total is O. A tampered signature scalar must not prove.
fn ed25519_batch_setup(m: usize, g: usize, tamper: bool) -> (Bytecode, ExecutionWitness) {
    use lean_vm::ed25519::curve::{Affine, base_point, scalar_mul_bigint};
    use lean_vm::ed25519::decompress_table::compress;
    use lean_vm::ed25519::gadgets::{L_25519, limbs_to_int, modulus_int};
    use lean_vm::ed25519::sha512_table::{block_words, digest_bytes, pad_single_block, sha512_block};
    use num_bigint::BigInt;
    use num_integer::Integer;
    let n = m * g;
    let program = r#"
N = N_PLACEHOLDER
M = M_PLACEHOLDER
G = G_PLACEHOLDER
def main():
    q = Array(64 * N)
    hint_witness("q", q)
    a = Array(32 * M)
    hint_witness("a", a)
    msg = Array(20 * N)
    hint_witness("msg", msg)
    s = Array(32 * N)
    hint_witness("s", s)
    rho = Array(4 * N)
    hint_witness("rho", rho)
    bpt = Array(97)
    hint_witness("bpt", bpt)
    zeros = Array(64)
    for t in unroll(0, 64):
        zeros[t] = 0
    rrec = Array(97 * N)
    for i in unroll(0, N):
        ed_sig(q + 64 * i, rrec + 97 * i, 0)
    arec = Array(97 * M)
    for j in unroll(0, M):
        ed_decompress(a + 32 * j, arec + 97 * j, 0)
    blk = Array(128 * N)
    rec = Array(101 * N)
    for j in unroll(0, M):
        for gi in unroll(0, G):
            i = j * G + gi
            for t in unroll(0, 31):
                blk[128 * i + t] = rrec[97 * i + 32 + t]
            blk[128 * i + 31] = rrec[97 * i + 63] + 128 * rrec[97 * i + 64]
            for t in unroll(0, 32):
                blk[128 * i + 32 + t] = a[32 * j + t]
            for t in unroll(0, 20):
                blk[128 * i + 64 + t] = msg[20 * i + t]
            blk[128 * i + 84] = 128
            for t in unroll(85, 126):
                blk[128 * i + t] = 0
            blk[128 * i + 126] = 2
            blk[128 * i + 127] = 160
            sha512(blk + 128 * i, rec + 101 * i, zeros)
            for t in unroll(0, 32):
                rec[101 * i + 64 + t] = s[32 * i + t]
            for t in unroll(0, 4):
                rec[101 * i + 96 + t] = rho[4 * i + t]
            rec[101 * i + 100] = rrec + 97 * i
    out = Array(90 * N)
    sacc = Array(64 * M)
    for j in unroll(0, M):
        for t in unroll(0, 32):
            sacc[64 * j + t] = 0
        if j == 0:
            for t in unroll(0, 32):
                sacc[64 * j + 32 + t] = 0
        else:
            for t in unroll(0, 32):
                sacc[64 * j + 32 + t] = out[90 * (G * j - 1) + 32 + t]
        scalar_l(rec + 101 * (G * j), sacc + 64 * j, out + 90 * (G * j))
        for i in unroll(G * j + 1, G * j + G):
            scalar_l(rec + 101 * i, out + 90 * (i - 1), out + 90 * i)
    krec = Array(34 * M)
    kout = Array(84 * M)
    for j in unroll(0, M):
        for t in unroll(0, 32):
            krec[34 * j + t] = out[90 * (G * (j + 1) - 1) + t]
        krec[34 * j + 32] = arec + 97 * j
        krec[34 * j + 33] = 1
        signer_scalar(krec + 34 * j, kout + 84 * j, 0)
    srec = Array(34)
    sout = Array(84)
    for t in unroll(0, 32):
        srec[t] = out[90 * (N - 1) + 32 + t]
    srec[32] = bpt
    srec[33] = 0
    signer_scalar(srec, sout, 0)
    return
"#;
    let flags = CompilationFlags { replacements: [("N_PLACEHOLDER".to_string(), n.to_string()), ("M_PLACEHOLDER".to_string(), m.to_string()), ("G_PLACEHOLDER".to_string(), g.to_string())].into_iter().collect() };
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program.to_string()), flags);
    let l = modulus_int(&L_25519);
    let mut x = 0x5851f42d4c957f2du64; let mut nb = move || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let rand_scalar = |nb: &mut dyn FnMut() -> u64| -> BigInt { let bytes: Vec<u8> = (0..32).map(|_| (nb() & 255) as u8).collect(); limbs_to_int(&bytes).mod_floor(&l) };
    let to32 = |v: &BigInt| -> [u8; 32] { let mut o = [0u8; 32]; for (i, b) in v.to_bytes_le().1.iter().enumerate() { o[i] = *b; } o };
    let bp = base_point();
    let inv8 = BigInt::from(8u8).modpow(&(&l - BigInt::from(2u8)), &l);
    let cells = |v: &[u8]| -> Vec<F> { v.iter().map(|b| F::from_usize(*b as usize)).collect() };
    let (mut q_c, mut a_c, mut msg_c, mut s_c, mut rho_c) = (vec![], vec![], vec![], vec![], vec![]);
    // native cross-checks: every signature verifies; the batch MSM S·B − Σρ_iR_i − ΣK_jA_j closes
    use lean_vm::ed25519::curve::{NEUTRAL, affine_add};
    use lean_vm::ed25519::gadgets::{P_25519, mod_sub};
    use lean_vm::ed25519::scalar_table::rho_from_cells;
    let neg = |p: &Affine| Affine { x: mod_sub(&[0u8; 32], &p.x, &P_25519), y: p.y };
    let mut msm = NEUTRAL; let mut s_total = BigInt::from(0u8);
    for j in 0..m {
        let a_sk = rand_scalar(&mut nb);
        let a_pt = scalar_mul_bigint(&bp, &a_sk);
        let a_bytes = compress(&a_pt);
        a_c.extend(cells(&a_bytes));
        for gi in 0..g {
            let i = j * g + gi;
            let r = rand_scalar(&mut nb);
            let r_pt = scalar_mul_bigint(&bp, &r);
            let r_bytes = compress(&r_pt);
            let msg: Vec<u8> = (0..20).map(|_| (nb() & 255) as u8).collect();
            let mut pre = vec![]; pre.extend_from_slice(&r_bytes); pre.extend_from_slice(&a_bytes); pre.extend_from_slice(&msg);
            let h = digest_bytes(&sha512_block(&block_words(&pad_single_block(&pre))));
            let c = limbs_to_int(&h).mod_floor(&l);
            let mut s_val = (&r + &c * &a_sk).mod_floor(&l);
            if tamper && i == 0 { s_val = (&s_val + BigInt::from(1u8)).mod_floor(&l); }
            let qp: Affine = scalar_mul_bigint(&bp, &(&r * &inv8).mod_floor(&l));
            q_c.extend(cells(&qp.x)); q_c.extend(cells(&qp.y));
            msg_c.extend(cells(&msg));
            s_c.extend(cells(&to32(&s_val)));
            let rho_cells: [u32; 4] = std::array::from_fn(|_| (nb() % F::ORDER_U64) as u32);
            for c in rho_cells { rho_c.push(F::from_usize(c as usize)); }
            // native checks
            let lhs = scalar_mul_bigint(&bp, &s_val);
            let rhs = affine_add(&r_pt, &scalar_mul_bigint(&a_pt, &c));
            if !tamper { assert_eq!(lhs, rhs, "native signature {i} does not verify"); }
            assert_eq!(scalar_mul_bigint(&qp, &BigInt::from(8u8)), r_pt, "8·Q' != R for signature {i}");
            let rho = BigInt::from(rho_from_cells(&rho_cells));
            msm = affine_add(&msm, &neg(&scalar_mul_bigint(&r_pt, &rho)));
            msm = affine_add(&msm, &neg(&scalar_mul_bigint(&a_pt, &(&rho * &c).mod_floor(&l))));
            s_total = (&s_total + &rho * &s_val).mod_floor(&l);
        }
    }
    msm = affine_add(&msm, &scalar_mul_bigint(&bp, &s_total));
    if !tamper { assert_eq!(msm, NEUTRAL, "native batch MSM does not close"); }
    println!("NATIVE MATH OK (signatures verify, MSM closes)");
    // base point record [Bx | By | 0 | p − Bx] (hinted here; the production driver embeds it in the bytecode)
    let mut bpt_c = vec![]; bpt_c.extend(cells(&bp.x)); bpt_c.extend(cells(&bp.y)); bpt_c.push(F::ZERO);
    { use lean_vm::ed25519::gadgets::{P_25519, mod_sub}; bpt_c.extend(cells(&mod_sub(&[0u8; 32], &bp.x, &P_25519))); }
    let mut hints = Hints::default();
    for (name, v) in [("q", &q_c), ("a", &a_c), ("msg", &msg_c), ("s", &s_c), ("rho", &rho_c), ("bpt", &bpt_c)] { hints.insert(&bytecode, name, arena_vec![ArenaVec::from_slice(v)]); }
    let witness = ExecutionWitness { hints, ..Default::default() };
    (bytecode, witness)
}

fn ed25519_batch_run(m: usize, g: usize, tamper: bool) -> Result<(), String> {
    let (bytecode, witness) = ed25519_batch_setup(m, g, tamper);
    let public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    let time = std::time::Instant::now();
    let proof = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_execution(&bytecode, &public_input, &witness, &default_whir_config(1), false))) {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return Err(format!("prove: {e:?}")),
        Err(_) => return Err("prove panicked (constraints not satisfied)".to_string()),
    };
    println!("batch M={m} G={g} tamper={tamper}: proof {:.3} s", time.elapsed().as_secs_f32());
    println!("{}", proof.metadata.as_ref().unwrap().display());
    verify_execution(&bytecode, &public_input, proof.proof).map(|_| ()).map_err(|e| format!("verify: {e:?}"))
}

/// Native AIR check of every ed25519 table on the batch trace: reports the first violated
/// constraint per table (row, constraint index, row flags) — the prover itself never checks.
fn native_check_ed_tables(bytecode: &Bytecode, witness: &ExecutionWitness) -> Vec<String> {
    use lean_vm::ed25519::*;
    struct Rec { flat: Vec<F>, shift: Vec<F>, idx: usize, failures: Vec<usize> }
    impl AirBuilder for Rec {
        type F = F; type IF = F; type EF = EF;
        fn flat(&self) -> &[F] { &self.flat }
        fn shift(&self) -> &[F] { &self.shift }
        fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures.push(self.idx); } self.idx += 1; }
        fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures.push(self.idx); } self.idx += 1; }
    }
    let public_input = [F::ZERO; PUBLIC_INPUT_LEN];
    let execution_result = try_execute_bytecode(bytecode, &public_input, witness, false).expect("execution");
    let trace = crate::trace_gen::get_execution_trace(bytecode, execution_result, &witness.min_table_log_n_rows);
    let mut report = vec![];
    macro_rules! check {
        ($name:expr, $air:expr, $table:expr, $flags:expr) => {{
            let tr = &trace.traces[&$table];
            let n = tr.columns[0].len(); let n_cols = tr.columns.len();
            let n_shift = $table.n_shift_columns();
            let mut first: Option<String> = None; let mut n_bad = 0;
            for r in 0..n {
                let flat: Vec<F> = (0..n_cols).map(|c| tr.columns[c][r]).collect();
                let rn = if r + 1 < n { r + 1 } else { r };
                let shift: Vec<F> = (0..n_shift).map(|c| tr.columns[c][rn]).collect();
                let mut b = Rec { flat, shift, idx: 0, failures: vec![] };
                $air.eval(&mut b, &ExtraDataForBuses::new(&[], vec![]));
                if !b.failures.is_empty() {
                    n_bad += 1;
                    if first.is_none() {
                        let flags: Vec<String> = $flags.iter().map(|&(nm, c): &(&str, usize)| format!("{nm}={}", tr.columns[c][r].as_canonical_u32())).collect();
                        first = Some(format!("{}: row {r}/{n}: constraints {:?} ({})", $name, &b.failures[..b.failures.len().min(8)], flags.join(" ")));
                    }
                }
            }
            if let Some(f) = first { report.push(format!("{f}; {n_bad} bad rows")); }
        }};
    }
    check!("ed_sig", EdSigTable::<false>, Table::ed_sig(), [("mult", edsig_table::COL_MULT)]);
    check!("ed_decompress", EdDecompressTable::<false>, Table::ed_decompress(), [("mult", decompress_table::COL_MULT), ("sign", decompress_table::COL_SIGN)]);
    check!("sha512", Sha512Table::<false>, Table::sha512(), [("r0", sha512_table::COL_FLAGS), ("r20", sha512_table::COL_FLAGS + 20)]);
    check!("scalar_l", ScalarLTable::<false>, Table::scalar_l(), [("mult", scalar_table::COL_MULT)]);
    check!("signer_scalar", SignerScalarTable::<false>, Table::signer_scalar(), [("mult", signer_scalar_table::COL_MULT), ("flip", signer_scalar_table::COL_FLIP)]);
    check!("ed_add", EdAddTable::<false>, Table::ed_add(), [("active", ed_add_table::COL_ACTIVE), ("start", ed_add_table::COL_START), ("head", ed_add_table::COL_HEAD), ("kb", ed_add_table::COL_KB), ("kr1", ed_add_table::COL_KR1), ("kr2", ed_add_table::COL_KR2), ("kh", ed_add_table::COL_KH), ("j", ed_add_table::COL_J), ("b", ed_add_table::COL_B), ("cnt", ed_add_table::COL_CNT), ("empty", ed_add_table::COL_EMPTY)]);
    // the MSM total: the horner head row's acc_out
    {
        let tr = &trace.traces[&Table::ed_add()];
        for r in 0..tr.columns[0].len() {
            if tr.columns[ed_add_table::COL_KH][r] == F::ONE && tr.columns[ed_add_table::COL_HEAD][r] == F::ONE {
                let x: Vec<u32> = (0..32).map(|i| tr.columns[ed_add_table::COL_X3 + i][r].as_canonical_u32()).collect();
                let y: Vec<u32> = (0..32).map(|i| tr.columns[ed_add_table::COL_Y3 + i][r].as_canonical_u32()).collect();
                report.push(format!("MSM total: x={:?} y={:?} (want x=0, y=1)", &x[..4], &y[..4]));
            }
        }
    }
    report
}

#[test]
fn test_ed25519_batch_native_constraints() {
    let (bytecode, witness) = ed25519_batch_setup(2, 2, false);
    for line in native_check_ed_tables(&bytecode, &witness) { println!("NATIVE {line}"); }
}

/// Phase D: a real leaf from the dataset — sorted by signer, hinted groups, root/ctx/ρ/H_leaf in-circuit,
/// the public input recomputed reader-side from the columns.
fn leaf_dataset(n: usize) -> Vec<crate::ed25519_leaf::SigRow> {
    let path = std::env::var("LEAF_DATASET").unwrap_or_else(|_| format!("{}/.cache/fb-stacks/datasets/sigs-25k-diverse.json", std::env::var("HOME").unwrap()));
    let rows = crate::ed25519_leaf::rows_from_json(&path);
    rows[..n].to_vec()
}
#[test]
fn test_zk_vm_ed25519_leaf() {
    use crate::ed25519_leaf::*;
    let n: usize = std::env::var("LEAF_N").ok().and_then(|v| v.parse().ok()).unwrap_or(16);
    let blob_id: [F; 9] = std::array::from_fn(|i| f(11 * (i + 1)));
    let leaf = build_leaf(&leaf_dataset(n), 3, &blob_id).expect("leaf");
    println!("leaf: {} signatures, {} signers", leaf.n_seg, leaf.n_groups);
    assert_eq!(leaf.public_input, expected_public_input(&leaf.rows, 3, &blob_id), "reader-side H_leaf");
    let time = std::time::Instant::now();
    let proof = prove_leaf(&leaf, &default_whir_config(1)).unwrap();
    println!("leaf proof: {:.3} s", time.elapsed().as_secs_f32());
    println!("{}", proof.metadata.as_ref().unwrap().display());
    verify_leaf(&leaf.public_input, proof.proof).expect("leaf must verify");
}
#[test]
fn test_zk_vm_ed25519_leaf_rejects_tampering() {
    use crate::ed25519_leaf::*;
    let blob_id: [F; 9] = std::array::from_fn(|i| f(11 * (i + 1)));
    let mut rows = leaf_dataset(4);
    // tamper: flip a bit of the digest of the first row (the column changes, the signature no longer matches)
    rows[0].digest[3] ^= 1;
    let leaf = build_leaf(&rows, 3, &blob_id).expect("leaf builds");
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| prove_leaf(&leaf, &default_whir_config(1))));
    let rejected = match res { Ok(Ok(p)) => verify_leaf(&leaf.public_input, p.proof).is_err(), _ => true };
    assert!(rejected, "a leaf with a signature over the wrong digest must not verify");
    // wrong public input (different seg_index) must not verify either
    let leaf2 = build_leaf(&leaf_dataset(4), 3, &blob_id).unwrap();
    let proof = prove_leaf(&leaf2, &default_whir_config(1)).unwrap();
    assert!(verify_leaf(&expected_public_input(&leaf2.rows, 4, &blob_id), proof.proof).is_err(), "wrong seg_index must not verify");
}

/// Every leaf of both 25k datasets builds (all real signatures pass the strict checks); LEAF_SIZE per leaf.
#[test]
#[ignore = "dataset sweep: LEAF_SWEEP=build|prove, ~30 s (build) / minutes (prove)"]
fn test_ed25519_leaf_dataset_sweep() {
    use crate::ed25519_leaf::*;
    let mode = std::env::var("LEAF_SWEEP").unwrap_or_else(|_| "build".to_string());
    let size: usize = std::env::var("LEAF_SIZE").ok().and_then(|v| v.parse().ok()).unwrap_or(1024);
    let home = std::env::var("HOME").unwrap();
    let datasets: Vec<String> = std::env::var("LEAF_DATASETS").map(|v| v.split(',').map(String::from).collect()).unwrap_or_else(|_| vec![format!("{home}/.cache/fb-stacks/datasets/sigs-25k.json"), format!("{home}/.cache/fb-stacks/datasets/sigs-25k-diverse.json")]);
    let blob_id: [F; 9] = std::array::from_fn(|i| f(i + 1));
    for path in datasets {
        let rows = rows_from_json(&path);
        let n_leaves = (rows.len() + size - 1) / size;
        let mut ok = 0; let t0 = std::time::Instant::now();
        for k in 0..n_leaves {
            let chunk = &rows[k * size..((k + 1) * size).min(rows.len())];
            let leaf = build_leaf(chunk, k, &blob_id).unwrap_or_else(|e| panic!("{path} leaf {k}: {e}"));
            assert_eq!(leaf.public_input, expected_public_input(&leaf.rows, k, &blob_id));
            if mode == "prove" {
                let t = std::time::Instant::now();
                let proof = prove_leaf(&leaf, &default_whir_config(1)).unwrap();
                verify_leaf(&leaf.public_input, proof.proof).expect("leaf verifies");
                println!("SWEEP {} leaf {k}: {} sigs, {} signers, proof+verify {:.1} s", path.rsplit('/').next().unwrap(), leaf.n_seg, leaf.n_groups, t.elapsed().as_secs_f32());
            }
            ok += 1;
        }
        println!("SWEEP {}: {ok}/{n_leaves} leaves of {size} {} in {:.1} s", path.rsplit('/').next().unwrap(), if mode == "prove" { "proven and verified" } else { "built" }, t0.elapsed().as_secs_f32());
    }
}

/// Frame-model probe: a 70k-cell local array in main, then callee frames; prints the addresses so a
/// callee frame landing inside the caller's array (frame under-allocation) is visible.
#[test]
fn test_big_frame_probe() {
    // If constant-size arrays are not counted in the frame size, helper's frame lands inside `big`
    // and the runtime loop's writes to big[i] collide with it.
    let program = r#"
def main():
    big = Array(20000)
    y = helper(3)
    assert y == 6
    for i in range(0, 20000):
        big[i] = i
    z = helper(4)
    assert z == 8
    return

def helper(a):
    t = Array(64)
    for i in unroll(0, 64):
        t[i] = a + i
    return t[0] * 2
"#;
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program.to_string()), CompilationFlags::default());
    let witness = ExecutionWitness { hints: Hints::default(), ..Default::default() };
    let res = try_execute_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], &witness, false);
    match &res { Ok(_) => println!("PROBE: frames disjoint (ok)"), Err(e) => println!("PROBE: runner error: {e}") }
    assert!(res.is_ok());
}

#[test]
fn test_zk_vm_ed25519_batch() {
    let m: usize = std::env::var("BATCH_M").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    let g: usize = std::env::var("BATCH_G").ok().and_then(|v| v.parse().ok()).unwrap_or(2);
    ed25519_batch_run(m, g, false).expect("a valid batch must prove and verify");
}

#[test]
fn test_zk_vm_ed25519_batch_rejects_tampered_signature() {
    assert!(ed25519_batch_run(1, 2, true).is_err(), "a tampered signature scalar must not prove");
}

/// Phase A of the ed25519 integration: the driver runs `ed_sig` on a torsion witness Q' and
/// `ed_decompress` on the compressed key A, and asserts P = 8Q' equals the decompressed (A.x, y_can)
/// cell by cell — a signer certificate, proven and verified through the real pipeline (execution
/// bus + memory lookups). Then a small batch in a runtime loop.
#[test]
fn test_zk_vm_ed25519_signer_certificate() {
    use lean_vm::ed25519::curve::{random_points, scalar_mul_small};
    use lean_vm::ed25519::decompress_table::compress;
    let n: usize = std::env::var("ED_CERT_N").ok().and_then(|v| v.parse().ok()).unwrap_or(3); // ED_CERT_N=1024 for a batch anchor
    let program = r#"
n = N_PLACEHOLDER
def main():
    q = Array(64 * n)
    hint_witness("q", q)
    a = Array(32 * n)
    hint_witness("a", a)
    out = Array(97 * n)
    dec = Array(97 * n)
    for i in range(0, n):
        ed_sig(q + 64 * i, out + 97 * i, 0)
        ed_decompress(a + 32 * i, dec + 97 * i, 0)
        for j in unroll(0, 64):
            assert out[97 * i + j] == dec[97 * i + j]
        for j in unroll(65, 97):
            assert out[97 * i + j] == dec[97 * i + j]
    return
"#;
    let flags = CompilationFlags { replacements: [("N_PLACEHOLDER".to_string(), n.to_string())].into_iter().collect() };
    let bytecode = compile_program_with_flags(&ProgramSource::Raw(program.to_string()), flags);
    let qs = random_points(n, 77);
    let mut q_cells = vec![]; let mut a_cells = vec![];
    for q in &qs {
        for b in q.x.iter().chain(q.y.iter()) { q_cells.push(F::from_usize(*b as usize)); }
        let a = compress(&scalar_mul_small(q, 8));
        for b in a.iter() { a_cells.push(F::from_usize(*b as usize)); }
    }
    let mut hints = Hints::default();
    hints.insert(&bytecode, "q", arena_vec![ArenaVec::from_slice(&q_cells)]);
    hints.insert(&bytecode, "a", arena_vec![ArenaVec::from_slice(&a_cells)]);
    let witness = ExecutionWitness { hints, ..Default::default() };
    test_zk_vm_helper_with_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], witness);
}
