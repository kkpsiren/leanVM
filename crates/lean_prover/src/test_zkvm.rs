use std::collections::BTreeMap;

use crate::{default_whir_config, prove_execution::prove_execution, verify_execution::verify_execution};
use backend::*;
use lean_compiler::*;
use lean_vm::*;
use rand::{RngExt, SeedableRng, rngs::StdRng};

const N: usize = 11;
const M: usize = 3;

const ALL_PRECOMPILES_PROGRAM: &str = r#"
DIM = 3
N = 11
M = 3
DIGEST_LEN = 4
HALF_DIGEST_LEN = 2
SCRATCH_SIZE = 8192
LOOP_ITERS = LOOP_ITERS_PLACEHOLDER

def main():
    scratch = Array(SCRATCH_SIZE)
    hint_witness("scratch", scratch)
    poseidon8_compress_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, scratch + 6 * DIGEST_LEN)

    # poseidon8_compress_quarter: only first 2 FE constrained
    full_out = scratch + 6 * DIGEST_LEN
    half_out = scratch + 80
    poseidon8_compress_quarter(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, half_out)
    for i in unroll(0, HALF_DIGEST_LEN):
        assert full_out[i] == half_out[i]

    # poseidon8_compress_half_hardcoded_left: the 2-element prefix lives at a compile-time
    # constant memory offset. Public input is the only region with such addresses, so we
    # place the prefix at public_input[0..2] (= memory address 0..2) and pass offset 0.
    hardcoded_left = scratch + 1496
    hardcoded_full_out = scratch + 1504
    poseidon8_compress_half_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_full_out,
        0
    )

    # Same, but only first 2 FE of the output are constrained.
    hardcoded_half_out = scratch + 1512
    poseidon8_compress_quarter_hardcoded_left(
        hardcoded_left,
        scratch + 5 * DIGEST_LEN,
        hardcoded_half_out,
        0
    )
    for i in unroll(0, HALF_DIGEST_LEN):
        assert hardcoded_full_out[i] == hardcoded_half_out[i]

    # poseidon8_permute: full 8-element permutation (no feed-forward), written in natural order:
    #   m[res .. res + 8] = poseidon(left || right)
    permute_out = scratch + 1600
    poseidon8_permute(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_out)

    # poseidon8_permute_half: same permutation, but only the low 4 elements are written/constrained.
    permute_half_out = scratch + 1620
    poseidon8_permute_half(scratch + 4 * DIGEST_LEN, scratch + 5 * DIGEST_LEN, permute_half_out)
    for i in unroll(0, DIGEST_LEN):
        assert permute_half_out[i] == permute_out[i]

    # poseidon8_permute_half_hardcoded_left: permutation (low 4) with a hardcoded 2-element left prefix.
    # Uses the same input as the hardcoded compression above, so it equals the permutation of that input.
    permute_hardcoded_out = scratch + 1640
    poseidon8_permute_half_hardcoded_left(hardcoded_left, scratch + 5 * DIGEST_LEN, permute_hardcoded_out, 0)

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

    c_buf = Array(LOOP_ITERS + 1)
    c_buf[0] = 0
    for i in range(0, LOOP_ITERS):
        c_buf[i + 1] = c_buf[i] + 1
    assert c_buf[LOOP_ITERS] == LOOP_ITERS

    return
"#;

fn all_precompiles_flags(loop_iters: usize) -> CompilationFlags {
    CompilationFlags {
        replacements: BTreeMap::from([("LOOP_ITERS_PLACEHOLDER".to_string(), loop_iters.to_string())]),
    }
}

fn all_precompiles_witness(bytecode: &Bytecode) -> ([F; PUBLIC_INPUT_LEN], ExecutionWitness) {
    let mut rng = StdRng::seed_from_u64(0);
    let mut scratch = F::zero_vec(8192);

    // Poseidon test data — width 8 / digest 4 / half-digest 2 for Goldilocks.
    // DSL uses `scratch + 4*DIGEST_LEN..6*DIGEST_LEN` (positions 16..24) for the input
    // and `scratch + 6*DIGEST_LEN..7*DIGEST_LEN` (positions 24..28) for the output.
    let poseidon_8_compress_input: [F; 8] = rng.random();
    scratch[16..24].copy_from_slice(&poseidon_8_compress_input);
    let poseidon_output = poseidon8_compress(poseidon_8_compress_input);
    scratch[24..28].copy_from_slice(&poseidon_output);
    // poseidon8_compress_half output at offset 80: first 2 = hash, last 2 = arbitrary pre-existing data
    scratch[80..82].copy_from_slice(&poseidon_output[..2]);
    scratch[82..84].copy_from_slice(&[F::from_usize(111), F::from_usize(222)]);

    // poseidon8_compress_hardcoded_left: prefix lives at public_input[0..2] (compile-time
    // constant offset 0), data at scratch[1496..1498], expected output at scratch[1504..1508].
    let hardcoded_prefix: [F; 2] = rng.random();
    let hardcoded_data: [F; 2] = rng.random();
    scratch[1496..1498].copy_from_slice(&hardcoded_data);
    let mut hardcoded_input = [F::ZERO; 8];
    hardcoded_input[..2].copy_from_slice(&hardcoded_prefix);
    hardcoded_input[2..4].copy_from_slice(&hardcoded_data);
    hardcoded_input[4..8].copy_from_slice(&poseidon_8_compress_input[4..8]);
    let hardcoded_output = poseidon8_compress(hardcoded_input);
    scratch[1504..1508].copy_from_slice(&hardcoded_output);
    // half output: first 2 = hash, last 2 = arbitrary pre-existing data
    scratch[1512..1514].copy_from_slice(&hardcoded_output[..2]);
    scratch[1514..1516].copy_from_slice(&[F::from_usize(555), F::from_usize(666)]);

    // poseidon8_permute output at 1600..1608: raw permutation result.
    let permute_output = poseidon8_permute(poseidon_8_compress_input);
    scratch[1600..1608].copy_from_slice(&permute_output);

    // poseidon8_permute_half output at 1620..1624: low 4 of the same permutation.
    scratch[1620..1624].copy_from_slice(&permute_output[..4]);

    // poseidon8_permute_half_hardcoded_left output at 1640..1644: low 4 of the permutation of the
    // hardcoded-left input (same input as the hardcoded compression above).
    let permute_hardcoded_output = poseidon8_permute(hardcoded_input);
    scratch[1640..1644].copy_from_slice(&permute_hardcoded_output[..4]);

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
    public_input[..2].copy_from_slice(&hardcoded_prefix);

    let mut hints = Hints::default();
    hints.insert(bytecode, "scratch", arena_vec![ArenaVec::from_slice(&scratch)]);
    let witness = ExecutionWitness {
        hints,
        ..Default::default()
    };
    (public_input, witness)
}

#[test]
fn test_zk_vm_all_precompiles() {
    let bytecode = compile_program_with_flags(
        &ProgramSource::Raw(ALL_PRECOMPILES_PROGRAM.to_string()),
        all_precompiles_flags(100),
    );
    let (public_input, witness) = all_precompiles_witness(&bytecode);
    test_zk_vm_helper_with_bytecode(&bytecode, &public_input, witness);
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
