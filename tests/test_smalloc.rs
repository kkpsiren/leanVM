use lean_multisig::{aggregate_single_msg_signatures, setup_prover, verify_single_message_aggregate};
use smalloc::Smalloc;
use xmss::signers_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};

#[global_allocator]
static ALLOC: Smalloc = Smalloc::new();

#[test]
fn test_aggregation_with_smalloc() {
    setup_prover();

    let log_inv_rate = 2;
    let message = message_for_benchmark();
    let slot: u32 = BENCHMARK_SLOT;
    let signatures = get_benchmark_signatures();
    let raw_xmss = signatures[0..6].to_vec();

    let aggregated = aggregate_single_msg_signatures(&[], raw_xmss, message, slot, log_inv_rate).unwrap();

    verify_single_message_aggregate(&aggregated).unwrap();
}
