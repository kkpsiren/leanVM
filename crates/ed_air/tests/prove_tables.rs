//! Measure the standalone tables through the shared harness.
//!   TABLE=edsig LOG_N_ROWS=14 RATE=1 cargo test --release -p ed_air --test prove_tables -- test_prove_table --exact --nocapture
use ed_air::harness::prove_verify;
fn env(name: &str, default: &str) -> String { std::env::var(name).unwrap_or(default.to_string()) }

#[test]
fn test_prove_table() {
    let log_n_rows: usize = env("LOG_N_ROWS", "10").parse().unwrap();
    let rate: usize = env("RATE", "1").parse().unwrap();
    let n_rows = 1 << log_n_rows;
    match env("TABLE", "edsig").as_str() {
        "edsig" => {
            let qs = ed_air::edadd::random_points(n_rows - 1, 9);
            let (cols, _) = ed_air::edsig::generate_trace(&qs, n_rows);
            assert_eq!(ed_air::edsig::check_trace(&cols), None);
            prove_verify(ed_air::edsig::EdSigAir, cols, rate, "edsig");
        }
        "scalar" => {
            let (cols, _) = ed_air::scalar::generate_trace(&ed_air::scalar::random_inputs(n_rows - 1, 5), n_rows);
            assert_eq!(ed_air::scalar::check_trace(&cols), None);
            prove_verify(ed_air::scalar::ScalarAir, cols, rate, "scalar");
        }
        other => panic!("unknown TABLE {other}"),
    }
}
