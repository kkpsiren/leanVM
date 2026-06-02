use clap::Parser;
use rec_aggregation::benchmark::{AggregationTopology, biggest_leaf, run_aggregation_benchmark};

// Allocator: smalloc (crate `smmalloc`) — a simple, fast allocator that serves allocations
// from a large, sparsely-used virtual reservation, reusing freed slots in place. Replaces
// the former `zk-alloc` bump arena, which was fast but fragile: any allocation outliving a
// phase, or a pointer retained across `begin_phase`'s slab reset (e.g. from a background
// thread, tracing, or a stray clone), silently corrupted memory. smalloc is stable (real
// per-slot free, no phase ceremony) while keeping the page-reuse that made the arena fast.
// The `standard-alloc` feature selects the plain system allocator for comparison.
#[cfg(not(feature = "standard-alloc"))]
#[global_allocator]
static ALLOC: smalloc::Smalloc = smalloc::Smalloc::new();

#[derive(Parser)]
enum Cli {
    #[command(about = "Aggregate XMSS")]
    Xmss {
        #[arg(long)]
        n_signatures: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "1", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
        #[arg(long, default_value = "1", help = "Number of measured runs per node (after warmup)")]
        repeat: usize,
    },
    #[command(about = "Run n->1 recursion")]
    Recursion {
        #[arg(long, default_value = "2", help = "Number of recursive proofs to aggregate")]
        n: usize,
        #[arg(long, help = "log(1/rate) in WHIR", default_value = "2", short = 'r')]
        log_inv_rate: usize,
        #[arg(long, help = "Enable tracing")]
        tracing: bool,
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
        #[arg(long, default_value = "1", help = "Number of measured runs per node (after warmup)")]
        repeat: usize,
    },
    #[command(about = "Run a fancy aggregation topology")]
    FancyAggregation {
        #[arg(
            long,
            help = "Print BenchmarkReport as JSON on stdout (one line per run); suppresses live output"
        )]
        json: bool,
        #[arg(long, default_value = "1", help = "Number of measured runs per node (after warmup)")]
        repeat: usize,
    },
}

fn run_with_warmup(topology: &AggregationTopology, tracing: bool, json: bool, repeat: usize) {
    let warmup = biggest_leaf(topology).unwrap();
    eprint!("warming up... ");
    let _ = run_aggregation_benchmark(&warmup, false, true, 1);
    eprintln!(
        "used {:.2} GiB",
        system_info::peak_rss_bytes() as f64 / (1u64 << 30) as f64
    );
    let report = run_aggregation_benchmark(topology, tracing && !json, json, repeat);
    if json {
        println!("{}", serde_json::to_string(&report).unwrap());
    }
}

#[allow(clippy::too_many_lines)]
fn main() {
    // Disable Transparent Huge Pages for this process so the allocator's large arenas stay
    // on 4 KB pages — avoids a strided-access cache-set collapse in the prover. Before any work.
    lean_multisig::tune_allocator();

    let cli = Cli::parse();

    match cli {
        Cli::Xmss {
            n_signatures,
            log_inv_rate,
            tracing,
            json,
            repeat,
        } => {
            let topology = AggregationTopology {
                raw_xmss: n_signatures,
                children: vec![],
                log_inv_rate,
                overlap: 0,
            };
            run_with_warmup(&topology, tracing, json, repeat);
        }
        Cli::Recursion {
            n,
            log_inv_rate,
            tracing,
            json,
            repeat,
        } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![
                    AggregationTopology {
                        raw_xmss: 775,
                        children: vec![],
                        log_inv_rate,
                        overlap: 0,
                    };
                    n
                ],
                log_inv_rate,
                overlap: 0,
            };
            run_with_warmup(&topology, tracing, json, repeat);
        }
        Cli::FancyAggregation { json, repeat } => {
            let topology = AggregationTopology {
                raw_xmss: 0,
                children: vec![AggregationTopology {
                    raw_xmss: 10,
                    children: vec![
                        AggregationTopology {
                            raw_xmss: 25,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 0,
                                    children: vec![
                                        AggregationTopology {
                                            raw_xmss: 1550,
                                            children: vec![],
                                            log_inv_rate: 1,
                                            overlap: 0,
                                        },
                                        AggregationTopology {
                                            raw_xmss: 508,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                    ],
                                    log_inv_rate: 2,
                                    overlap: 10,
                                },
                                AggregationTopology {
                                    raw_xmss: 0,
                                    children: vec![
                                        AggregationTopology {
                                            raw_xmss: 1550,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                        AggregationTopology {
                                            raw_xmss: 508,
                                            children: vec![],
                                            log_inv_rate: 2,
                                            overlap: 0,
                                        },
                                    ],
                                    log_inv_rate: 2,
                                    overlap: 10,
                                },
                            ],
                            log_inv_rate: 1,
                            overlap: 5,
                        },
                        AggregationTopology {
                            raw_xmss: 0,
                            children: vec![
                                AggregationTopology {
                                    raw_xmss: 775,
                                    children: vec![],
                                    log_inv_rate: 2,
                                    overlap: 0,
                                };
                                2
                            ],
                            log_inv_rate: 2,
                            overlap: 5,
                        },
                    ],
                    log_inv_rate: 2,
                    overlap: 2,
                }],
                log_inv_rate: 4,
                overlap: 0,
            };
            run_with_warmup(&topology, false, json, repeat);
        }
    }
}
