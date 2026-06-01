//! TEMPORARY model validation driver.

use compiler_fuzzer::field_util::zero_public_input;
use compiler_fuzzer::harness::{CompileOutcome, RunOutcome, compile_source, run};
use compiler_fuzzer::model::{CheckedProgram, Computation, Gadget, GadgetKind, Op, Operand, Step};
use compiler_fuzzer::rng::Rng;

fn comp2() -> Computation {
    // value = in0 + in1
    Computation {
        n_inputs: 2,
        steps: vec![Step {
            op: Op::Add,
            a: Operand::Input(0),
            b: Operand::Input(1),
        }],
    }
}

fn main() {
    let gadgets = vec![
        Gadget {
            id: 0,
            kind: GadgetKind::EqBound,
            comp: comp2(),
        },
        Gadget {
            id: 1,
            kind: GadgetKind::EqConst { c: 12345 },
            comp: comp2(),
        },
        Gadget {
            id: 2,
            kind: GadgetKind::Ne,
            comp: comp2(),
        },
        Gadget {
            id: 3,
            kind: GadgetKind::Bool,
            comp: Computation::identity(1),
        },
        Gadget {
            id: 4,
            kind: GadgetKind::RangeLt { bound: 1000 },
            comp: Computation::identity(1),
        },
        Gadget {
            id: 5,
            kind: GadgetKind::RangeLe { bound: 1000 },
            comp: Computation::identity(1),
        },
    ];
    let prog = CheckedProgram::new(gadgets);
    let source = prog.emit_source();
    println!("==== SOURCE ====\n{source}\n================");

    let bc = match compile_source(&source) {
        CompileOutcome::Ok(bc) => bc,
        other => {
            println!("COMPILE FAILED: {other:?}");
            return;
        }
    };

    let mut rng = Rng::new(42);
    let honest = prog.honest_buffers(&mut rng);
    let input = zero_public_input();

    match run(&bc, &input, &CheckedProgram::witness(&honest)) {
        RunOutcome::Ok(_) => println!("honest run: OK (expected)"),
        other => println!("honest run: UNEXPECTED {other:?}"),
    }

    for i in 0..prog.gadgets.len() {
        let bufs = prog.violating_buffers(&honest, i);
        let out = run(&bc, &input, &CheckedProgram::witness(&bufs));
        let g = &prog.gadgets[i];
        match out {
            RunOutcome::Ok(_) => println!("  gadget {i} [{}] violation: ACCEPTED -> DROPPED CHECK?!", g.label()),
            RunOutcome::Error(e) => {
                let cls = compiler_fuzzer::harness::FailureClass::of(&e);
                let ok = cls.consistent_with(g.check_kind());
                println!(
                    "  gadget {i} [{}] violation: rejected ({e:?}) consistent={ok}",
                    g.label()
                );
            }
            RunOutcome::Panicked(p) => println!("  gadget {i} [{}] violation: VM PANIC {}", g.label(), p.message),
        }
    }
}
