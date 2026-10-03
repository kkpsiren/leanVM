# AGENTS.md

This repo is leanVM. It is a minimal hash-based zkVM.

The README is the upstream leanVM readme. Recent history follows the upstream authors. Do not describe this tree as an Orb app.

## Code

- `src/` holds the Rust binary and library entry points.
- `crates/lean_vm` holds the VM.
- `crates/lean_compiler` holds the compiler. `crates/lean_compiler/zkDSL.md` is the zkDSL note.
- `crates/lean_prover` holds the prover. `crates/lean_prover/python-verifier/verifier.py` is the Python verifier.
- `crates/rec_aggregation` holds recursive aggregation.
- `crates/sub_protocols` holds sub-protocols.
- `crates/xmss` holds XMSS. `crates/xmss/xmss.md` is its note.
- `crates/whir` holds WHIR.
- `crates/backend` holds the field, AIR, and proof backend crates.
- `tests/` holds Rust tests.
- `misc/minimal_zkVM.tex` is the spec source.

The workspace manifest is `Cargo.toml`. The package name there is `lean-multisig`.
