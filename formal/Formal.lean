import Formal.Isa
import Formal.Wrapping
import Formal.ExecTable
import Formal.Complete
import Formal.Bus
import Formal.Logup
import Formal.ExtensionTable
import Formal.ExtensionLen
import Formal.Trace
import Formal.Sanity

/-!
# Formal verification of the leanVM AIR (core ISA)

A Lean 4 + Mathlib formalization of the soundness of the minimal zkVM's algebraic
intermediate representation (`misc/minimal_zkVM.tex`), applying the methodology of
StarkWare/CMU's S-two and Stone proofs: model the VM semantics over an abstract
field, model the AIR constraints, and prove that constraint satisfaction implies
the existence of a valid execution — leaving the cryptographic layer (PCS,
Fiat–Shamir, the probabilistic logup reduction) as the trust boundary.

Scope: the four **core instructions** `ADD`, `MUL`, `DEREF`, `JUMP`. Precompiles
are partial — the EXTENSION table's accumulation is done; POSEIDON is future work.

## Modules

* `Isa`            — VM semantics: operands, `Instr`, `Instr.NextState` (golden spec).
* `Wrapping`       — the `next`-row shift `wrapNext` (last row self-paired).
* `ExecTable`      — EXECUTION table columns, `encodeInstr`, `ExecConstraints`,
                     and `exec_sound` (constraints ⟹ semantics).
* `Complete`       — `exec_complete` (semantics ⟹ constraints satisfiable).
* `Bus`            — the bus, balance, and the memory / bytecode lookups; `exec_sound_of_bus`.
* `Logup`          — `logup_vanishing`: the deterministic core of "logup ⟹ balance".
* `ExtensionTable` — EXTENSION-table accumulation: `ext_add/dot/eq_sound`.
* `ExtensionLen`   — `len_bound` (`§lem:len-bound`) via the wrapping pair.
* `Trace`          — trace-level soundness: `trace_sound`, `trace_sound_table`,
                     and the end-to-end `trace_sound_table_of_bus`.
* `Sanity`         — machine-checked non-vacuity of the main premises.

## Top-level result

`trace_sound_table_of_bus` (Trace): given a committed EXECUTION table whose AIR
constraints hold on every row (with the wrapping shift), balanced memory and
bytecode buses carrying each row's pulls, and the boundary registers, there
exists a valid execution trace from the initial to the final state, each step a
`NextState` transition for the actual bytecode instruction. No `MemBinding`,
bytecode-binding, or per-pair hypotheses remain free.

## Trust boundary (assumed, as in S-two / Stone)

The committed columns satisfy the AIR on the whole boolean hypercube (the
zerocheck / sumcheck / WHIR PCS); the buses are balanced (the logup-GKR output —
`logup_vanishing` is its deterministic core, with the rational-identity
cross-multiplication, the Schwartz–Zippel random-point step, and the fingerprint
injectivity remaining); field primality and the extension-field structure; and
the boundary `pc`/`fp` openings. Every theorem above is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only) with no `sorry`.
-/
