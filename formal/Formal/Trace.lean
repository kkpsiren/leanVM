import Formal.ExecTable

/-!
# Trace-level soundness of the EXECUTION table (core instructions)

This file lifts the single-step soundness lemma `exec_sound`
(Formal/ExecTable.lean) to a whole **execution trace**, mirroring the shape of
the main theorems of both ancestor works:

* Stone (Avigad et al., *A Verified Algebraic Representation of Cairo Program
  Execution*, CPP 2022): "there exists an execution trace … that starts at the
  start state, runs for `T` steps, and ends at the end state, and each
  successive state follows the previous one according to the machine semantics."
* S-two (*Formal verification of the S-two AIR*): the `trace_sound` theorem
  concludes `∃ exec : Fin (n+1) → RegisterState, exec 0 = initial ∧
  exec last = final ∧ ∀ i, NextState mem (exec i) (exec i.succ)`.

The leanVM analogue below has exactly that conclusion. Two design points carried
over from the papers:

* **Relational ("agrees") semantics.** `Instr.NextState` is a `Prop` on the
  successor state, *not* a function computing it. This is Stone's `agrees`
  pattern: the AIR proves the committed next row *satisfies* the semantics,
  without claiming the next state is uniquely determined. (For JUMP with a
  non-boolean condition the semantics would be nondeterministic; soundness does
  not need determinism — only that the committed step is one the semantics
  allows. Decoding *is* in fact deterministic here, but, as Stone observes,
  uniqueness is needed only for downstream program proofs, not for soundness.)

* **The trace is ordered in the table.** Row `i+1` is the AIR `next` of row `i`,
  so the per-row constraints directly chain the register states — leanVM needs
  no separate "chain lookup" (contrast S-two, whose opcode rows are unordered
  and chained by a multiset-equality lookup).

## Still hypotheses at this stage (the next phases discharge them)

* `hwf` — each row's instruction columns are the (well-formed) bytecode
  instruction at that row's `pc`. Provided by the bytecode bus + the
  well-formed-bytecode assumption.
* `hmem` — each row's memory bindings. Provided by the verified bus-balance /
  logup lemma (next phase), which also constructs the memory function `m`
  itself (cf. Stone §Memory: `def mem … ; mem extends m* ; mem (a i) = v i`).
* `hstart`/`hend` — the boundary register values; in the full protocol these
  come from the boundary `pc` opening claims and the public input.
-/

namespace LeanVM

variable {F : Type*} [Field F]

/-- **Trace-level soundness (core instructions).**

Given a length-`n` run recorded as rows `rows 0, …, rows n` such that every
consecutive pair satisfies the EXECUTION-table AIR constraints, every row's
instruction columns are the well-formed bytecode instruction at its `pc`, and
every row's memory bindings hold, there exists an execution trace of register
states from `(initpc, initfp)` to `(finalpc, finalfp)` in which each step is a
valid leanVM transition (`Instr.NextState`) for the instruction fetched at that
step's `pc`.

This is the leanVM counterpart of Stone's correctness theorem and S-two's
`trace_sound`, restricted to the four core instructions and with the
memory/bytecode/boundary facts still taken as hypotheses. -/
theorem trace_sound (hchar : (2 : F) ≠ 0) (m : F → F) (bytecode : F → Instr F)
    (n : ℕ) (rows : Fin (n + 1) → ExecRow F)
    (initpc initfp finalpc finalfp : F)
    (hwf  : ∀ i, (rows i).instr = encodeInstr (bytecode (rows i).pc))
    (hmem : ∀ i, MemBinding m (rows i))
    (hair : ∀ i : Fin n, ExecConstraints (rows i.castSucc) (rows i.succ))
    (hstart : (rows 0).pc = initpc ∧ (rows 0).fp = initfp)
    (hend   : (rows (Fin.last n)).pc = finalpc ∧ (rows (Fin.last n)).fp = finalfp) :
    ∃ exec : Fin (n + 1) → State F,
      exec 0 = ⟨initpc, initfp⟩ ∧
      exec (Fin.last n) = ⟨finalpc, finalfp⟩ ∧
      ∀ i : Fin n,
        (bytecode (exec i.castSucc).pc).NextState m (exec i.castSucc) (exec i.succ) := by
  refine ⟨fun i => ⟨(rows i).pc, (rows i).fp⟩, ?_, ?_, ?_⟩
  · simp only [hstart.1, hstart.2]
  · simp only [hend.1, hend.2]
  · intro i
    exact exec_sound hchar m (bytecode (rows i.castSucc).pc)
      (rows i.castSucc) (rows i.succ) (hwf _) (hmem _) (hair i)

end LeanVM
