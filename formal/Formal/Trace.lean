import Formal.ExecTable
import Formal.Bus
import Formal.Wrapping

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

/-! ## Extracting the consecutive-pair constraints from the committed table

`trace_sound` above assumed the per-consecutive-pair form of the AIR constraints
(`hair`). The faithful statement is instead that the constraint holds on **every
committed row** `r` with the wrapping-pair shift `wrapNext r` — this is what the
batched zerocheck establishes (the constraint MLE vanishes on the whole boolean
hypercube). The lemma below derives the consecutive form from the table form: on
an interior row `i.castSucc`, `wrapNext` is exactly the successor `i.succ`. The
last row's self-pairing carries no transition, so it is correctly absent from the
`Fin n` family of consecutive pairs. -/

variable {n : ℕ}

/-- The table-level AIR constraint (holding on every row, with `wrapNext`) yields
the consecutive-pair constraints `(rows i, rows (i+1))` for every `i : Fin n`. -/
theorem execConstraints_consecutive (rows : Fin (n + 1) → ExecRow F)
    (hairAll : ∀ r, ExecConstraints (rows r) (rows (wrapNext r))) :
    ∀ i : Fin n, ExecConstraints (rows i.castSucc) (rows i.succ) := by
  intro i
  have h := hairAll i.castSucc
  rwa [wrapNext_castSucc] at h

/-- **Trace soundness from the committed table.** Same as `trace_sound`, but the
AIR hypothesis is the faithful table-level form `hairAll` (constraint on every
row with the wrapping-pair shift); the consecutive-pair structure is *derived*,
not assumed. -/
theorem trace_sound_table (hchar : (2 : F) ≠ 0) (m : F → F) (bytecode : F → Instr F)
    (rows : Fin (n + 1) → ExecRow F) (initpc initfp finalpc finalfp : F)
    (hwf  : ∀ i, (rows i).instr = encodeInstr (bytecode (rows i).pc))
    (hmem : ∀ i, MemBinding m (rows i))
    (hairAll : ∀ r, ExecConstraints (rows r) (rows (wrapNext r)))
    (hstart : (rows 0).pc = initpc ∧ (rows 0).fp = initfp)
    (hend   : (rows (Fin.last n)).pc = finalpc ∧ (rows (Fin.last n)).fp = finalfp) :
    ∃ exec : Fin (n + 1) → State F,
      exec 0 = ⟨initpc, initfp⟩ ∧
      exec (Fin.last n) = ⟨finalpc, finalfp⟩ ∧
      ∀ i : Fin n,
        (bytecode (exec i.castSucc).pc).NextState m (exec i.castSucc) (exec i.succ) :=
  trace_sound hchar m bytecode n rows initpc initfp finalpc finalfp hwf hmem
    (execConstraints_consecutive rows hairAll) hstart hend

/-- **End-to-end EXECUTION-table trace soundness.** With the committed table
satisfying the AIR on every row (wrapping shift), the memory and bytecode buses
balanced (the logup-GKR output), each row's pulls placed on those buses, and the
boundary registers fixed, there exists a valid execution trace from the initial
to the final state — each step a `NextState` transition for the **actual bytecode
instruction**. No `MemBinding`, bytecode-binding, or consecutive-pair hypotheses
remain free: they are all discharged here. -/
theorem trace_sound_table_of_bus (hchar : (2 : F) ≠ 0) (m : F → F)
    (bytecode : F → Instr F) (rows : Fin (n + 1) → ExecRow F)
    (initpc initfp finalpc finalfp : F)
    {memBus : Bus (F × F)} {bcBus : Bus (InstrCols F × F)}
    (hmemBal : memBus.Balanced) (hmemPush : IsMemoryPush m memBus.pushes)
    (hbcBal : bcBus.Balanced) (hbcPush : IsBytecodePush bytecode bcBus.pushes)
    (hpullMem : ∀ r : Fin (n + 1),
      ((rows r).addrA, (rows r).valA) ∈ memBus.pulls ∧
      ((rows r).addrB, (rows r).valB) ∈ memBus.pulls ∧
      ((rows r).addrC, (rows r).valC) ∈ memBus.pulls)
    (hpullBc : ∀ r : Fin (n + 1), ((rows r).instr, (rows r).pc) ∈ bcBus.pulls)
    (hairAll : ∀ r, ExecConstraints (rows r) (rows (wrapNext r)))
    (hstart : (rows 0).pc = initpc ∧ (rows 0).fp = initfp)
    (hend   : (rows (Fin.last n)).pc = finalpc ∧ (rows (Fin.last n)).fp = finalfp) :
    ∃ exec : Fin (n + 1) → State F,
      exec 0 = ⟨initpc, initfp⟩ ∧
      exec (Fin.last n) = ⟨finalpc, finalfp⟩ ∧
      ∀ i : Fin n,
        (bytecode (exec i.castSucc).pc).NextState m (exec i.castSucc) (exec i.succ) := by
  have hwf : ∀ r, (rows r).instr = encodeInstr (bytecode (rows r).pc) := fun r =>
    bytecode_lookup_sound bytecode hbcBal hbcPush (hpullBc r)
  have hmem : ∀ r, MemBinding m (rows r) := fun r =>
    memBinding_of_bus m (rows r) hmemBal hmemPush
      (hpullMem r).1 (hpullMem r).2.1 (hpullMem r).2.2
  exact trace_sound_table hchar m bytecode rows initpc initfp finalpc finalfp
    hwf hmem hairAll hstart hend

end LeanVM
