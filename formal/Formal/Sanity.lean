import Formal.Bus
import Formal.Complete

/-!
# Non-vacuity sanity checks

A soundness theorem whose hypotheses are unsatisfiable is vacuously true and
proves nothing. These `example`s confirm — machine-checked on every build — that
the premises of the main theorems are jointly satisfiable, so the theorems have
real content. (They complement `exec_complete`, which already constructs a
satisfying instance for the EXECUTION-table constraints, and `isMemoryPush_image`
/ `isBytecodePush_image`, which witness the bus push-structure predicates.)
-/

namespace LeanVM

variable {F : Type*} [Field F]

/-- The premises of `mem_lookup_sound` are satisfiable: a balanced bus that
pushes and pulls a single genuine memory pair `(a, m a)`. -/
example (m : F → F) (a : F) :
    ∃ b : Bus (F × F), b.Balanced ∧ IsMemoryPush m b.pushes ∧ (a, m a) ∈ b.pulls :=
  ⟨⟨{(a, m a)}, {(a, m a)}⟩, rfl,
    fun p hp => by rw [Multiset.mem_singleton] at hp; subst hp; rfl,
    Multiset.mem_singleton.mpr rfl⟩

/-- The premises of `bytecode_lookup_sound` are satisfiable. -/
example (bc : F → Instr F) (pc : F) :
    ∃ b : Bus (InstrCols F × F), b.Balanced ∧ IsBytecodePush bc b.pushes ∧
      (encodeInstr (bc pc), pc) ∈ b.pulls :=
  ⟨⟨{(encodeInstr (bc pc), pc)}, {(encodeInstr (bc pc), pc)}⟩, rfl,
    fun p hp => by rw [Multiset.mem_singleton] at hp; subst hp; rfl,
    Multiset.mem_singleton.mpr rfl⟩

/-- The premises of `exec_sound` are satisfiable for *every* instruction and
valid step — via the honest assignment of `Formal/Complete.lean`. Hence
`exec_sound`, and the trace theorems built on it, are not vacuous. -/
example (m : F → F) (I : Instr F) (s t : State F) (hstep : I.NextState m s t) :
    ∃ r n : ExecRow F,
      r.instr = encodeInstr I ∧ MemBinding m r ∧ ExecConstraints r n :=
  ⟨mkRow m s I, mkNext I t,
    (exec_complete m I s t hstep).2.2.2.2.1,
    (exec_complete m I s t hstep).2.2.2.2.2.1,
    (exec_complete m I s t hstep).2.2.2.2.2.2⟩

end LeanVM
