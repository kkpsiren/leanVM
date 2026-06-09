import Formal.ExecTable
import Mathlib.Data.Multiset.Basic

/-!
# The bus, and the memory / bytecode lookups

This file models the leanVM **bus** (`misc/minimal_zkVM.tex`, §"One bus to
interact between tables") and proves that, on a **balanced** bus, the memory and
bytecode lookups are sound: every memory pull `(addr, value)` satisfies
`value = m[addr]`, and every bytecode pull `(instr, pc)` satisfies
`instr = bytecode[pc]`. Composed with `exec_sound`, this **discharges the two
hypotheses** (`MemBinding` and the bytecode binding) that the per-step soundness
proof previously assumed.

## What "balanced" means and the logup boundary (inspired by S-two)

Tables `Push`/`Pull` tuples on a global channel; the bus is *balanced* when every
tuple is pulled exactly as many times as it is pushed. We model this directly as
**equality of the push and pull multisets** (`Bus.Balanced`). Equivalently
(`Bus.balanced_iff_count`), every tuple's push-count equals its pull-count — the
tex's condition `∑_{k : σ_k = σ} m_k = 0` (pushes `+`, pulls `−`), and the
multiset-`count` form of S-two's logup conclusion `count z a = μ b m z`.

The leanVM protocol *establishes* balance via the logup-GKR rational identity
`∑_k m_k / (γ − π_β(σ_k)) = 0` at Fiat-Shamir-random `(β, γ)`, which is
equivalent to balance up to soundness error `K·ℓ/q` (tex §"Balanced bus proved
via logup"; the analogue of S-two's `count_eq_of_sum_eq'` plus the exceptional /
bad-set cardinality bounds). That probabilistic reduction — random point ⟹
identity ⟹ multiset balance — is the **logup soundness boundary**; we take
`Bus.Balanced` as its verified output, exactly as `exec_sound` takes
`ExecConstraints` and as Stone/S-two take the STARK certificate.

Because every interaction carries a **domain separator** in its last slot
(`memory_sep = 1`, `bytecode_sep = 2`, …) and these are distinct, memory and
bytecode tuples can never collide. That justifies analyzing the memory and
bytecode sub-buses independently here, as separate typed buses.
-/

namespace LeanVM

variable {F : Type*} [Field F] {T : Type*}

/-! ## The bus -/

/-- A bus over tuple type `T`: the multiset of pushed tuples and the multiset of
pulled tuples (a tuple's multiplicity is its count in the multiset). -/
structure Bus (T : Type*) where
  pushes : Multiset T
  pulls  : Multiset T

/-- The bus is **balanced** when the multiset of pushes equals the multiset of
pulls — i.e. every tuple is pushed exactly as often as it is pulled. -/
def Bus.Balanced (b : Bus T) : Prop := b.pushes = b.pulls

/-- Balance, stated as the per-tuple count condition `∑_{k : σ_k = σ} m_k = 0`
(the form used by the logup argument and by S-two's `Multiset.count` conclusion). -/
theorem Bus.balanced_iff_count [DecidableEq T] (b : Bus T) :
    b.Balanced ↔ ∀ σ, b.pushes.count σ = b.pulls.count σ := by
  unfold Bus.Balanced
  constructor
  · intro h σ; rw [h]
  · intro h; exact Multiset.ext.2 h

/-- **The logup consequence at the multiset level:** on a balanced bus, any tuple
that is pulled must also be pushed. (Establishing balance is the cryptographic
logup step; this elementary consequence is what the lookups rely on.) -/
theorem Bus.pull_mem_pushes {b : Bus T} (h : b.Balanced) {σ : T}
    (hσ : σ ∈ b.pulls) : σ ∈ b.pushes := by
  unfold Bus.Balanced at h
  rw [h]; exact hσ

/-! ## Memory lookup -/

/-- The memory bus pushes only address→value pairs of the memory function `m`:
every pushed pair `(a, v)` satisfies `v = m a`. In the real protocol the pushes
are `(i, m[i])` for each cell `i`, with multiplicity `memory_acc[i]`. -/
def IsMemoryPush (m : F → F) (pushes : Multiset (F × F)) : Prop :=
  ∀ p ∈ pushes, p.2 = m p.1

omit [Field F] in
/-- The canonical memory pushes — each address `a` paired with `m a` — satisfy
`IsMemoryPush`. -/
theorem isMemoryPush_image (m : F → F) (addrs : Multiset F) :
    IsMemoryPush m (addrs.map (fun a => (a, m a))) := by
  intro p hp
  rw [Multiset.mem_map] at hp
  obtain ⟨a, _, rfl⟩ := hp
  rfl

omit [Field F] in
/-- **Memory lookup soundness.** On a balanced memory bus whose pushes are
address→value pairs of `m`, every pulled pair `(a, v)` satisfies `v = m a`. -/
theorem mem_lookup_sound (m : F → F) {b : Bus (F × F)}
    (hbal : b.Balanced) (hpush : IsMemoryPush m b.pushes)
    {a v : F} (hpull : (a, v) ∈ b.pulls) : v = m a :=
  hpush (a, v) (b.pull_mem_pushes hbal hpull)

/-! ## Bytecode lookup -/

/-- The bytecode bus pushes only instruction→pc pairs of the bytecode `bc`: every
pushed pair `(cols, pc)` has `cols = encodeInstr (bc pc)`. In the real protocol
the pushes are `(instr(pc), pc)` for each `pc`, with multiplicity
`bytecode_acc[pc]`, and the bytecode is well-formed. -/
def IsBytecodePush (bc : F → Instr F) (pushes : Multiset (InstrCols F × F)) : Prop :=
  ∀ p ∈ pushes, p.1 = encodeInstr (bc p.2)

/-- The canonical bytecode pushes satisfy `IsBytecodePush`. -/
theorem isBytecodePush_image (bc : F → Instr F) (pcs : Multiset F) :
    IsBytecodePush bc (pcs.map (fun pc => (encodeInstr (bc pc), pc))) := by
  intro p hp
  rw [Multiset.mem_map] at hp
  obtain ⟨pc, _, rfl⟩ := hp
  rfl

/-- **Bytecode lookup soundness.** On a balanced bytecode bus whose pushes are the
well-formed bytecode instructions, every pulled pair `(cols, pc)` satisfies
`cols = encodeInstr (bc pc)`. -/
theorem bytecode_lookup_sound (bc : F → Instr F) {b : Bus (InstrCols F × F)}
    (hbal : b.Balanced) (hpush : IsBytecodePush bc b.pushes)
    {cols : InstrCols F} {pc : F} (hpull : (cols, pc) ∈ b.pulls) :
    cols = encodeInstr (bc pc) :=
  hpush (cols, pc) (b.pull_mem_pushes hbal hpull)

/-! ## Discharging the EXECUTION-table hypotheses -/

omit [Field F] in
/-- A balanced memory bus carrying a row's three memory pulls yields `MemBinding`
— the hypothesis `exec_sound` / `exec_complete` previously assumed. -/
theorem memBinding_of_bus (m : F → F) {b : Bus (F × F)} (r : ExecRow F)
    (hbal : b.Balanced) (hpush : IsMemoryPush m b.pushes)
    (hA : (r.addrA, r.valA) ∈ b.pulls)
    (hB : (r.addrB, r.valB) ∈ b.pulls)
    (hC : (r.addrC, r.valC) ∈ b.pulls) :
    MemBinding m r :=
  ⟨mem_lookup_sound m hbal hpush hA,
   mem_lookup_sound m hbal hpush hB,
   mem_lookup_sound m hbal hpush hC⟩

/-- **EXECUTION-table soundness from the bus.** With the memory and bytecode
buses balanced (the logup-GKR output) and a row's pulls placed on them, the AIR
constraints imply that `(n.pc, n.fp)` is a valid successor of `(r.pc, r.fp)`
under the semantics of the **actual bytecode instruction** `bc r.pc` — no
`MemBinding` or bytecode-binding hypotheses remain. -/
theorem exec_sound_of_bus (h2 : (2 : F) ≠ 0) (m : F → F) (bc : F → Instr F)
    {memBus : Bus (F × F)} {bcBus : Bus (InstrCols F × F)} (r n : ExecRow F)
    (hmemBal : memBus.Balanced) (hmemPush : IsMemoryPush m memBus.pushes)
    (hbcBal : bcBus.Balanced) (hbcPush : IsBytecodePush bc bcBus.pushes)
    (hpA : (r.addrA, r.valA) ∈ memBus.pulls)
    (hpB : (r.addrB, r.valB) ∈ memBus.pulls)
    (hpC : (r.addrC, r.valC) ∈ memBus.pulls)
    (hpI : (r.instr, r.pc) ∈ bcBus.pulls)
    (hair : ExecConstraints r n) :
    (bc r.pc).NextState m ⟨r.pc, r.fp⟩ ⟨n.pc, n.fp⟩ := by
  have hwf : r.instr = encodeInstr (bc r.pc) :=
    bytecode_lookup_sound bc hbcBal hbcPush hpI
  have hmem : MemBinding m r := memBinding_of_bus m r hmemBal hmemPush hpA hpB hpC
  exact exec_sound h2 m (bc r.pc) r n hwf hmem hair

end LeanVM
