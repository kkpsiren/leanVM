import Formal.ExecTable

/-!
# Completeness of the EXECUTION table AIR constraints (core instructions)

The converse of `exec_sound` (Formal/ExecTable.lean). Where soundness says
"constraints ⟹ semantics", completeness says "semantics ⟹ the honest prover can
fill the row". Concretely: for any core instruction `I`, memory `m`, and a step
`s → t` satisfying `Instr.NextState`, we exhibit an explicit EXECUTION row whose
instruction columns encode `I`, whose memory columns are consistent with `m`,
and which — together with a next row carrying registers `t` — satisfies every
AIR constraint of the table.

`mkRow` is the honest column assignment; the addresses are `fp + operand` for
the A/B/C operands, except the DEREF B-address which is the double-dereference
`m[fp+α] + β`. Together with `exec_sound`, this pins down the table's behavior in
both directions for the four core opcodes.

Note an asymmetry: `exec_sound` needs `(2 : F) ≠ 0` (to evaluate the Lagrange
selector `P₂(2) = 1` and conclude the DEREF constraint is active), but
`exec_complete` does **not** — the honest assignment makes the relevant
constraint factors vanish identically, regardless of the selector's value.
-/

namespace LeanVM

variable {F : Type*} [Field F]

/-- The honest current-row column assignment for instruction `I` executed from
state `s` under memory `m`. -/
def mkRow (m : F → F) (s : State F) : Instr F → ExecRow F
  | .add a b c =>
      { pc := s.pc, fp := s.fp,
        addrA := s.fp + a.val, addrB := s.fp + b.val, addrC := s.fp + c.val,
        valA := m (s.fp + a.val), valB := m (s.fp + b.val), valC := m (s.fp + c.val),
        instr := encodeInstr (.add a b c) }
  | .mul a b c =>
      { pc := s.pc, fp := s.fp,
        addrA := s.fp + a.val, addrB := s.fp + b.val, addrC := s.fp + c.val,
        valA := m (s.fp + a.val), valB := m (s.fp + b.val), valC := m (s.fp + c.val),
        instr := encodeInstr (.mul a b c) }
  | .deref α β c =>
      { pc := s.pc, fp := s.fp,
        addrA := s.fp + α, addrB := m (s.fp + α) + β, addrC := s.fp + c.val,
        valA := m (s.fp + α), valB := m (m (s.fp + α) + β), valC := m (s.fp + c.val),
        instr := encodeInstr (.deref α β c) }
  | .jump a b c =>
      { pc := s.pc, fp := s.fp,
        addrA := s.fp + a.val, addrB := s.fp + b.val, addrC := s.fp + c.val,
        valA := m (s.fp + a.val), valB := m (s.fp + b.val), valC := m (s.fp + c.val),
        instr := encodeInstr (.jump a b c) }

/-- The honest next row: only its registers `(pc, fp) = t` matter to the AIR
constraints; the remaining columns are filled with zeros. -/
def mkNext (I : Instr F) (t : State F) : ExecRow F :=
  { pc := t.pc, fp := t.fp,
    addrA := 0, addrB := 0, addrC := 0, valA := 0, valB := 0, valC := 0,
    instr := encodeInstr I }

/-- **Completeness of the EXECUTION table (core instructions).**

If `s → t` is a valid leanVM step for instruction `I` under memory `m`, then the
explicit assignment `mkRow`/`mkNext` gives a current row encoding `I` with
registers `s`, a next row with registers `t`, memory columns consistent with
`m`, and all EXECUTION-table AIR constraints satisfied. -/
theorem exec_complete (m : F → F) (I : Instr F) (s t : State F)
    (hstep : I.NextState m s t) :
    (mkRow m s I).pc = s.pc ∧ (mkRow m s I).fp = s.fp ∧
    (mkNext I t).pc = t.pc ∧ (mkNext I t).fp = t.fp ∧
    (mkRow m s I).instr = encodeInstr I ∧
    MemBinding m (mkRow m s I) ∧
    ExecConstraints (mkRow m s I) (mkNext I t) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · cases I <;> rfl
  · cases I <;> rfl
  · cases I <;> rfl
  · cases I <;> exact ⟨rfl, rfl, rfl⟩
  · cases I with
    | add a b c =>
        obtain ⟨hsem, hpc, hfp⟩ := hstep
        have hnA : (mkRow m s (.add a b c)).nuA = a.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + a.val)) (s.fp + a.val) a rfl (by ring)
        have hnB : (mkRow m s (.add a b c)).nuB = b.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + b.val)) (s.fp + b.val) b rfl (by ring)
        have hnC : (mkRow m s (.add a b c)).nuC = c.resolve m s.fp :=
          nu_c_eq m s.fp (m (s.fp + c.val)) (s.fp + c.val) c rfl (by ring)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · rw [hnA, hnB, hnC]
          simp only [ExecRow.flagAdd, mkRow, encodeInstr, P1]; linear_combination -hsem
        · simp only [mkRow, encodeInstr]; ring
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hpc
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hfp
    | mul a b c =>
        obtain ⟨hsem, hpc, hfp⟩ := hstep
        have hnA : (mkRow m s (.mul a b c)).nuA = a.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + a.val)) (s.fp + a.val) a rfl (by ring)
        have hnB : (mkRow m s (.mul a b c)).nuB = b.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + b.val)) (s.fp + b.val) b rfl (by ring)
        have hnC : (mkRow m s (.mul a b c)).nuC = c.resolve m s.fp :=
          nu_c_eq m s.fp (m (s.fp + c.val)) (s.fp + c.val) c rfl (by ring)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [ExecRow.flagAdd, mkRow, encodeInstr, P1]; ring
        · rw [hnA, hnB, hnC]; simp only [mkRow, encodeInstr]; linear_combination -hsem
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hpc
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hfp
    | deref α β c =>
        obtain ⟨hsem, hpc, hfp⟩ := hstep
        have hnC : (mkRow m s (.deref α β c)).nuC = c.resolve m s.fp :=
          nu_c_eq m s.fp (m (s.fp + c.val)) (s.fp + c.val) c rfl (by ring)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [ExecRow.flagAdd, mkRow, encodeInstr, P1]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · rw [hnC]; simp only [mkRow, encodeInstr]; rw [hsem]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hpc
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, mkNext, encodeInstr, zero_mul, sub_zero, one_mul]
          linear_combination hfp
    | jump a b c =>
        obtain ⟨hcond, h1, h0⟩ := hstep
        have hnA : (mkRow m s (.jump a b c)).nuA = a.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + a.val)) (s.fp + a.val) a rfl (by ring)
        have hnB : (mkRow m s (.jump a b c)).nuB = b.resolve m s.fp :=
          nu_ab_eq m s.fp (m (s.fp + b.val)) (s.fp + b.val) b rfl (by ring)
        have hnC : (mkRow m s (.jump a b c)).nuC = c.resolve m s.fp :=
          nu_c_eq m s.fp (m (s.fp + c.val)) (s.fp + c.val) c rfl (by ring)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [ExecRow.flagAdd, mkRow, encodeInstr, P1]; ring
        · simp only [mkRow, encodeInstr]; ring
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · simp only [ExecRow.flagDeref, mkRow, encodeInstr, P2]; ring
        · rw [hnA]; simp only [mkRow, encodeInstr]
          rcases hcond with h | h <;> rw [h] <;> ring
        · rw [hnA, hnB]; simp only [mkRow, mkNext, encodeInstr]
          rcases hcond with h | h
          · rw [h]; ring
          · obtain ⟨hpc1, _⟩ := h1 h; rw [h, hpc1]; ring
        · rw [hnA]; simp only [mkRow, mkNext, encodeInstr]
          rcases hcond with h | h
          · obtain ⟨hpc0, _⟩ := h0 h; rw [h, hpc0]; ring
          · rw [h]; ring
        · rw [hnA, hnC]; simp only [mkRow, mkNext, encodeInstr]
          rcases hcond with h | h
          · rw [h]; ring
          · obtain ⟨_, hfp1⟩ := h1 h; rw [h, hfp1]; ring
        · rw [hnA]; simp only [mkRow, mkNext, encodeInstr]
          rcases hcond with h | h
          · obtain ⟨_, hfp0⟩ := h0 h; rw [h, hfp0]; ring
          · rw [h]; ring

end LeanVM
