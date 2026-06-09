import Formal.Isa
import Mathlib.Tactic

/-!
# Soundness of the EXECUTION table AIR constraints (core instructions)

This file models the EXECUTION table of the minimal zkVM (`misc/minimal_zkVM.tex`,
§"EXECUTION table") and proves its **soundness**: if a table row satisfies the
AIR constraints, the memory bus-pulls hold, and the instruction columns encode a
(well-formed) core instruction `I`, then the registers of the next row are a
valid successor of the current row under `Instr.NextState` (Formal/Isa.lean).

This is the leanVM analogue of S-two's `GenericOpcode.spec`: the AIR algebra of
one step provably realizes the VM semantics of that step.

## Trust boundary (taken as hypotheses, matching S-two)

* The **memory bus** balances, so each `value_X = m[addr_X]` (`MemBinding`).
  In the full proof this is a consequence of the verified logup/bus-balance
  lemma; here it is a hypothesis on the row.
* The **bytecode bus** binds the 12 instruction columns to `bytecode[pc]`, and
  the bytecode is **well-formed** — captured by `row.instr = encodeInstr I` for
  an honest `Instr` value `I` (so flags are genuinely boolean, `aux₁ ∈ {0,1,2}`,
  exactly one opcode is active, …).
* The base field has characteristic `≠ 2` (`(2 : F) ≠ 0`), needed for the
  Lagrange selectors `P₁, P₂`. True for KoalaBear.
-/

namespace LeanVM

variable {F : Type*} [Field F]

/-! ## Column layout -/

/-- The 12 instruction-encoding columns of an EXECUTION row (§Columns). `aux₂`
is only used by precompiles; for core instructions it is `0`. -/
structure InstrCols (F : Type*) where
  operandA : F
  operandB : F
  operandC : F
  flagA : F
  flagB : F
  flagC : F
  flagCfp : F
  flagABfp : F
  flagMul : F
  flagJump : F
  aux1 : F
  aux2 : F

/-- A full EXECUTION row: registers, the three memory accesses `(addr, value)`,
and the instruction columns. 20 base-field columns total. -/
structure ExecRow (F : Type*) where
  pc : F
  fp : F
  addrA : F
  addrB : F
  addrC : F
  valA : F
  valB : F
  valC : F
  instr : InstrCols F

/-! ## Instruction encoding (§Opcode encoding)

`encodeInstr I` produces the 12 instruction columns for instruction `I`. The
flag columns are determined by the operands' addressing modes. -/

/-- Column `flag_X` for an `A`/`B` operand: `1` for immediate, `0` for memory. -/
def OperandAB.flagCol (o : OperandAB F) : F :=
  match o.mode with | .imm => 1 | .mem => 0

/-- Column `flag_C` for a `C` operand: `1` for immediate, else `0`. -/
def OperandC.flagCol (o : OperandC F) : F :=
  match o.mode with | .imm => 1 | .mem => 0 | .fpRel => 0

/-- Column `flag^C_fp` for a `C` operand: `1` for fp-relative, else `0`. -/
def OperandC.fpRelCol (o : OperandC F) : F :=
  match o.mode with | .imm => 0 | .mem => 0 | .fpRel => 1

/-- Encode a core instruction into its 12 instruction columns. -/
def encodeInstr : Instr F → InstrCols F
  | .add a b c =>
      { operandA := a.val, operandB := b.val, operandC := c.val,
        flagA := a.flagCol, flagB := b.flagCol, flagC := c.flagCol, flagCfp := c.fpRelCol,
        flagABfp := 0, flagMul := 0, flagJump := 0, aux1 := 1, aux2 := 0 }
  | .mul a b c =>
      { operandA := a.val, operandB := b.val, operandC := c.val,
        flagA := a.flagCol, flagB := b.flagCol, flagC := c.flagCol, flagCfp := c.fpRelCol,
        flagABfp := 0, flagMul := 1, flagJump := 0, aux1 := 0, aux2 := 0 }
  | .deref α β c =>
      { operandA := α, operandB := β, operandC := c.val,
        flagA := 0, flagB := 1, flagC := c.flagCol, flagCfp := c.fpRelCol,
        flagABfp := 0, flagMul := 0, flagJump := 0, aux1 := 2, aux2 := 0 }
  | .jump a b c =>
      { operandA := a.val, operandB := b.val, operandC := c.val,
        flagA := a.flagCol, flagB := b.flagCol, flagC := c.flagCol, flagCfp := c.fpRelCol,
        flagABfp := 0, flagMul := 0, flagJump := 1, aux1 := 0, aux2 := 0 }

/-! ## Virtual columns (§Opcode encoding, §AIR constraints) -/

/-- `ν_A` (§Opcode encoding). -/
def ExecRow.nuA (r : ExecRow F) : F :=
  r.instr.flagA * r.instr.operandA
    + (1 - r.instr.flagA - r.instr.flagABfp) * r.valA
    + r.instr.flagABfp * (r.fp + r.instr.operandA)

/-- `ν_B`. -/
def ExecRow.nuB (r : ExecRow F) : F :=
  r.instr.flagB * r.instr.operandB
    + (1 - r.instr.flagB - r.instr.flagABfp) * r.valB
    + r.instr.flagABfp * (r.fp + r.instr.operandB)

/-- `ν_C`. -/
def ExecRow.nuC (r : ExecRow F) : F :=
  r.instr.flagC * r.instr.operandC
    + (1 - r.instr.flagC - r.instr.flagCfp) * r.valC
    + r.instr.flagCfp * (r.fp + r.instr.operandC)

/-- Lagrange basis polynomial `P₁(x) = x(2 - x)`; equals `1` at `x = 1`, `0` at
`x ∈ {0, 2}`. Selects `flag_add` from `aux₁`. -/
def P1 (x : F) : F := x * (2 - x)

/-- Lagrange basis polynomial `P₂(x) = x(x-1)/2`; equals `1` at `x = 2`, `0` at
`x ∈ {0, 1}`. Selects `flag_deref` from `aux₁`. -/
def P2 (x : F) : F := x * (x - 1) * (2 : F)⁻¹

/-- Virtual selector `flag_add = P₁(aux₁)`. -/
def ExecRow.flagAdd (r : ExecRow F) : F := P1 r.instr.aux1

/-- Virtual selector `flag_deref = P₂(aux₁)`. -/
def ExecRow.flagDeref (r : ExecRow F) : F := P2 r.instr.aux1

/-! ## AIR constraints (§AIR constraints) -/

/-- The degree-5 AIR constraints of the EXECUTION table for a row `r` and its
successor row `n`, restricted to the core instructions (the conditional
precompile push is a bus interaction, handled elsewhere). The JUMP constraints,
with `J := flag_jump · ν_A`, double as the default `pc ← pc+1`, `fp ← fp` rule
for non-jump rows (where `flag_jump = 0 ⟹ J = 0`). -/
def ExecConstraints (r n : ExecRow F) : Prop :=
  -- Addressing constraints
  (1 - r.instr.flagA - r.instr.flagABfp) * (r.addrA - (r.fp + r.instr.operandA)) = 0 ∧
  (1 - r.instr.flagB - r.instr.flagABfp) * (r.addrB - (r.fp + r.instr.operandB)) = 0 ∧
  (1 - r.instr.flagC - r.instr.flagCfp) * (r.addrC - (r.fp + r.instr.operandC)) = 0 ∧
  -- ADD
  r.flagAdd * (r.nuB - (r.nuA + r.nuC)) = 0 ∧
  -- MUL
  r.instr.flagMul * (r.nuB - r.nuA * r.nuC) = 0 ∧
  -- DEREF
  r.flagDeref * (r.addrB - (r.valA + r.instr.operandB)) = 0 ∧
  r.flagDeref * (r.valB - r.nuC) = 0 ∧
  -- JUMP, with J = flag_jump * ν_A
  (r.instr.flagJump * r.nuA) * (1 - r.nuA) = 0 ∧
  (r.instr.flagJump * r.nuA) * (n.pc - r.nuB) = 0 ∧
  (1 - r.instr.flagJump * r.nuA) * (n.pc - (r.pc + 1)) = 0 ∧
  (r.instr.flagJump * r.nuA) * (n.fp - r.nuC) = 0 ∧
  (1 - r.instr.flagJump * r.nuA) * (n.fp - r.fp) = 0

/-- The memory bus-pull bindings for a row: each `value_X` is the memory contents
at `addr_X`. -/
def MemBinding (m : F → F) (r : ExecRow F) : Prop :=
  r.valA = m r.addrA ∧ r.valB = m r.addrB ∧ r.valC = m r.addrC

/-! ## Operand reconstruction lemmas

These show that the `ν` virtual columns recover the abstract operand resolution
of Formal/Isa.lean, given the column encoding, the memory binding, and the
relevant addressing constraint. -/

/-- Reconstruction of an `A`/`B` `ν` value (`flag_AB_fp = 0` for core opcodes). -/
theorem nu_ab_eq (m : F → F) (fp value addr : F) (o : OperandAB F)
    (hmem : value = m addr)
    (haddr : (1 - o.flagCol - 0) * (addr - (fp + o.val)) = 0) :
    o.flagCol * o.val + (1 - o.flagCol - 0) * value + 0 * (fp + o.val)
      = o.resolve m fp := by
  obtain ⟨mode, v⟩ := o
  cases mode with
  | imm => simp [OperandAB.flagCol, OperandAB.resolve]
  | mem =>
      simp only [OperandAB.flagCol, OperandAB.resolve, sub_zero, zero_mul, one_mul,
        zero_add, add_zero] at haddr ⊢
      have hAddr : addr = fp + v := sub_eq_zero.mp haddr
      rw [hmem, hAddr]

/-- Reconstruction of the `C` `ν` value. -/
theorem nu_c_eq (m : F → F) (fp value addr : F) (o : OperandC F)
    (hmem : value = m addr)
    (haddr : (1 - o.flagCol - o.fpRelCol) * (addr - (fp + o.val)) = 0) :
    o.flagCol * o.val + (1 - o.flagCol - o.fpRelCol) * value + o.fpRelCol * (fp + o.val)
      = o.resolve m fp := by
  obtain ⟨mode, v⟩ := o
  cases mode with
  | imm => simp [OperandC.flagCol, OperandC.fpRelCol, OperandC.resolve]
  | mem =>
      simp only [OperandC.flagCol, OperandC.fpRelCol, OperandC.resolve, sub_zero,
        zero_mul, one_mul, zero_add, add_zero] at haddr ⊢
      have hAddr : addr = fp + v := sub_eq_zero.mp haddr
      rw [hmem, hAddr]
  | fpRel =>
      simp only [OperandC.flagCol, OperandC.fpRelCol, OperandC.resolve]
      ring

/-! ## Soundness theorem -/

/-- **Soundness of the EXECUTION table (core instructions).**

If a row `r` and its successor `n` satisfy the AIR constraints, the memory bus
bindings hold, and the instruction columns encode a core instruction `I`, then
`(n.pc, n.fp)` is a valid successor of `(r.pc, r.fp)` under the leanVM semantics
of `I`. -/
theorem exec_sound (h2 : (2 : F) ≠ 0) (m : F → F) (I : Instr F) (r n : ExecRow F)
    (hbc : r.instr = encodeInstr I)
    (hmem : MemBinding m r)
    (hair : ExecConstraints r n) :
    I.NextState m ⟨r.pc, r.fp⟩ ⟨n.pc, n.fp⟩ := by
  obtain ⟨hmA, hmB, hmC⟩ := hmem
  obtain ⟨ha1, ha2, ha3, hAdd, hMul, hDer1, hDer2, hJ1, hJ2, hJ3, hJ4, hJ5⟩ := hair
  cases I with
  | add a b c =>
      -- column facts
      have e_fA : r.instr.flagA = a.flagCol := by simp only [hbc, encodeInstr]
      have e_oA : r.instr.operandA = a.val := by simp only [hbc, encodeInstr]
      have e_fB : r.instr.flagB = b.flagCol := by simp only [hbc, encodeInstr]
      have e_oB : r.instr.operandB = b.val := by simp only [hbc, encodeInstr]
      have e_fC : r.instr.flagC = c.flagCol := by simp only [hbc, encodeInstr]
      have e_fCfp : r.instr.flagCfp = c.fpRelCol := by simp only [hbc, encodeInstr]
      have e_oC : r.instr.operandC = c.val := by simp only [hbc, encodeInstr]
      have e_ABfp : r.instr.flagABfp = 0 := by simp only [hbc, encodeInstr]
      have e_mul : r.instr.flagMul = 0 := by simp only [hbc, encodeInstr]
      have e_jmp : r.instr.flagJump = 0 := by simp only [hbc, encodeInstr]
      have e_aux : r.instr.aux1 = 1 := by simp only [hbc, encodeInstr]
      -- ν reconstructions
      have hnA : r.nuA = a.resolve m r.fp := by
        rw [ExecRow.nuA, e_fA, e_oA, e_ABfp]
        rw [e_fA, e_ABfp, e_oA] at ha1
        exact nu_ab_eq m r.fp r.valA r.addrA a hmA ha1
      have hnB : r.nuB = b.resolve m r.fp := by
        rw [ExecRow.nuB, e_fB, e_oB, e_ABfp]
        rw [e_fB, e_ABfp, e_oB] at ha2
        exact nu_ab_eq m r.fp r.valB r.addrB b hmB ha2
      have hnC : r.nuC = c.resolve m r.fp := by
        rw [ExecRow.nuC, e_fC, e_oC, e_fCfp]
        rw [e_fC, e_fCfp, e_oC] at ha3
        exact nu_c_eq m r.fp r.valC r.addrC c hmC ha3
      have e_fAdd : r.flagAdd = 1 := by
        rw [ExecRow.flagAdd, e_aux, P1]; ring
      -- register update from JUMP constraints (J = 0)
      rw [e_jmp] at hJ3 hJ5
      simp only [zero_mul, sub_zero, one_mul, sub_eq_zero] at hJ3 hJ5
      -- ADD semantic constraint
      rw [e_fAdd, one_mul, hnA, hnB, hnC, sub_eq_zero] at hAdd
      refine ⟨?_, hJ3, hJ5⟩
      linear_combination -hAdd
  | mul a b c =>
      have e_fA : r.instr.flagA = a.flagCol := by simp only [hbc, encodeInstr]
      have e_oA : r.instr.operandA = a.val := by simp only [hbc, encodeInstr]
      have e_fB : r.instr.flagB = b.flagCol := by simp only [hbc, encodeInstr]
      have e_oB : r.instr.operandB = b.val := by simp only [hbc, encodeInstr]
      have e_fC : r.instr.flagC = c.flagCol := by simp only [hbc, encodeInstr]
      have e_fCfp : r.instr.flagCfp = c.fpRelCol := by simp only [hbc, encodeInstr]
      have e_oC : r.instr.operandC = c.val := by simp only [hbc, encodeInstr]
      have e_ABfp : r.instr.flagABfp = 0 := by simp only [hbc, encodeInstr]
      have e_mul : r.instr.flagMul = 1 := by simp only [hbc, encodeInstr]
      have e_jmp : r.instr.flagJump = 0 := by simp only [hbc, encodeInstr]
      have hnA : r.nuA = a.resolve m r.fp := by
        rw [ExecRow.nuA, e_fA, e_oA, e_ABfp]
        rw [e_fA, e_ABfp, e_oA] at ha1
        exact nu_ab_eq m r.fp r.valA r.addrA a hmA ha1
      have hnB : r.nuB = b.resolve m r.fp := by
        rw [ExecRow.nuB, e_fB, e_oB, e_ABfp]
        rw [e_fB, e_ABfp, e_oB] at ha2
        exact nu_ab_eq m r.fp r.valB r.addrB b hmB ha2
      have hnC : r.nuC = c.resolve m r.fp := by
        rw [ExecRow.nuC, e_fC, e_oC, e_fCfp]
        rw [e_fC, e_fCfp, e_oC] at ha3
        exact nu_c_eq m r.fp r.valC r.addrC c hmC ha3
      rw [e_jmp] at hJ3 hJ5
      simp only [zero_mul, sub_zero, one_mul, sub_eq_zero] at hJ3 hJ5
      rw [e_mul, one_mul, hnA, hnB, hnC, sub_eq_zero] at hMul
      refine ⟨?_, hJ3, hJ5⟩
      linear_combination -hMul
  | deref α β c =>
      have e_fA : r.instr.flagA = 0 := by simp only [hbc, encodeInstr]
      have e_oA : r.instr.operandA = α := by simp only [hbc, encodeInstr]
      have e_fB : r.instr.flagB = 1 := by simp only [hbc, encodeInstr]
      have e_oB : r.instr.operandB = β := by simp only [hbc, encodeInstr]
      have e_ABfp : r.instr.flagABfp = 0 := by simp only [hbc, encodeInstr]
      have e_fC : r.instr.flagC = c.flagCol := by simp only [hbc, encodeInstr]
      have e_fCfp : r.instr.flagCfp = c.fpRelCol := by simp only [hbc, encodeInstr]
      have e_oC : r.instr.operandC = c.val := by simp only [hbc, encodeInstr]
      have e_jmp : r.instr.flagJump = 0 := by simp only [hbc, encodeInstr]
      have e_aux : r.instr.aux1 = 2 := by simp only [hbc, encodeInstr]
      have hnC : r.nuC = c.resolve m r.fp := by
        rw [ExecRow.nuC, e_fC, e_oC, e_fCfp]
        rw [e_fC, e_fCfp, e_oC] at ha3
        exact nu_c_eq m r.fp r.valC r.addrC c hmC ha3
      -- ν_A = value_A (memory mode, flag_A = 0); J = 0 since flag_jump = 0
      have e_jzero : r.instr.flagJump * r.nuA = 0 := by rw [e_jmp, zero_mul]
      rw [e_jzero] at hJ3 hJ5
      simp only [sub_zero, one_mul, sub_eq_zero] at hJ3 hJ5
      have e_fDer : r.flagDeref = 1 := by
        rw [ExecRow.flagDeref, e_aux, P2]
        rw [show (2 : F) - 1 = 1 by ring, mul_one, mul_inv_cancel₀ h2]
      -- addr_A = fp + α  (addressing constraint, flag_A = 0)
      rw [e_fA, e_ABfp, e_oA] at ha1
      simp only [sub_zero, one_mul, sub_eq_zero] at ha1
      -- DEREF constraints
      rw [e_fDer, one_mul, e_oB, sub_eq_zero] at hDer1   -- addr_B = val_A + β
      rw [e_fDer, one_mul, hnC, sub_eq_zero] at hDer2    -- val_B = ν_C
      refine ⟨?_, hJ3, hJ5⟩
      -- goal: m (m (fp + α) + β) = c.resolve
      rw [← hDer2, hmB, hDer1, hmA, ha1]
  | jump a b c =>
      have e_fA : r.instr.flagA = a.flagCol := by simp only [hbc, encodeInstr]
      have e_oA : r.instr.operandA = a.val := by simp only [hbc, encodeInstr]
      have e_fB : r.instr.flagB = b.flagCol := by simp only [hbc, encodeInstr]
      have e_oB : r.instr.operandB = b.val := by simp only [hbc, encodeInstr]
      have e_fC : r.instr.flagC = c.flagCol := by simp only [hbc, encodeInstr]
      have e_fCfp : r.instr.flagCfp = c.fpRelCol := by simp only [hbc, encodeInstr]
      have e_oC : r.instr.operandC = c.val := by simp only [hbc, encodeInstr]
      have e_ABfp : r.instr.flagABfp = 0 := by simp only [hbc, encodeInstr]
      have e_jmp : r.instr.flagJump = 1 := by simp only [hbc, encodeInstr]
      have hnA : r.nuA = a.resolve m r.fp := by
        rw [ExecRow.nuA, e_fA, e_oA, e_ABfp]
        rw [e_fA, e_ABfp, e_oA] at ha1
        exact nu_ab_eq m r.fp r.valA r.addrA a hmA ha1
      have hnB : r.nuB = b.resolve m r.fp := by
        rw [ExecRow.nuB, e_fB, e_oB, e_ABfp]
        rw [e_fB, e_ABfp, e_oB] at ha2
        exact nu_ab_eq m r.fp r.valB r.addrB b hmB ha2
      have hnC : r.nuC = c.resolve m r.fp := by
        rw [ExecRow.nuC, e_fC, e_oC, e_fCfp]
        rw [e_fC, e_fCfp, e_oC] at ha3
        exact nu_c_eq m r.fp r.valC r.addrC c hmC ha3
      -- J = ν_A
      rw [e_jmp, one_mul] at hJ1 hJ2 hJ3 hJ4 hJ5
      rw [hnA] at hJ1 hJ2 hJ3 hJ4 hJ5
      rw [hnB] at hJ2
      rw [hnC] at hJ4
      -- condition is boolean
      have hbool : a.resolve m r.fp = 0 ∨ a.resolve m r.fp = 1 := by
        rcases mul_eq_zero.mp hJ1 with h | h
        · exact Or.inl h
        · exact Or.inr (by linear_combination -h)
      refine ⟨hbool, ?_, ?_⟩
      · intro h1
        rw [h1, one_mul, sub_eq_zero] at hJ2 hJ4
        exact ⟨hJ2, hJ4⟩
      · intro h0
        rw [h0] at hJ3 hJ5
        simp only [sub_zero, one_mul, sub_eq_zero] at hJ3 hJ5
        exact ⟨hJ3, hJ5⟩

end LeanVM
