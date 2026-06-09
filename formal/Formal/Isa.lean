import Mathlib.Algebra.Field.Basic

/-!
# leanVM ISA semantics — core instructions (no precompiles)

This file formalizes the instruction set of the minimal zkVM described in
`misc/minimal_zkVM.tex` (§"VM specification"), restricted to the four **core
instructions** `ADD`, `MUL`, `DEREF`, `JUMP`. The two precompiles
(`POSEIDON_OP`, `EXTENSION_OP`) are intentionally out of scope here.

Everything is parameterized by an abstract field `F`. This mirrors the
methodology of the S-two / Stone soundness proofs, which define the virtual
machine `NextState` relation over an arbitrary field and only instantiate the
concrete prime later. KoalaBear (`F = ZMod (2^31 - 2^24 + 1)`) is one such
instantiation.

The central definition is `Instr.NextState`, the single-step semantics of the
VM. The companion file `Formal/ExecTable.lean` proves that the AIR constraints
of the EXECUTION table imply this relation (soundness of the encoding).
-/

namespace LeanVM

variable {F : Type*} [Field F]

/-- Addressing mode for the **A** and **B** operands of core instructions:
immediate or memory. (fp-relative is reserved for the `C` operand and for
precompiles, so it is excluded here.) -/
inductive Mode2 where
  | imm
  | mem
  deriving DecidableEq, Repr

/-- Addressing mode for the **C** operand: immediate, memory, or fp-relative. -/
inductive Mode3 where
  | imm
  | mem
  | fpRel
  deriving DecidableEq, Repr

/-- An `A`/`B` operand: an addressing mode together with a field value. -/
structure OperandAB (F : Type*) where
  mode : Mode2
  val  : F

/-- A `C` operand. -/
structure OperandC (F : Type*) where
  mode : Mode3
  val  : F

/-- Resolve an `A`/`B` operand to a field value, given memory `m` and frame
pointer `fp` (§Addressing modes):
`imm ↦ x`, `mem ↦ m[fp + x]`. -/
def OperandAB.resolve (m : F → F) (fp : F) (o : OperandAB F) : F :=
  match o.mode with
  | .imm => o.val
  | .mem => m (fp + o.val)

/-- Resolve a `C` operand: `imm ↦ x`, `mem ↦ m[fp + x]`, `fpRel ↦ fp + x`. -/
def OperandC.resolve (m : F → F) (fp : F) (o : OperandC F) : F :=
  match o.mode with
  | .imm   => o.val
  | .mem   => m (fp + o.val)
  | .fpRel => fp + o.val

/-- Core ISA instructions (precompiles excluded).

* `add a b c` / `mul a b c`: the `A`,`B` operands range over `imm`/`mem`, the
  `C` operand additionally over `fpRel`.
* `deref α β c`: a double dereference `m[m[fp + α] + β] = val(c)`; here `α, β`
  are raw field offsets (the spec fixes `A` to memory mode and `B` to immediate
  mode for this opcode).
* `jump a b c`: conditional jump. -/
inductive Instr (F : Type*) where
  | add   (a b : OperandAB F) (c : OperandC F)
  | mul   (a b : OperandAB F) (c : OperandC F)
  | deref (α β : F) (c : OperandC F)
  | jump  (a b : OperandAB F) (c : OperandC F)

/-- VM register state: program counter and frame pointer (§Registers). The rest
of the machine (memory, bytecode) is read-only and modeled separately. -/
structure State (F : Type*) where
  pc : F
  fp : F

/-- Single-step semantics of a core instruction (§ISA): relates the current
state `s` to a successor state `t` under (read-only) memory `m`.

* `ADD`/`MUL`/`DEREF`: assert the arithmetic / memory side-condition, with the
  register update `pc ← pc + 1`, `fp ← fp`.
* `JUMP`: the condition `ν_A` is boolean; if it is `1` the registers jump to
  `(ν_B, ν_C)`, otherwise they advance by `(pc + 1, fp)`. -/
def Instr.NextState (m : F → F) (i : Instr F) (s t : State F) : Prop :=
  match i with
  | .add a b c =>
      a.resolve m s.fp + c.resolve m s.fp = b.resolve m s.fp
        ∧ t.pc = s.pc + 1 ∧ t.fp = s.fp
  | .mul a b c =>
      a.resolve m s.fp * c.resolve m s.fp = b.resolve m s.fp
        ∧ t.pc = s.pc + 1 ∧ t.fp = s.fp
  | .deref α β c =>
      m (m (s.fp + α) + β) = c.resolve m s.fp
        ∧ t.pc = s.pc + 1 ∧ t.fp = s.fp
  | .jump a b c =>
      (a.resolve m s.fp = 0 ∨ a.resolve m s.fp = 1)
        ∧ (a.resolve m s.fp = 1 → t.pc = b.resolve m s.fp ∧ t.fp = c.resolve m s.fp)
        ∧ (a.resolve m s.fp = 0 → t.pc = s.pc + 1 ∧ t.fp = s.fp)

end LeanVM
