import Agentica.Prelude.Int

/-!
# `Int` `+` and `-`

The VM adds and subtracts with `__builtin_add_overflow` and
`__builtin_sub_overflow` (`vm/interp.c`, `agc_op_add_i` and `agc_op_sub_i`):
when the exact result does not fit in 64 bits, the program halts with
`RUNTIME-INTEGER-OVERFLOW`. It never wraps.
-/

namespace Agentica

/-- Agentica `a + b` on `Int` (`agc_op_add_i`): the exact sum, or
`RUNTIME-INTEGER-OVERFLOW`. -/
def AInt.add (a b : AInt) : M AInt :=
  if a.bits.saddOverflow b.bits then .error .integerOverflow else pure ⟨a.bits + b.bits⟩

/-- Agentica `a - b` on `Int` (`agc_op_sub_i`): the exact difference, or
`RUNTIME-INTEGER-OVERFLOW`. -/
def AInt.sub (a b : AInt) : M AInt :=
  if a.bits.ssubOverflow b.bits then .error .integerOverflow else pure ⟨a.bits - b.bits⟩

namespace AInt

/-- When the exact sum fits in 64 bits, `a + b` is that sum. -/
theorem add_ok (a b : AInt) (h : -2 ^ 63 ≤ a.bits.toInt + b.bits.toInt)
    (h' : a.bits.toInt + b.bits.toInt < 2 ^ 63) :
    ∃ c, AInt.add a b = pure c ∧ c.bits.toInt = a.bits.toInt + b.bits.toInt := by
  have hno : ¬ a.bits.saddOverflow b.bits = true := by
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  exact ⟨_, by simp only [AInt.add, hno, ↓reduceIte, Bool.false_eq_true],
    BitVec.toInt_add_of_not_saddOverflow hno⟩

/-- When the exact sum does not fit in 64 bits, `a + b` halts. -/
theorem add_overflow (a b : AInt)
    (h : a.bits.toInt + b.bits.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ a.bits.toInt + b.bits.toInt) :
    AInt.add a b = .error .integerOverflow := by
  have ho : a.bits.saddOverflow b.bits = true := by
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [AInt.add, ho, ↓reduceIte]

/-- When the exact difference fits in 64 bits, `a - b` is that difference. -/
theorem sub_ok (a b : AInt) (h : -2 ^ 63 ≤ a.bits.toInt - b.bits.toInt)
    (h' : a.bits.toInt - b.bits.toInt < 2 ^ 63) :
    ∃ c, AInt.sub a b = pure c ∧ c.bits.toInt = a.bits.toInt - b.bits.toInt := by
  have hno : ¬ a.bits.ssubOverflow b.bits = true := by
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  exact ⟨_, by simp only [AInt.sub, hno, ↓reduceIte, Bool.false_eq_true],
    BitVec.toInt_sub_of_not_ssubOverflow hno⟩

/-- When the exact difference does not fit in 64 bits, `a - b` halts. -/
theorem sub_overflow (a b : AInt)
    (h : a.bits.toInt - b.bits.toInt < -2 ^ 63 ∨ 2 ^ 63 ≤ a.bits.toInt - b.bits.toInt) :
    AInt.sub a b = .error .integerOverflow := by
  have ho : a.bits.ssubOverflow b.bits = true := by
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  simp only [AInt.sub, ho, ↓reduceIte]

/-! Edge cases, checked by the kernel (`rfl`). -/

example : AInt.add (ofInt 9223372036854775807) (ofInt 1) = .error .integerOverflow := rfl

example : AInt.sub (ofInt (-9223372036854775808)) (ofInt 1) = .error .integerOverflow := rfl

example : AInt.add (ofInt (-1)) (ofInt 1) = pure (ofInt 0) := rfl

end AInt

end Agentica
