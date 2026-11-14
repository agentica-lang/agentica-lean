import Agentica.Prelude.Int

/-!
# `Int` unary minus

`-a` negates with `agc_op_neg_i` (`vm/interp.c`): the least `Int`,
`-9223372036854775808`, has no negation in 64 bits, so `-a` on it halts with
`RUNTIME-INTEGER-OVERFLOW`. A literal such as `-5` is one number, not a
minus applied to `5`.
-/

namespace Agentica

/-- Agentica `-a` on `Int` (`agc_op_neg_i`): the negation, or
`RUNTIME-INTEGER-OVERFLOW` for the least `Int`. -/
def AInt.neg (a : AInt) : M AInt :=
  if a.bits = BitVec.intMin 64 then .error .integerOverflow else pure ⟨-a.bits⟩

namespace AInt

/-- Except for the least `Int`, `-a` is the negation. -/
theorem neg_ok (a : AInt) (h : -2 ^ 63 < a.bits.toInt) :
    ∃ c, AInt.neg a = pure c ∧ c.bits.toInt = -a.bits.toInt := by
  have hne : a.bits ≠ BitVec.intMin 64 := by
    intro he
    rw [he, BitVec.toInt_intMin] at h
    simp at h
  exact ⟨⟨-a.bits⟩, by simp only [AInt.neg, hne, ↓reduceIte],
    BitVec.toInt_neg_of_ne_intMin hne⟩

/-- `-a` halts on the least `Int`. -/
theorem neg_overflow (a : AInt) (h : a.bits.toInt = -2 ^ 63) :
    AInt.neg a = .error .integerOverflow := by
  have he : a.bits = BitVec.intMin 64 := by
    apply BitVec.eq_of_toInt_eq
    rw [h, BitVec.toInt_intMin]
    decide
  simp only [AInt.neg, he, ↓reduceIte]

/-! Edge cases, checked by the kernel (`rfl`). -/

example : AInt.neg (ofInt (-9223372036854775808)) = .error .integerOverflow := rfl

example : AInt.neg (ofInt 9223372036854775807) = pure (ofInt (-9223372036854775807)) := rfl

example : AInt.neg (ofInt 0) = pure (ofInt 0) := rfl

end AInt

end Agentica
