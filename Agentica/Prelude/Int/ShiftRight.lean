import Agentica.Prelude.Int

/-!
# `Int.shift_right`

The contract, from agentica (`vm/numbers.c`, `builtin_int_shift_right` and
`shift_count`; the page `site/content/library/text-and-data/numbers.md`):

- a negative count fails with `RUNTIME-INVALID-COUNT`;
- otherwise the shift is arithmetic: the sign bit comes in, so it rounds
  toward minus infinity (`(-7).shift_right(1)` is `-4`);
- a count of 64 or more gives `-1` for a negative `a` and `0` otherwise.
-/

namespace Agentica

/-- Agentica `Int.shift_right(a, count)`. It follows `builtin_int_shift_right`
and `shift_count` of `vm/numbers.c` step by step: the count check, the test
for 64 or more, then `~(~bits >> count)` for a negative `a` and
`bits >> count` otherwise. -/
def AInt.shift_right (a count : AInt) : M AInt :=
  if count.bits.toInt < 0 then .error .invalidCount
  else if count.bits.toNat ≥ 64 then .ok (if a.bits.msb then ofInt (-1) else ofInt 0)
  else if a.bits.msb then .ok ⟨~~~(~~~a.bits >>> count.bits.toNat)⟩
  else .ok ⟨a.bits >>> count.bits.toNat⟩

namespace AInt

/-- For a count `n` with `0 ≤ n < 64`, the result is the signed value of `a`
divided by `2^n`, rounded toward minus infinity (`Int` `>>>`). -/
theorem shift_right_of_lt_64 (a count : AInt) (n : Nat)
    (hn : count.bits.toInt = n) (h : n < 64) :
    ∃ c, AInt.shift_right a count = .ok c ∧ c.bits.toInt = a.bits.toInt >>> n := by
  have hnat : count.bits.toNat = n := by
    have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
    omega
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : ¬ n ≥ 64 := by omega
  refine ⟨⟨a.bits.sshiftRight n⟩, ?_, BitVec.toInt_sshiftRight⟩
  cases hm : a.bits.msb
  · simp only [shift_right, h1, hnat, h2, hm, ↓reduceIte, Bool.false_eq_true,
      BitVec.sshiftRight_eq_of_msb_false hm]
  · simp only [shift_right, h1, hnat, h2, hm, ↓reduceIte,
      BitVec.sshiftRight_eq_of_msb_true hm]

/-- The same as a division: `a >>> n` is `a / 2^n` on `Int`, which rounds
down for a positive divisor. -/
theorem shift_right_eq_div (a count : AInt) (n : Nat)
    (hn : count.bits.toInt = n) (h : n < 64) :
    ∃ c, AInt.shift_right a count = .ok c ∧ c.bits.toInt = a.bits.toInt / (2 ^ n : Nat) := by
  obtain ⟨c, hc, hv⟩ := shift_right_of_lt_64 a count n hn h
  exact ⟨c, hc, by rw [hv, Int.shiftRight_eq_div_pow]⟩

/-- A count of 64 or more gives `-1` for a negative `a`. -/
theorem shift_right_of_ge_64_of_neg (a count : AInt) (h : 64 ≤ count.bits.toInt)
    (ha : a.bits.toInt < 0) :
    AInt.shift_right a count = .ok (ofInt (-1)) := by
  have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : count.bits.toNat ≥ 64 := by omega
  have hm : a.bits.msb = true := by rw [BitVec.msb_eq_toInt]; simpa using ha
  simp only [shift_right, h1, h2, hm, ↓reduceIte]

/-- A count of 64 or more gives `0` for an `a` that is not negative. -/
theorem shift_right_of_ge_64_of_nonneg (a count : AInt) (h : 64 ≤ count.bits.toInt)
    (ha : 0 ≤ a.bits.toInt) :
    AInt.shift_right a count = .ok (ofInt 0) := by
  have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : count.bits.toNat ≥ 64 := by omega
  have hm : a.bits.msb = false := by rw [BitVec.msb_eq_toInt]; simpa using ha
  simp only [shift_right, h1, h2, hm, ↓reduceIte, Bool.false_eq_true]

/-- A negative count is the error `RUNTIME-INVALID-COUNT`. -/
theorem shift_right_of_neg (a count : AInt) (h : count.bits.toInt < 0) :
    AInt.shift_right a count = .error .invalidCount := by
  simp only [shift_right, h, ↓reduceIte]

/-! The count cases, checked by the kernel (`rfl`). The values were compared
with agentica 0.24.1 by hand. -/

example : AInt.shift_right (ofInt (-7)) (ofInt 1) = .ok (ofInt (-4)) := rfl

example : AInt.shift_right (ofInt 7) (ofInt 1) = .ok (ofInt 3) := rfl

example : AInt.shift_right (ofInt (-7)) (ofInt 0) = .ok (ofInt (-7)) := rfl

example : AInt.shift_right (ofInt (-9223372036854775808)) (ofInt 63) = .ok (ofInt (-1)) := rfl

example : AInt.shift_right (ofInt 9223372036854775807) (ofInt 63) = .ok (ofInt 0) := rfl

example : AInt.shift_right (ofInt (-5)) (ofInt 100) = .ok (ofInt (-1)) := rfl

example : AInt.shift_right (ofInt 5) (ofInt 64) = .ok (ofInt 0) := rfl

example : AInt.shift_right (ofInt 5) (ofInt (-1)) = .error .invalidCount := rfl

end AInt

end Agentica
