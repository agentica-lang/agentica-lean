import Agentica.Prelude.Int

/-!
# `Int.shift_left`

The contract, from agentica (`vm/numbers.c`, `builtin_int_shift_left` and
`shift_count`; the page `site/content/library/text-and-data/numbers.md`):

- a negative count fails with `RUNTIME-INVALID-COUNT`;
- otherwise the result is the low 64 bits of `a * 2^n`: bits that leave the
  top are dropped, and bit 63 becomes the sign. It never overflows;
- a count of 64 or more gives 0.
-/

namespace Agentica

/-- Agentica `Int.shift_left(a, count)`. It follows `builtin_int_shift_left`
and `shift_count` of `vm/numbers.c` step by step: the count check, then the
test for 64 or more, then the shift. -/
def AInt.shift_left (a count : AInt) : M AInt :=
  if count.bits.toInt < 0 then .error .invalidCount
  else if count.bits.toNat ≥ 64 then .ok ⟨0⟩
  else .ok ⟨a.bits <<< count.bits.toNat⟩

namespace AInt

/-- For a count `n` with `0 ≤ n < 64`, the unsigned value of the result is
`a * 2^n` modulo `2^64`. -/
theorem shift_left_of_lt_64 (a count : AInt) (n : Nat)
    (hn : count.bits.toInt = n) (h : n < 64) :
    AInt.shift_left a count = .ok ⟨BitVec.ofNat 64 (a.bits.toNat * 2 ^ n)⟩ := by
  have hnat : count.bits.toNat = n := by
    have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
    omega
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : ¬ n ≥ 64 := by omega
  simp only [shift_left, h1, hnat, h2, ↓reduceIte, Except.ok.injEq, AInt.mk.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]

/-- A count of 64 or more shifts every bit out: the result is 0. -/
theorem shift_left_of_ge_64 (a count : AInt) (h : 64 ≤ count.bits.toInt) :
    AInt.shift_left a count = .ok ⟨0⟩ := by
  have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : count.bits.toNat ≥ 64 := by omega
  simp only [shift_left, h1, h2, ↓reduceIte]

/-- A negative count is the error `RUNTIME-INVALID-COUNT`. -/
theorem shift_left_of_neg (a count : AInt) (h : count.bits.toInt < 0) :
    AInt.shift_left a count = .error .invalidCount := by
  simp only [shift_left, h, ↓reduceIte]

/-! The count cases, checked by the kernel (`rfl`). The values were compared
with agentica 0.24.1 by hand. -/

example : AInt.shift_left (ofInt 3) (ofInt 8) = .ok (ofInt 768) := rfl

example : AInt.shift_left (ofInt 5) (ofInt 0) = .ok (ofInt 5) := rfl

example : AInt.shift_left (ofInt 1) (ofInt 63) = .ok (ofInt (-9223372036854775808)) := rfl

example : AInt.shift_left (ofInt (-1)) (ofInt 1) = .ok (ofInt (-2)) := rfl

example : AInt.shift_left (ofInt 1) (ofInt 64) = .ok (ofInt 0) := rfl

example : AInt.shift_left (ofInt 1) (ofInt (-1)) = .error .invalidCount := rfl

end AInt

end Agentica
