import Agentica.Prelude.Int

/-!
# `Int.shift_right_unsigned`

The contract, from agentica (`vm/numbers.c`, `builtin_int_shift_right_unsigned`
and `shift_count`; the catalog row in `compiler/catalog/builtins_data.agc`;
the page `site/content/library/text-and-data/numbers.md`):

- a negative count fails with `RUNTIME-INVALID-COUNT`;
- otherwise the 64 bits of `a` are read as an unsigned number and shifted
  right, with zeros coming in;
- a count of 64 or more gives 0. (In C, `x >> n` with `n >= 64` is undefined,
  so the VM tests for it first.)
-/

namespace Agentica

/-- Agentica `Int.shift_right_unsigned(a, count)`. It follows
`builtin_int_shift_right_unsigned` and `shift_count` of `vm/numbers.c` step by
step: the count check, then the test for 64 or more, then the shift. -/
def AInt.shift_right_unsigned (a count : AInt) : M AInt :=
  if count.bits.toInt < 0 then .error .invalidCount
  else if count.bits.toNat ≥ 64 then .ok ⟨0⟩
  else .ok ⟨a.bits >>> count.bits.toNat⟩

namespace AInt

/-- For a count `n` with `0 ≤ n < 64`, the result is the unsigned value of `a`
divided by `2^n`, rounded down. -/
theorem shift_right_unsigned_of_lt_64 (a count : AInt) (n : Nat)
    (hn : count.bits.toInt = n) (h : n < 64) :
    a.shift_right_unsigned count = .ok ⟨BitVec.ofNat 64 (a.bits.toNat / 2 ^ n)⟩ := by
  have hnat : count.bits.toNat = n := by
    have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
    omega
  have hdiv : a.bits.toNat / 2 ^ n < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.bits.isLt
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : ¬ n ≥ 64 := by omega
  simp only [shift_right_unsigned, h1, hnat, h2, ↓reduceIte, Except.ok.injEq, AInt.mk.injEq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hdiv]

/-- The same, read as numbers: the unsigned value of the result is
`a.bits.toNat / 2^n`. -/
theorem toNat_shift_right_unsigned_of_lt_64 (a count : AInt) (n : Nat)
    (hn : count.bits.toInt = n) (h : n < 64) :
    (a.shift_right_unsigned count).map (·.bits.toNat) = .ok (a.bits.toNat / 2 ^ n) := by
  rw [shift_right_unsigned_of_lt_64 a count n hn h]
  simp only [Except.map, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.bits.isLt)]

/-- A count of 64 or more shifts every bit out: the result is 0. -/
theorem shift_right_unsigned_of_ge_64 (a count : AInt) (h : 64 ≤ count.bits.toInt) :
    a.shift_right_unsigned count = .ok ⟨0⟩ := by
  have := toInt_eq_toNat_of_nonneg (x := count.bits) (by omega)
  have h1 : ¬ count.bits.toInt < 0 := by omega
  have h2 : count.bits.toNat ≥ 64 := by omega
  simp only [shift_right_unsigned, h1, h2, ↓reduceIte]

/-- A negative count is the error `RUNTIME-INVALID-COUNT`. -/
theorem shift_right_unsigned_of_neg (a count : AInt) (h : count.bits.toInt < 0) :
    a.shift_right_unsigned count = .error .invalidCount := by
  simp only [shift_right_unsigned, h, ↓reduceIte]

/-! The examples of the site page, checked by the kernel (`rfl`). -/

example : (ofInt (-1)).shift_right_unsigned (ofInt 60) = .ok (ofInt 15) := rfl

example : (ofInt (-1)).shift_right_unsigned (ofInt (64 - 8)) = .ok (ofInt 255) :=
  rfl

end AInt

end Agentica
