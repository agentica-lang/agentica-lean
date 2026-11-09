import Agentica.Prelude.Int

/-!
# `Int` comparisons

The VM compares `Int`s as signed 64-bit numbers (`int64_t`), so a value with
bit 63 set is negative and below every value without it. `==` and `!=`
compare the 64 bits. Each comparison gives a `Bool` and never halts.
-/

namespace Agentica

/-- Agentica `a == b` on `Int`. -/
def AInt.eq (a b : AInt) : Bool := decide (a = b)

/-- Agentica `a != b` on `Int`. -/
def AInt.ne (a b : AInt) : Bool := !decide (a = b)

/-- Agentica `a < b` on `Int`, signed. -/
def AInt.lt (a b : AInt) : Bool := decide (a.bits.toInt < b.bits.toInt)

/-- Agentica `a <= b` on `Int`, signed. -/
def AInt.le (a b : AInt) : Bool := decide (a.bits.toInt ≤ b.bits.toInt)

/-- Agentica `a > b` on `Int`, signed. -/
def AInt.gt (a b : AInt) : Bool := decide (a.bits.toInt > b.bits.toInt)

/-- Agentica `a >= b` on `Int`, signed. -/
def AInt.ge (a b : AInt) : Bool := decide (a.bits.toInt ≥ b.bits.toInt)

namespace AInt

@[simp] theorem eq_iff (a b : AInt) : AInt.eq a b = true ↔ a.bits.toInt = b.bits.toInt := by
  simp only [AInt.eq, decide_eq_true_eq]
  constructor
  · intro h; rw [h]
  · intro h; cases a; cases b; simp only [AInt.mk.injEq]; exact BitVec.toInt_inj.mp h

@[simp] theorem ne_iff (a b : AInt) : AInt.ne a b = true ↔ a.bits.toInt ≠ b.bits.toInt := by
  have h := eq_iff a b
  simp only [AInt.eq, decide_eq_true_eq] at h
  simp only [AInt.ne, Bool.not_eq_true', decide_eq_false_iff_not, ne_eq]
  exact not_congr h

@[simp] theorem lt_iff (a b : AInt) : AInt.lt a b = true ↔ a.bits.toInt < b.bits.toInt := by
  simp only [AInt.lt, decide_eq_true_eq]

@[simp] theorem le_iff (a b : AInt) : AInt.le a b = true ↔ a.bits.toInt ≤ b.bits.toInt := by
  simp only [AInt.le, decide_eq_true_eq]

@[simp] theorem gt_iff (a b : AInt) : AInt.gt a b = true ↔ a.bits.toInt > b.bits.toInt := by
  simp only [AInt.gt, decide_eq_true_eq]

@[simp] theorem ge_iff (a b : AInt) : AInt.ge a b = true ↔ a.bits.toInt ≥ b.bits.toInt := by
  simp only [AInt.ge, decide_eq_true_eq]

/-! Signed, not unsigned: `-1` (all bits set) is below `0`. -/

example : AInt.lt (ofInt (-1)) (ofInt 0) = true := rfl

example : AInt.gt (ofInt (-9223372036854775808)) (ofInt 9223372036854775807) = false := rfl

end AInt

end Agentica
