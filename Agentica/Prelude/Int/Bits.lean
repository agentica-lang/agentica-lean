import Agentica.Prelude.Int

/-!
# `Int.bit_and`, `Int.bit_or`, `Int.bit_xor` and `Int.bit_not`

The VM works on the 64 bits of each `Int` as an unsigned number and reads the
result back as signed (`vm/numbers.c`, `builtin_int_bit_and` and the others,
through `int_from_bits`). None of them halts.
-/

namespace Agentica

/-- Agentica `Int.bit_and(a, b)` (`builtin_int_bit_and`). -/
def AInt.bit_and (a b : AInt) : AInt := ⟨a.bits &&& b.bits⟩

/-- Agentica `Int.bit_or(a, b)` (`builtin_int_bit_or`). -/
def AInt.bit_or (a b : AInt) : AInt := ⟨a.bits ||| b.bits⟩

/-- Agentica `Int.bit_xor(a, b)` (`builtin_int_bit_xor`). -/
def AInt.bit_xor (a b : AInt) : AInt := ⟨a.bits ^^^ b.bits⟩

/-- Agentica `Int.bit_not(a)` (`builtin_int_bit_not`). -/
def AInt.bit_not (a : AInt) : AInt := ⟨~~~a.bits⟩

namespace AInt

/-- `bit_and` on the unsigned values. -/
theorem toNat_bit_and (a b : AInt) :
    (AInt.bit_and a b).bits.toNat = a.bits.toNat &&& b.bits.toNat :=
  BitVec.toNat_and _ _

/-- `bit_or` on the unsigned values. -/
theorem toNat_bit_or (a b : AInt) :
    (AInt.bit_or a b).bits.toNat = a.bits.toNat ||| b.bits.toNat :=
  BitVec.toNat_or _ _

/-- `bit_xor` on the unsigned values. -/
theorem toNat_bit_xor (a b : AInt) :
    (AInt.bit_xor a b).bits.toNat = a.bits.toNat ^^^ b.bits.toNat :=
  BitVec.toNat_xor _ _

/-- `bit_not` is `-a - 1` on the signed values, so it never overflows. -/
theorem toInt_bit_not (a : AInt) : (AInt.bit_not a).bits.toInt = -a.bits.toInt - 1 := by
  simp only [AInt.bit_not]
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond (x := a.bits), BitVec.toNat_not]
  have := a.bits.isLt
  split <;> split <;> omega

/-! Examples, checked by the kernel (`rfl`). The values were compared with
agentica 0.24.1 by hand. -/

example : AInt.bit_and (ofInt 12) (ofInt 10) = ofInt 8 := rfl

example : AInt.bit_or (ofInt 12) (ofInt 10) = ofInt 14 := rfl

example : AInt.bit_xor (ofInt 12) (ofInt 10) = ofInt 6 := rfl

example : AInt.bit_not (ofInt 0) = ofInt (-1) := rfl

example : AInt.bit_and (ofInt (-1)) (ofInt 255) = ofInt 255 := rfl

end AInt

end Agentica
