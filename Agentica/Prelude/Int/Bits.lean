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

/-- A high byte shifted left by 8, ORed with a low byte, is
`low + 256 * high`: how the little-endian readers of `std/binary` build a
16-bit value. -/
theorem or_shift_8 (lo hi : Nat) (hlo : lo < 256) (hhi : hi < 256) :
    (BitVec.ofNat 64 hi <<< 8 ||| BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo + 256 * hi) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := hi) (by omega),
    Nat.mod_eq_of_lt (a := lo) (by omega), Nat.mod_eq_of_lt (a := hi * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm hi, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

/-- `X * 2^j` and `c < 2^j`, both shifted left by `k`: their OR is their sum. -/
theorem nat_or_shift (X c j k : Nat) (hc : c < 2 ^ j) :
    X * 2 ^ j * 2 ^ k ||| c * 2 ^ k = (X * 2 ^ j + c) * 2 ^ k := by
  have h := Nat.two_pow_add_eq_or_of_lt hc X
  calc X * 2 ^ j * 2 ^ k ||| c * 2 ^ k = (X * 2 ^ j) <<< k ||| c <<< k := by
        simp only [Nat.shiftLeft_eq]
    _ = (X * 2 ^ j ||| c) <<< k := Nat.shiftLeft_or_distrib.symm
    _ = (X * 2 ^ j + c) <<< k := by rw [Nat.mul_comm X, h]
    _ = (X * 2 ^ j + c) * 2 ^ k := Nat.shiftLeft_eq _ _

/-- Four bytes ORed as the little-endian readers do, on `Nat`. -/
theorem nat_or_bytes4 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (_hd : d < 256) :
    ((d * 2 ^ 24 ||| c * 2 ^ 16) ||| b * 2 ^ 8) ||| a =
      a + 2 ^ 8 * b + 2 ^ 16 * c + 2 ^ 24 * d := by
  have e1 : d * 2 ^ 24 ||| c * 2 ^ 16 = (d * 2 ^ 8 + c) * 2 ^ 16 := by
    rw [show d * 2 ^ 24 = d * 2 ^ 8 * 2 ^ 16 by omega]
    exact nat_or_shift d c 8 16 hc
  have e2 : (d * 2 ^ 8 + c) * 2 ^ 16 ||| b * 2 ^ 8 = ((d * 2 ^ 8 + c) * 2 ^ 8 + b) * 2 ^ 8 := by
    rw [show (d * 2 ^ 8 + c) * 2 ^ 16 = (d * 2 ^ 8 + c) * 2 ^ 8 * 2 ^ 8 by omega]
    exact nat_or_shift _ b 8 8 hb
  have e3 := Nat.two_pow_add_eq_or_of_lt (i := 8) (b := a) ha ((d * 2 ^ 8 + c) * 2 ^ 8 + b)
  rw [e1, e2, Nat.mul_comm _ (2 ^ 8), ← e3]
  omega

/-- The four bytes of a little-endian 32-bit value, as the readers OR them. -/
theorem or_bytes4 (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256)
    (hd : d < 256) :
    (((BitVec.ofNat 64 d <<< 24 ||| BitVec.ofNat 64 c <<< 16) ||| BitVec.ofNat 64 b <<< 8) |||
      BitVec.ofNat 64 a) = BitVec.ofNat 64 (a + 2 ^ 8 * b + 2 ^ 16 * c + 2 ^ 24 * d) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (a := c) (by omega),
    Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := a) (by omega),
    Nat.mod_eq_of_lt (a := d * 2 ^ 24) (by omega), Nat.mod_eq_of_lt (a := c * 2 ^ 16) (by omega),
    Nat.mod_eq_of_lt (a := b * 2 ^ 8) (by omega), nat_or_bytes4 a b c d ha hb hc hd,
    Nat.mod_eq_of_lt (by omega)]

/-- Two 32-bit halves, the high one shifted by 32. -/
theorem or_halves (lo hi : Nat) (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    (BitVec.ofNat 64 hi <<< 32 ||| BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo + 2 ^ 32 * hi) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := hi) (by omega), Nat.mod_eq_of_lt (a := lo) (by omega),
    Nat.mod_eq_of_lt (a := hi * 2 ^ 32) (by omega), Nat.mul_comm hi,
    ← Nat.two_pow_add_eq_or_of_lt hlo, Nat.mod_eq_of_lt (by omega)]
  omega
/-! Examples, checked by the kernel (`rfl`). The values were compared with
agentica 0.24.1 by hand. -/

example : AInt.bit_and (ofInt 12) (ofInt 10) = ofInt 8 := rfl

example : AInt.bit_or (ofInt 12) (ofInt 10) = ofInt 14 := rfl

example : AInt.bit_xor (ofInt 12) (ofInt 10) = ofInt 6 := rfl

example : AInt.bit_not (ofInt 0) = ofInt (-1) := rfl

example : AInt.bit_and (ofInt (-1)) (ofInt 255) = ofInt 255 := rfl

end AInt

end Agentica
