import Agentica.Std.Binary.Proofs.ReadU16Le

/-!
# `read_u32_le`

Theorems about `load32_le` and `read_u32_le` of `Agentica/Std/Binary.lean`.
-/

namespace Agentica.Std.Binary

/-! ## Lemmas about the OR of the bytes -/

/-- `X * 2^j` and `c < 2^j`, both shifted left by `k`: their OR is their sum. -/
theorem nat_or_shift (X c j k : Nat) (hc : c < 2 ^ j) :
    X * 2 ^ j * 2 ^ k ||| c * 2 ^ k = (X * 2 ^ j + c) * 2 ^ k := by
  have h := Nat.two_pow_add_eq_or_of_lt hc X
  calc X * 2 ^ j * 2 ^ k ||| c * 2 ^ k = (X * 2 ^ j) <<< k ||| c <<< k := by
        simp only [Nat.shiftLeft_eq]
    _ = (X * 2 ^ j ||| c) <<< k := Nat.shiftLeft_or_distrib.symm
    _ = (X * 2 ^ j + c) <<< k := by rw [Nat.mul_comm X, h]
    _ = (X * 2 ^ j + c) * 2 ^ k := Nat.shiftLeft_eq _ _

/-- Four bytes ORed as `load32_le` does, on `Nat`. -/
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

/-- The four bytes of a little-endian 32-bit value, as `load32_le` ORs them.
`load64_le` uses it too, for each half; `ReadU64Le.lean` imports this file. -/
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

/-- `load32_le` in range never halts and is `b0 + 2^8 b1 + 2^16 b2 + 2^24 b3`,
with `bk` the byte at `offset + k`. -/
theorem load32_le_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    load32_le data offset type = pure (.ok ⟨BitVec.ofNat 64 (data.byte offset.bits.toNat +
      2 ^ 8 * data.byte (offset.bits.toNat + 1) + 2 ^ 16 * data.byte (offset.bits.toNat + 2) +
      2 ^ 24 * data.byte (offset.bits.toNat + 3))⟩) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  obtain ⟨_, a1, b1⟩ := add_at data offset 1 h0 (by omega)
  obtain ⟨_, a2, b2⟩ := add_at data offset 2 h0 (by omega)
  obtain ⟨_, a3, b3⟩ := add_at data offset 3 h0 (by omega)
  have ha := at_byte data offset h0 (by omega)
  have s8 := AInt.shift_left_lit 8 (by omega)
  have s16 := AInt.shift_left_lit 16 (by omega)
  have s24 := AInt.shift_left_lit 24 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 a2 a3 s8 s16 s24
  rw [load32_le, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, a2, b2, a3, b3, s8, s16, s24, AInt.bit_or]
  rw [or_bytes4 _ _ _ _ (Bytes.byte_lt _ _) (Bytes.byte_lt _ _) (Bytes.byte_lt _ _)
    (Bytes.byte_lt _ _)]

/-- In range, `read_u32_le` never halts and is the little-endian value. -/
theorem read_u32_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    read_u32_le data offset = pure (.ok ⟨BitVec.ofNat 64 (data.byte offset.bits.toNat +
      2 ^ 8 * data.byte (offset.bits.toNat + 1) + 2 ^ 16 * data.byte (offset.bits.toNat + 2) +
      2 ^ 24 * data.byte (offset.bits.toNat + 3))⟩) :=
  load32_le_in_range data offset "u32" h0 h4

/-- In range, `read_u32_le` is `ok` of the little-endian value as an `Int`. -/
theorem read_u32_le_toInt (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    ∃ c, read_u32_le data offset = pure (.ok c) ∧ c.bits.toInt = data.byte offset.bits.toNat +
      2 ^ 8 * data.byte (offset.bits.toNat + 1) + 2 ^ 16 * data.byte (offset.bits.toNat + 2) +
      2 ^ 24 * data.byte (offset.bits.toNat + 3) := by
  have lt := Bytes.byte_lt data
  have := lt offset.bits.toNat
  have := lt (offset.bits.toNat + 1)
  have := lt (offset.bits.toNat + 2)
  have := lt (offset.bits.toNat + 3)
  refine ⟨_, read_u32_le_in_range data offset h0 h4, ?_⟩
  rw [AInt.toInt_ofNat_of_lt (by omega)]
  omega

/-- Out of range, `read_u32_le` never halts and gives the documented error. -/
theorem read_u32_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_u32_le data offset = pure (.error { kind := "argument", message := (
      "u32 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_u32_le, load32_le, window_out data offset _ "u32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Std.Binary
