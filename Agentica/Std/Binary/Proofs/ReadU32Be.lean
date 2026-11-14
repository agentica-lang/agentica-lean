import Agentica.Std.Binary.Proofs.ReadU32Le

/-!
# `read_u32_be`

Theorems about `load32_be` and `read_u32_be` of `Agentica/Std/Binary.lean`.
It is `load32_le` with the bytes in the other order, so `or_bytes4` of
`ReadU32Le.lean` proves it too.
-/

namespace Agentica.Std.Binary

/-! ## Theorems -/

/-- The four bytes at `o`, big-endian: `2^24 b0 + 2^16 b1 + 2^8 b2 + b3`. -/
def be32 (data : Bytes) (o : Nat) : Nat :=
  data.byte (o + 3) + 2 ^ 8 * data.byte (o + 2) + 2 ^ 16 * data.byte (o + 1) +
    2 ^ 24 * data.byte o

/-- `be32` fits in 32 bits. -/
theorem be32_lt (data : Bytes) (o : Nat) : be32 data o < 2 ^ 32 := by
  have lt := Bytes.byte_lt data
  have := lt o
  have := lt (o + 1)
  have := lt (o + 2)
  have := lt (o + 3)
  unfold be32; omega

/-- `load32_be` in range never halts and is the 64 bits of `be32`. -/
theorem load32_be_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    load32_be data offset type =
      pure (.ok ⟨BitVec.ofNat 64 (be32 data offset.bits.toNat)⟩) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  obtain ⟨_, a1, b1⟩ := add_at data offset 1 h0 (by omega)
  obtain ⟨_, a2, b2⟩ := add_at data offset 2 h0 (by omega)
  obtain ⟨_, a3, b3⟩ := add_at data offset 3 h0 (by omega)
  have ha := at_byte data offset h0 (by omega)
  have s8 := AInt.shift_left_lit 8 (by omega)
  have s16 := AInt.shift_left_lit 16 (by omega)
  have s24 := AInt.shift_left_lit 24 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 a2 a3 s8 s16 s24
  rw [load32_be, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, a2, b2, a3, b3, s8, s16, s24, AInt.bit_or]
  rw [or_bytes4 _ _ _ _ (Bytes.byte_lt _ _) (Bytes.byte_lt _ _) (Bytes.byte_lt _ _)
    (Bytes.byte_lt _ _)]
  rfl

/-- In range, `read_u32_be` never halts and is the big-endian value. -/
theorem read_u32_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    ∃ c, read_u32_be data offset = pure (.ok c) ∧
      c.bits.toInt = be32 data offset.bits.toNat := by
  have := be32_lt data offset.bits.toNat
  exact ⟨_, load32_be_in_range data offset "u32" h0 h4, AInt.toInt_ofNat_of_lt (by omega)⟩

/-- Out of range, `read_u32_be` never halts and gives the documented error. -/
theorem read_u32_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_u32_be data offset = pure (.error { kind := "argument", message := (
      "u32 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_u32_be, load32_be, window_out data offset _ "u32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Std.Binary
