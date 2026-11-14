import Agentica.Std.Binary.Proofs.ReadU32Le

/-!
# `read_u64_le` and `read_i64_le`

Theorems about `load64_le`, `unsigned64`, `read_u64_le` and `read_i64_le` of
`Agentica/Std/Binary.lean`.
-/

namespace Agentica.Std.Binary

/-! ## Theorems -/

/-- Two 32-bit halves, the high one shifted by 32. -/
theorem or_halves (lo hi : Nat) (hlo : lo < 2 ^ 32) (hhi : hi < 2 ^ 32) :
    (BitVec.ofNat 64 hi <<< 32 ||| BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo + 2 ^ 32 * hi) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := hi) (by omega), Nat.mod_eq_of_lt (a := lo) (by omega),
    Nat.mod_eq_of_lt (a := hi * 2 ^ 32) (by omega), Nat.mul_comm hi,
    ← Nat.two_pow_add_eq_or_of_lt hlo, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The eight bytes at `offset`, little-endian: `b0 + 2^8 b1 + ... + 2^56 b7`. -/
def le64 (data : Bytes) (o : Nat) : Nat :=
  data.byte o + 2 ^ 8 * data.byte (o + 1) + 2 ^ 16 * data.byte (o + 2) +
    2 ^ 24 * data.byte (o + 3) + 2 ^ 32 * (data.byte (o + 4) + 2 ^ 8 * data.byte (o + 5) +
    2 ^ 16 * data.byte (o + 6) + 2 ^ 24 * data.byte (o + 7))

/-- `load64_le` in range never halts and is the 64 bits of `le64`. -/
theorem load64_le_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    load64_le data offset type =
      pure (.ok ⟨BitVec.ofNat 64 (le64 data offset.bits.toNat)⟩) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  obtain ⟨_, a1, b1⟩ := add_at data offset 1 h0 (by omega)
  obtain ⟨_, a2, b2⟩ := add_at data offset 2 h0 (by omega)
  obtain ⟨_, a3, b3⟩ := add_at data offset 3 h0 (by omega)
  obtain ⟨_, a4, b4⟩ := add_at data offset 4 h0 (by omega)
  obtain ⟨_, a5, b5⟩ := add_at data offset 5 h0 (by omega)
  obtain ⟨_, a6, b6⟩ := add_at data offset 6 h0 (by omega)
  obtain ⟨_, a7, b7⟩ := add_at data offset 7 h0 (by omega)
  have ha := at_byte data offset h0 (by omega)
  have s8 := AInt.shift_left_lit 8 (by omega)
  have s16 := AInt.shift_left_lit 16 (by omega)
  have s24 := AInt.shift_left_lit 24 (by omega)
  have s32 := AInt.shift_left_lit 32 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 a2 a3 a4 a5 a6 a7 s8 s16 s24 s32
  rw [load64_le, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, s8, s16,
    s24, s32, AInt.bit_or]
  have lt := Bytes.byte_lt data
  rw [or_bytes4 _ _ _ _ (lt _) (lt _) (lt _) (lt _),
    or_bytes4 _ _ _ _ (lt _) (lt _) (lt _) (lt _)]
  have := lt offset.bits.toNat
  have := lt (offset.bits.toNat + 1)
  have := lt (offset.bits.toNat + 2)
  have := lt (offset.bits.toNat + 3)
  have := lt (offset.bits.toNat + 4)
  have := lt (offset.bits.toNat + 5)
  have := lt (offset.bits.toNat + 6)
  have := lt (offset.bits.toNat + 7)
  rw [or_halves _ _ (by omega) (by omega)]
  rfl

/-- `le64` fits in 64 bits. -/
theorem le64_lt (data : Bytes) (o : Nat) : le64 data o < 2 ^ 64 := by
  have lt := Bytes.byte_lt data
  have := lt o
  have := lt (o + 1)
  have := lt (o + 2)
  have := lt (o + 3)
  have := lt (o + 4)
  have := lt (o + 5)
  have := lt (o + 6)
  have := lt (o + 7)
  unfold le64; omega

/-- `le64` is below `2^63` exactly when the top byte is below 128. -/
theorem le64_lt_iff (data : Bytes) (o : Nat) :
    le64 data o < 2 ^ 63 ↔ data.byte (o + 7) < 128 := by
  have lt := Bytes.byte_lt data
  have := lt o
  have := lt (o + 1)
  have := lt (o + 2)
  have := lt (o + 3)
  have := lt (o + 4)
  have := lt (o + 5)
  have := lt (o + 6)
  unfold le64; omega

/-- The signed value of the 64 bits of `le64`: two's complement. -/
theorem le64_toInt (data : Bytes) (o : Nat) :
    (BitVec.ofNat 64 (le64 data o)).toInt =
      if le64 data o < 2 ^ 63 then (le64 data o : Int) else le64 data o - 2 ^ 64 := by
  have := le64_lt data o
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  split <;> split <;> omega

/-- In range, `read_i64_le` never halts and is the little-endian value read as
two's complement. -/
theorem read_i64_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    ∃ c, read_i64_le data offset = pure (.ok c) ∧
      c.bits.toInt = if le64 data offset.bits.toNat < 2 ^ 63
        then (le64 data offset.bits.toNat : Int)
        else le64 data offset.bits.toNat - 2 ^ 64 :=
  ⟨_, load64_le_in_range data offset "i64" h0 h8, le64_toInt data _⟩

/-- In range, `read_u64_le` never halts. When the top byte is below 128 it is
the little-endian value; otherwise the value is above `Int.MAX` and it is the
documented error. -/
theorem read_u64_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    read_u64_le data offset =
      if data.byte (offset.bits.toNat + 7) < 128 then
        pure (.ok ⟨BitVec.ofNat 64 (le64 data offset.bits.toNat)⟩)
      else
        pure (.error { kind := "number.range", message := (
          "u64 at offset " ++ String.from_int offset ++ " does not fit in Int") }) := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have ht := le64_toInt data offset.bits.toNat
  have hiff := le64_lt_iff data offset.bits.toNat
  have hlt := le64_lt data offset.bits.toNat
  rw [read_u64_le, load64_le_in_range data offset "u64" h0 h8]
  simp only [pure_bind, unsigned64, AInt.lt, h0i]
  by_cases hb : data.byte (offset.bits.toNat + 7) < 128
  · have : ¬ (BitVec.ofNat 64 (le64 data offset.bits.toNat)).toInt < 0 := by
      rw [ht, ite_eq_left (hiff.mpr hb)]; omega
    simp only [hb, this, decide_false, ↓reduceIte, Bool.false_eq_true]
  · have : (BitVec.ofNat 64 (le64 data offset.bits.toNat)).toInt < 0 := by
      rw [ht, ite_eq_right (fun h => hb (hiff.mp h))]; omega
    simp only [hb, this, decide_true, ↓reduceIte]

/-- In range with the top byte below 128, `read_u64_le` is `ok` of the
little-endian value. -/
theorem read_u64_le_toInt (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size)
    (hb : data.byte (offset.bits.toNat + 7) < 128) :
    ∃ c, read_u64_le data offset = pure (.ok c) ∧
      c.bits.toInt = le64 data offset.bits.toNat := by
  refine ⟨_, by rw [read_u64_le_in_range data offset h0 h8, ite_eq_left hb], ?_⟩
  exact AInt.toInt_ofNat_of_lt ((le64_lt_iff data _).mpr hb)

/-- Out of range, `read_u64_le` never halts and gives the documented error. -/
theorem read_u64_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_u64_le data offset = pure (.error { kind := "argument", message := (
      "u64 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_u64_le, load64_le, window_out data offset _ "u64" (by omega) (by omega)
    (by omega)]
  rfl

/-- Out of range, `read_i64_le` never halts and gives the documented error. -/
theorem read_i64_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_i64_le data offset = pure (.error { kind := "argument", message := (
      "i64 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_i64_le, load64_le, window_out data offset _ "i64" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Std.Binary
