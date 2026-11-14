import Agentica.Std.Binary.Proofs.ReadU16Le

/-!
# `read_u16_be`

Theorems about `load16_be` and `read_u16_be` of `Agentica/Std/Binary.lean`.
-/

namespace Agentica.Std.Binary

/-- In range, `load16_be` never halts and is `256 * b0 + b1`, for any type
name. -/
theorem load16_be_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    load16_be data offset type = pure (.ok ⟨BitVec.ofNat 64
      (data.byte (offset.bits.toNat + 1) + 256 * data.byte offset.bits.toNat)⟩) := by
  have := AInt.toInt_eq_toNat_of_nonneg h0
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  obtain ⟨_, a1, b1⟩ := add_at data offset 1 h0 (by omega)
  have ha := at_byte data offset h0 (by omega)
  have hs := AInt.shift_left_lit 8 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 hs
  rw [load16_be, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, hs, AInt.bit_or]
  rw [AInt.or_shift_8 _ _ (Bytes.byte_lt _ _) (Bytes.byte_lt _ _)]

/-- In range, `read_u16_be` never halts and is `256 * b0 + b1`. -/
theorem read_u16_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    read_u16_be data offset = pure (.ok ⟨BitVec.ofNat 64
      (data.byte (offset.bits.toNat + 1) + 256 * data.byte offset.bits.toNat)⟩) :=
  load16_be_in_range data offset "u16" h0 h2

/-- In range, `read_u16_be` is `ok` of `256 * b0 + b1` as an `Int`. -/
theorem read_u16_be_toInt (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    ∃ c, read_u16_be data offset = pure (.ok c) ∧
      c.bits.toInt = data.byte (offset.bits.toNat + 1) + 256 * data.byte offset.bits.toNat := by
  have := Bytes.byte_lt data offset.bits.toNat
  have := Bytes.byte_lt data (offset.bits.toNat + 1)
  refine ⟨_, read_u16_be_in_range data offset h0 h2, ?_⟩
  rw [AInt.toInt_ofNat_of_lt (by omega)]
  omega

/-- Out of range, `read_u16_be` never halts and gives the documented error. -/
theorem read_u16_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 2) :
    read_u16_be data offset = pure (.error { kind := "argument", message := (
      "u16 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  rw [read_u16_be, load16_be, window_out data offset _ "u16" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Std.Binary
