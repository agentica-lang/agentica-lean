import Agentica.Std.Binary.Proofs.ReadU32Be

/-!
# `read_frame_length`

Theorems about `read_frame_length` of `Agentica/Std/Binary.lean`: a negative
limit is an error, else the big-endian u32 at `offset` when it is at most the
limit, else a `binary.too_large` error. Out of range it is the error of
`read_u32_be`.
-/

namespace Agentica.Std.Binary

/-- A negative limit never halts and gives the documented error. -/
theorem read_frame_length_negative (data : Bytes) (offset max : AInt)
    (h : max.bits.toInt < 0) :
    read_frame_length data offset max = pure (.error { kind := "argument", message := (
      "frame limit " ++ String.from_int max ++ " is negative") }) := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have hlt : AInt.lt max (AInt.ofInt 0) = true := by
    simp only [AInt.lt, decide_eq_true_eq]; omega
  simp only [read_frame_length, hlt, ↓reduceIte]

/-- In range with a limit of 0 or more, `read_frame_length` never halts: the
length when it is at most the limit, else the documented error. -/
theorem read_frame_length_in_range (data : Bytes) (offset max : AInt)
    (hm : 0 ≤ max.bits.toInt) (h0 : 0 ≤ offset.bits.toInt)
    (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    read_frame_length data offset max =
      let length : AInt := ⟨BitVec.ofNat 64 (be32 data offset.bits.toNat)⟩
      if (be32 data offset.bits.toNat : Int) ≤ max.bits.toInt then pure (.ok length)
      else pure (.error { kind := "binary.too_large", message := (
        "frame length " ++ String.from_int length ++ " is above the limit " ++
          String.from_int max) }) := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have hlt : ¬ AInt.lt max (AInt.ofInt 0) = true := by
    simp only [AInt.lt, decide_eq_true_eq]; omega
  have hb := be32_lt data offset.bits.toNat
  have ht : (BitVec.ofNat 64 (be32 data offset.bits.toNat)).toInt =
      be32 data offset.bits.toNat := AInt.toInt_ofNat_of_lt (by omega)
  simp only [read_frame_length, hlt, Bool.false_eq_true, ↓reduceIte,
    load32_be_in_range data offset "u32" h0 h4, pure_bind, AInt.gt, ht]
  by_cases hle : (be32 data offset.bits.toNat : Int) ≤ max.bits.toInt
  · have : ¬ (be32 data offset.bits.toNat : Int) > max.bits.toInt := by omega
    simp only [hle, this, decide_false, Bool.false_eq_true, ↓reduceIte]
  · have : (be32 data offset.bits.toNat : Int) > max.bits.toInt := by omega
    simp only [hle, this, decide_true, ↓reduceIte]

/-- Out of range with a limit of 0 or more, `read_frame_length` never halts
and gives the error of `read_u32_be`. -/
theorem read_frame_length_out_of_range (data : Bytes) (offset max : AInt)
    (hm : 0 ≤ max.bits.toInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_frame_length data offset max = read_u32_be data offset := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  have hlt : ¬ AInt.lt max (AInt.ofInt 0) = true := by
    simp only [AInt.lt, decide_eq_true_eq]; omega
  rw [read_u32_be_out_of_range data offset h]
  simp only [read_frame_length, hlt, Bool.false_eq_true, ↓reduceIte]
  rw [load32_be, window_out data offset (AInt.ofInt 4) "u32" (by omega) (by omega) (by omega)]
  rfl

end Agentica.Std.Binary
