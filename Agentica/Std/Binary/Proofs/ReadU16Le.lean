import Agentica.Std.Binary

/-!
# `read_u16_le`, and `window` for every reader

Theorems about `window`, `load16_le` and `read_u16_le` of
`Agentica/Std/Binary.lean`, which `translator/` writes from `std/binary`. The
statements and proofs are written by hand and use short names
(`Bytes.length`), which the namespace resolves to the prelude.
-/

namespace Agentica.Std.Binary

/-! ## Lemmas about `window`, for every reader -/

/-- In range, `window` never halts and is `ok()`. -/
theorem window_ok (data : Bytes) (offset n : AInt) (type : String)
    (hn : 0 ≤ n.bits.toInt) (hn8 : n.bits.toInt ≤ 8) (h0 : 0 ≤ offset.bits.toInt)
    (h : offset.bits.toInt + n.bits.toInt ≤ data.data.size) :
    window data offset n type = pure (.ok ()) := by
  have := data.small
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have hsz := Bytes.length_toInt data
  obtain ⟨lim, hlim, hlimv⟩ := AInt.sub_ok (Bytes.length data) n (by omega) (by omega)
  have hlt : ¬ AInt.lt offset (AInt.ofInt 0) = true := by
    simp only [AInt.lt, decide_eq_true_eq]; omega
  have hgt : AInt.gt offset lim = false := by
    simp only [AInt.gt, decide_eq_false_iff_not]; omega
  simp only [window, hlt, Bool.false_eq_true, ↓reduceIte, hlim, pure_bind, hgt]

/-- Out of range, `window` never halts and is the documented error. -/
theorem window_out (data : Bytes) (offset n : AInt) (type : String)
    (hn : 0 ≤ n.bits.toInt) (hn8 : n.bits.toInt ≤ 8)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + n.bits.toInt) :
    window data offset n type = pure (.error { kind := "argument", message := (
      type ++ " at offset " ++
        String.from_int offset ++ " is outside bytes of length " ++
        String.from_int (Bytes.length data)) }) := by
  have := data.small
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have hsz := Bytes.length_toInt data
  by_cases hneg : offset.bits.toInt < 0
  · have hlt : AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    simp only [window, hlt, ↓reduceIte, pure_bind]
  · have hlt : ¬ AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    obtain ⟨lim, hlim, hlimv⟩ := AInt.sub_ok (Bytes.length data) n (by omega) (by omega)
    have hgt : AInt.gt offset lim = true := by
      simp only [AInt.gt, decide_eq_true_eq]; omega
    simp only [window, hlt, Bool.false_eq_true, ↓reduceIte, hlim, pure_bind, hgt]

/-- `data[offset]` in range, with the byte as `Bytes.byte`. -/
theorem at_byte (data : Bytes) (offset : AInt) (h0 : 0 ≤ offset.bits.toInt)
    (h : offset.bits.toInt < data.data.size) :
    Bytes.at data offset = pure ⟨BitVec.ofNat 64 (data.byte offset.bits.toNat)⟩ :=
  Bytes.at_ok data offset h0 h

/-- `data[offset + k]` in range: the add and the read never halt. -/
theorem add_at (data : Bytes) (offset : AInt) (k : Nat) (h0 : 0 ≤ offset.bits.toInt)
    (hk : offset.bits.toInt + k < data.data.size) :
    ∃ i, AInt.add offset (AInt.ofInt k) = pure i ∧
      Bytes.at data i = pure ⟨BitVec.ofNat 64 (data.byte (offset.bits.toNat + k))⟩ := by
  have := data.small
  have hki : (AInt.ofInt k).bits.toInt = k := AInt.ofInt_toInt (by omega)
  obtain ⟨i, hi, hiv⟩ := AInt.add_ok offset (AInt.ofInt k) (by omega) (by omega)
  have := AInt.toInt_eq_toNat_of_nonneg h0
  have hinat : i.bits.toNat = offset.bits.toNat + k := by
    have := AInt.toInt_eq_toNat_of_nonneg (x := i.bits) (by omega)
    omega
  refine ⟨i, hi, ?_⟩
  rw [Bytes.at_ok data i (by omega) (by omega), hinat]
  rfl

/-! ## The theorems -/

/-- In range, `load16_le` never halts and is `b0 + 256 * b1`. -/
theorem load16_le_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    load16_le data offset type = pure (.ok ⟨BitVec.ofNat 64
      (data.byte offset.bits.toNat + 256 * data.byte (offset.bits.toNat + 1))⟩) := by
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  obtain ⟨_, a1, b1⟩ := add_at data offset 1 h0 (by omega)
  have ha := at_byte data offset h0 (by omega)
  have hs := AInt.shift_left_lit 8 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 hs
  rw [load16_le, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, hs, AInt.bit_or]
  rw [AInt.or_shift_8 _ _ (Bytes.byte_lt _ _) (Bytes.byte_lt _ _)]

/-- In range, `read_u16_le` never halts and is `b0 + 256 * b1`. -/
theorem read_u16_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    read_u16_le data offset = pure (.ok ⟨BitVec.ofNat 64
      ((data.data[offset.bits.toNat]!).toNat +
        256 * (data.data[offset.bits.toNat + 1]!).toNat)⟩) :=
  load16_le_in_range data offset "u16" h0 h2

/-- In range, `read_u16_le` is `ok` of `b0 + 256 * b1` as an `Int`. -/
theorem read_u16_le_toInt (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    ∃ c, read_u16_le data offset = pure (.ok c) ∧
      c.bits.toInt = data.byte offset.bits.toNat + 256 * data.byte (offset.bits.toNat + 1) := by
  have := Bytes.byte_lt data offset.bits.toNat
  have := Bytes.byte_lt data (offset.bits.toNat + 1)
  refine ⟨_, load16_le_in_range data offset "u16" h0 h2, ?_⟩
  rw [AInt.toInt_ofNat_of_lt (by omega)]
  omega

/-- Out of range, `read_u16_le` never halts and gives the documented error:
a negative offset, or one where two bytes do not fit (up to `Int.MAX`). -/
theorem read_u16_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 2) :
    read_u16_le data offset = pure (.error { kind := "argument", message := (
      "u16 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have := data.small
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  have hsz := Bytes.length_toInt data
  by_cases hneg : offset.bits.toInt < 0
  · have hlt : AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    simp only [read_u16_le, load16_le, window, hlt, ↓reduceIte, pure_bind]
    rfl
  · have hlt : ¬ AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    obtain ⟨lim, hlim, hlimv⟩ :=
      AInt.sub_ok (Bytes.length data) (AInt.ofInt 2) (by omega) (by omega)
    have hgt : AInt.gt offset lim = true := by
      simp only [AInt.gt, decide_eq_true_eq]; omega
    simp only [read_u16_le, load16_le, window, hlt, Bool.false_eq_true, ↓reduceIte, hlim,
      pure_bind, hgt]
    rfl

/-! ## The cases compared with agentica

`Binary.read_u16_le` on the bytes `[1, 2, 255]` printed these results (agentica
0.31.1, by hand); the kernel checks the translation gives the same. -/

example : read_u16_le Bytes.sample (AInt.ofInt (-1)) =
    pure (.error { kind := "argument", message := (
      "u16 at offset -1 is outside bytes of length 3") }) := rfl

example : read_u16_le Bytes.sample (AInt.ofInt 0) = pure (.ok (AInt.ofInt 513)) := rfl

example : read_u16_le Bytes.sample (AInt.ofInt 1) = pure (.ok (AInt.ofInt 65282)) := rfl

example : read_u16_le Bytes.sample (AInt.ofInt 2) =
    pure (.error { kind := "argument", message := (
      "u16 at offset 2 is outside bytes of length 3") }) := rfl

example : read_u16_le Bytes.sample (AInt.ofInt 9223372036854775807) =
    pure (.error { kind := "argument", message := (
      "u16 at offset 9223372036854775807 is outside bytes of length 3") }) := by
  rfl

end Agentica.Std.Binary
