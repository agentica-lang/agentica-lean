import Agentica.Std.Binary

/-!
# The writers of `std/binary`

Theorems about `fits`, `pack`, the `bytesN_be` and `bytesN_le` helpers and the
range errors of the writers of `Agentica/Std/Binary.lean`.
`RoundTrip.lean` reads the bytes of each writer back.
-/

namespace Agentica.Std.Binary

/-! ## Theorems -/

/-- `v.shift_right(s) & 255` for a count `s` up to 56 is byte `s / 8` of the
64 bits of `v`: the sign bits that the shift brings in stay above the low 8. -/
theorem shift_and (v : AInt) (s : Nat) (hs : s ≤ 56) :
    ∃ c, AInt.shift_right v (AInt.ofInt s) = .ok c ∧
      (AInt.bit_and c (AInt.ofInt 255)).bits.toNat = v.bits.toNat / 2 ^ s % 256 := by
  have hsi : (AInt.ofInt s).bits.toInt = s := AInt.ofInt_toInt (by omega)
  have hsn : (AInt.ofInt s).bits.toNat = s := by
    have := AInt.toInt_eq_toNat_of_nonneg (x := (AInt.ofInt s).bits) (by omega)
    omega
  have h1 : ¬ (AInt.ofInt s).bits.toInt < 0 := by omega
  have h2 : ¬ s ≥ 64 := by omega
  refine ⟨⟨v.bits.sshiftRight s⟩, ?_, ?_⟩
  · cases hm : v.bits.msb
    · simp only [AInt.shift_right, h1, hsn, h2, hm, ↓reduceIte, Bool.false_eq_true,
        BitVec.sshiftRight_eq_of_msb_false hm]
    · simp only [AInt.shift_right, h1, hsn, h2, hm, ↓reduceIte,
        BitVec.sshiftRight_eq_of_msb_true hm]
  · have e : (v.bits.sshiftRight s &&& (AInt.ofInt 255).bits) =
        (v.bits >>> s &&& (AInt.ofInt 255).bits) := by
      ext i hi
      simp only [BitVec.getElem_and, BitVec.getElem_sshiftRight, BitVec.getElem_ushiftRight]
      by_cases h : s + i < 64
      · simp only [h, ↓reduceDIte, BitVec.getLsbD_eq_getElem]
      · have h255 : (AInt.ofInt 255).bits = BitVec.ofNat 64 255 := rfl
        have hb : (BitVec.ofNat 64 255)[i] = false := by
          rw [BitVec.getElem_eq_testBit_toNat]
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 255 < 2 ^ 8)
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp only [h255, hb, Bool.and_false]
    show (v.bits.sshiftRight s &&& (AInt.ofInt 255).bits).toNat = _
    rw [e, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have : (AInt.ofInt 255).bits.toNat = 2 ^ 8 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- `v & 255` is the low byte of the 64 bits of `v`. -/
theorem and_255 (v : AInt) :
    (AInt.bit_and v (AInt.ofInt 255)).bits.toNat = v.bits.toNat % 256 := by
  rw [AInt.toNat_bit_and]
  have : (AInt.ofInt 255).bits.toNat = 2 ^ 8 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

/-- `pack` of items below 256 never halts and is their bytes. -/
theorem pack_eq (items : List AInt) (h : ∀ x ∈ items, x.bits.toNat < 256)
    (hl : items.length < 2 ^ 63) :
    pack items =
      pure ⟨(items.map fun x => x.bits.toNat.toUInt8).toArray, by simpa using hl⟩ := by
  have hb : ∀ x ∈ items, 0 ≤ x.bits.toInt ∧ x.bits.toInt ≤ 255 := by
    intro x hx
    have := h x hx
    have := AInt.toInt_ofNat_of_lt (n := x.bits.toNat) (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    omega
  rw [pack, Bytes.from_list_ok items hb hl]
  rfl

/-- `bytes2_le` never halts and is the low 2 bytes of the 64 bits of `v`,
little-endian. -/
theorem bytes2_le_eq (v : AInt) :
    ∃ b, bytes2_le v = pure b ∧ b.data.size = 2 ∧
      b.byte 0 = v.bits.toNat % 256 ∧
      b.byte 1 = v.bits.toNat / 2 ^ 8 % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  simp only [bytes2_le, h8, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- `bytes2_be` never halts and is the low 2 bytes of the 64 bits of `v`,
big-endian. -/
theorem bytes2_be_eq (v : AInt) :
    ∃ b, bytes2_be v = pure b ∧ b.data.size = 2 ∧
      b.byte 0 = v.bits.toNat / 2 ^ 8 % 256 ∧
      b.byte 1 = v.bits.toNat % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  simp only [bytes2_be, h8, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- `bytes4_le` never halts and is the low 4 bytes of the 64 bits of `v`,
little-endian. -/
theorem bytes4_le_eq (v : AInt) :
    ∃ b, bytes4_le v = pure b ∧ b.data.size = 4 ∧
      b.byte 0 = v.bits.toNat % 256 ∧
      b.byte 1 = v.bits.toNat / 2 ^ 8 % 256 ∧
      b.byte 2 = v.bits.toNat / 2 ^ 16 % 256 ∧
      b.byte 3 = v.bits.toNat / 2 ^ 24 % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  obtain ⟨c16, h16, l16⟩ := shift_and v 16 (by omega)
  replace h16 : AInt.shift_right v (AInt.ofInt 16) = .ok c16 := h16
  obtain ⟨c24, h24, l24⟩ := shift_and v 24 (by omega)
  replace h24 : AInt.shift_right v (AInt.ofInt 24) = .ok c24 := h24
  simp only [bytes4_le, h8, h16, h24, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- `bytes4_be` never halts and is the low 4 bytes of the 64 bits of `v`,
big-endian. -/
theorem bytes4_be_eq (v : AInt) :
    ∃ b, bytes4_be v = pure b ∧ b.data.size = 4 ∧
      b.byte 0 = v.bits.toNat / 2 ^ 24 % 256 ∧
      b.byte 1 = v.bits.toNat / 2 ^ 16 % 256 ∧
      b.byte 2 = v.bits.toNat / 2 ^ 8 % 256 ∧
      b.byte 3 = v.bits.toNat % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  obtain ⟨c16, h16, l16⟩ := shift_and v 16 (by omega)
  replace h16 : AInt.shift_right v (AInt.ofInt 16) = .ok c16 := h16
  obtain ⟨c24, h24, l24⟩ := shift_and v 24 (by omega)
  replace h24 : AInt.shift_right v (AInt.ofInt 24) = .ok c24 := h24
  simp only [bytes4_be, h8, h16, h24, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- `bytes8_le` never halts and is the low 8 bytes of the 64 bits of `v`,
little-endian. -/
theorem bytes8_le_eq (v : AInt) :
    ∃ b, bytes8_le v = pure b ∧ b.data.size = 8 ∧
      b.byte 0 = v.bits.toNat % 256 ∧
      b.byte 1 = v.bits.toNat / 2 ^ 8 % 256 ∧
      b.byte 2 = v.bits.toNat / 2 ^ 16 % 256 ∧
      b.byte 3 = v.bits.toNat / 2 ^ 24 % 256 ∧
      b.byte 4 = v.bits.toNat / 2 ^ 32 % 256 ∧
      b.byte 5 = v.bits.toNat / 2 ^ 40 % 256 ∧
      b.byte 6 = v.bits.toNat / 2 ^ 48 % 256 ∧
      b.byte 7 = v.bits.toNat / 2 ^ 56 % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  obtain ⟨c16, h16, l16⟩ := shift_and v 16 (by omega)
  replace h16 : AInt.shift_right v (AInt.ofInt 16) = .ok c16 := h16
  obtain ⟨c24, h24, l24⟩ := shift_and v 24 (by omega)
  replace h24 : AInt.shift_right v (AInt.ofInt 24) = .ok c24 := h24
  obtain ⟨c32, h32, l32⟩ := shift_and v 32 (by omega)
  replace h32 : AInt.shift_right v (AInt.ofInt 32) = .ok c32 := h32
  obtain ⟨c40, h40, l40⟩ := shift_and v 40 (by omega)
  replace h40 : AInt.shift_right v (AInt.ofInt 40) = .ok c40 := h40
  obtain ⟨c48, h48, l48⟩ := shift_and v 48 (by omega)
  replace h48 : AInt.shift_right v (AInt.ofInt 48) = .ok c48 := h48
  obtain ⟨c56, h56, l56⟩ := shift_and v 56 (by omega)
  replace h56 : AInt.shift_right v (AInt.ofInt 56) = .ok c56 := h56
  simp only [bytes8_le, h8, h16, h24, h32, h40, h48, h56, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- `bytes8_be` never halts and is the low 8 bytes of the 64 bits of `v`,
big-endian. -/
theorem bytes8_be_eq (v : AInt) :
    ∃ b, bytes8_be v = pure b ∧ b.data.size = 8 ∧
      b.byte 0 = v.bits.toNat / 2 ^ 56 % 256 ∧
      b.byte 1 = v.bits.toNat / 2 ^ 48 % 256 ∧
      b.byte 2 = v.bits.toNat / 2 ^ 40 % 256 ∧
      b.byte 3 = v.bits.toNat / 2 ^ 32 % 256 ∧
      b.byte 4 = v.bits.toNat / 2 ^ 24 % 256 ∧
      b.byte 5 = v.bits.toNat / 2 ^ 16 % 256 ∧
      b.byte 6 = v.bits.toNat / 2 ^ 8 % 256 ∧
      b.byte 7 = v.bits.toNat % 256 := by
  have l := and_255 v
  obtain ⟨c8, h8, l8⟩ := shift_and v 8 (by omega)
  replace h8 : AInt.shift_right v (AInt.ofInt 8) = .ok c8 := h8
  obtain ⟨c16, h16, l16⟩ := shift_and v 16 (by omega)
  replace h16 : AInt.shift_right v (AInt.ofInt 16) = .ok c16 := h16
  obtain ⟨c24, h24, l24⟩ := shift_and v 24 (by omega)
  replace h24 : AInt.shift_right v (AInt.ofInt 24) = .ok c24 := h24
  obtain ⟨c32, h32, l32⟩ := shift_and v 32 (by omega)
  replace h32 : AInt.shift_right v (AInt.ofInt 32) = .ok c32 := h32
  obtain ⟨c40, h40, l40⟩ := shift_and v 40 (by omega)
  replace h40 : AInt.shift_right v (AInt.ofInt 40) = .ok c40 := h40
  obtain ⟨c48, h48, l48⟩ := shift_and v 48 (by omega)
  replace h48 : AInt.shift_right v (AInt.ofInt 48) = .ok c48 := h48
  obtain ⟨c56, h56, l56⟩ := shift_and v 56 (by omega)
  replace h56 : AInt.shift_right v (AInt.ofInt 56) = .ok c56 := h56
  simp only [bytes8_be, h8, h16, h24, h32, h40, h48, h56, bind, Except.bind]
  rw [pack_eq _ (by simp; omega) (by simp)]
  refine ⟨_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Bytes.byte] <;> omega

/-- In range, `fits` is `ok`. -/
theorem fits_ok (value low high : AInt) (type : String)
    (h0 : low.bits.toInt ≤ value.bits.toInt) (h1 : value.bits.toInt ≤ high.bits.toInt) :
    fits value low high type = pure (.ok ()) := by
  have : (if AInt.lt value low then true else AInt.gt value high) = false := by
    simp only [AInt.lt, AInt.gt, decide_eq_true_eq]; split <;> simp <;> omega
  simp only [fits, this, Bool.false_eq_true, ↓reduceIte]

/-- Out of range, `fits` is the documented error. -/
theorem fits_out (value low high : AInt) (type : String)
    (h : value.bits.toInt < low.bits.toInt ∨ high.bits.toInt < value.bits.toInt) :
    fits value low high type = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int value ++ " does not fit in " ++ type) }) := by
  have : (if AInt.lt value low then true else AInt.gt value high) = true := by
    simp only [AInt.lt, AInt.gt, decide_eq_true_eq]; split <;> simp <;> omega
  simp only [fits, this, ↓reduceIte]

/-- Two `Int` values with the same signed value are equal. -/
theorem aint_eq (a b : AInt) (h : a.bits.toInt = b.bits.toInt) : a = b := by
  cases a; cases b; congr; exact BitVec.eq_of_toInt_eq h

/-- The signed value of 64 bits is the unsigned one, or that minus `2^64`. -/
theorem toInt_cases (v : AInt) :
    (v.bits.toInt = v.bits.toNat ∧ v.bits.toNat < 2 ^ 63) ∨
      (v.bits.toInt = v.bits.toNat - 2 ^ 64 ∧ 2 ^ 63 ≤ v.bits.toNat ∧
        v.bits.toNat < 2 ^ 64) := by
  have := v.bits.isLt
  rw [BitVec.toInt_eq_toNat_cond]
  split <;> omega

/-- The eight bytes of a 64-bit number, added back, are the number. -/
theorem digits8 (n : Nat) (h : n < 2 ^ 64) :
    n % 256 + 2 ^ 8 * (n / 2 ^ 8 % 256) + 2 ^ 16 * (n / 2 ^ 16 % 256) +
      2 ^ 24 * (n / 2 ^ 24 % 256) + 2 ^ 32 * (n / 2 ^ 32 % 256) + 2 ^ 40 * (n / 2 ^ 40 % 256) +
      2 ^ 48 * (n / 2 ^ 48 % 256) + 2 ^ 56 * (n / 2 ^ 56 % 256) = n := by
  omega

/-- Out of range, `write_u8` never halts and gives the documented error. -/
theorem write_u8_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 255 < v.bits.toInt) :
    write_u8 v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u8") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 255).bits.toInt = 255 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 255) "u8" (by omega)
  simp only [write_u8, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_i8` never halts and gives the documented error. -/
theorem write_i8_out_of_range (v : AInt)
    (h : v.bits.toInt < -128 ∨ 127 < v.bits.toInt) :
    write_i8 v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in i8") }) := by
  have hn : AInt.neg (AInt.ofInt 128) = .ok (AInt.ofInt (-128)) := rfl
  have hl : (AInt.ofInt (-128)).bits.toInt = -128 := by decide
  have hh : (AInt.ofInt 127).bits.toInt = 127 := by decide
  have hf := fits_out v (AInt.ofInt (-128)) (AInt.ofInt 127) "i8" (by omega)
  simp only [write_i8, hn, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u16_be` never halts and gives the documented error. -/
theorem write_u16_be_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 65535 < v.bits.toInt) :
    write_u16_be v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u16") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 65535).bits.toInt = 65535 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 65535) "u16" (by omega)
  simp only [write_u16_be, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_i16_be` never halts and gives the documented error. -/
theorem write_i16_be_out_of_range (v : AInt)
    (h : v.bits.toInt < -32768 ∨ 32767 < v.bits.toInt) :
    write_i16_be v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in i16") }) := by
  have hn : AInt.neg (AInt.ofInt 32768) = .ok (AInt.ofInt (-32768)) := rfl
  have hl : (AInt.ofInt (-32768)).bits.toInt = -32768 := by decide
  have hh : (AInt.ofInt 32767).bits.toInt = 32767 := by decide
  have hf := fits_out v (AInt.ofInt (-32768)) (AInt.ofInt 32767) "i16" (by omega)
  simp only [write_i16_be, hn, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u16_le` never halts and gives the documented error. -/
theorem write_u16_le_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 65535 < v.bits.toInt) :
    write_u16_le v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u16") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 65535).bits.toInt = 65535 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 65535) "u16" (by omega)
  simp only [write_u16_le, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_i16_le` never halts and gives the documented error. -/
theorem write_i16_le_out_of_range (v : AInt)
    (h : v.bits.toInt < -32768 ∨ 32767 < v.bits.toInt) :
    write_i16_le v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in i16") }) := by
  have hn : AInt.neg (AInt.ofInt 32768) = .ok (AInt.ofInt (-32768)) := rfl
  have hl : (AInt.ofInt (-32768)).bits.toInt = -32768 := by decide
  have hh : (AInt.ofInt 32767).bits.toInt = 32767 := by decide
  have hf := fits_out v (AInt.ofInt (-32768)) (AInt.ofInt 32767) "i16" (by omega)
  simp only [write_i16_le, hn, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u32_be` never halts and gives the documented error. -/
theorem write_u32_be_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 4294967295 < v.bits.toInt) :
    write_u32_be v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u32") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 4294967295) "u32" (by omega)
  simp only [write_u32_be, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_i32_be` never halts and gives the documented error. -/
theorem write_i32_be_out_of_range (v : AInt)
    (h : v.bits.toInt < -2147483648 ∨ 2147483647 < v.bits.toInt) :
    write_i32_be v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in i32") }) := by
  have hn : AInt.neg (AInt.ofInt 2147483648) = .ok (AInt.ofInt (-2147483648)) := rfl
  have hl : (AInt.ofInt (-2147483648)).bits.toInt = -2147483648 := by decide
  have hh : (AInt.ofInt 2147483647).bits.toInt = 2147483647 := by decide
  have hf := fits_out v (AInt.ofInt (-2147483648)) (AInt.ofInt 2147483647) "i32" (by omega)
  simp only [write_i32_be, hn, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u32_le` never halts and gives the documented error. -/
theorem write_u32_le_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 4294967295 < v.bits.toInt) :
    write_u32_le v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u32") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 4294967295) "u32" (by omega)
  simp only [write_u32_le, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_i32_le` never halts and gives the documented error. -/
theorem write_i32_le_out_of_range (v : AInt)
    (h : v.bits.toInt < -2147483648 ∨ 2147483647 < v.bits.toInt) :
    write_i32_le v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in i32") }) := by
  have hn : AInt.neg (AInt.ofInt 2147483648) = .ok (AInt.ofInt (-2147483648)) := rfl
  have hl : (AInt.ofInt (-2147483648)).bits.toInt = -2147483648 := by decide
  have hh : (AInt.ofInt 2147483647).bits.toInt = 2147483647 := by decide
  have hf := fits_out v (AInt.ofInt (-2147483648)) (AInt.ofInt 2147483647) "i32" (by omega)
  simp only [write_i32_le, hn, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u64_be` never halts and gives the documented error. -/
theorem write_u64_be_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 9223372036854775807 < v.bits.toInt) :
    write_u64_be v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u64") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 9223372036854775807).bits.toInt = 9223372036854775807 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 9223372036854775807) "u64" (by omega)
  simp only [write_u64_be, hf, bind, Except.bind, String.append_assoc]
  rfl

/-- Out of range, `write_u64_le` never halts and gives the documented error. -/
theorem write_u64_le_out_of_range (v : AInt)
    (h : v.bits.toInt < 0 ∨ 9223372036854775807 < v.bits.toInt) :
    write_u64_le v = pure (.error { kind := "argument", message := (
      "value " ++ String.from_int v ++ " does not fit in u64") }) := by
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 9223372036854775807).bits.toInt = 9223372036854775807 := by decide
  have hf := fits_out v (AInt.ofInt 0) (AInt.ofInt 9223372036854775807) "u64" (by omega)
  simp only [write_u64_le, hf, bind, Except.bind, String.append_assoc]
  rfl

end Agentica.Std.Binary
