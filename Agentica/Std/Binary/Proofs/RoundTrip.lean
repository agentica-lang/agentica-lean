import Agentica.Std.Binary.Proofs.Write
import Agentica.Std.Binary.Proofs.Read8
import Agentica.Std.Binary.Proofs.ReadSignedBe
import Agentica.Std.Binary.Proofs.ReadU64Be
import Agentica.Std.Binary.Proofs.ReadFrameLength

/-!
# Round trips of `std/binary`

Each writer of `Agentica/Std/Binary.lean`, in range, gives bytes that its
reader turns back into the same value.
-/

namespace Agentica.Std.Binary

/-! ## Theorems -/

/-- In range, `write_u8` never halts, and `read_u8` at offset 0 of its bytes
gives the value back. -/
theorem write_u8_round_trip (v : AInt) (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 255) :
    ∃ b, write_u8 v = pure (.ok b) ∧ b.data.size = 1 ∧
      read_u8 b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 255).bits.toInt = 255 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 255) "u8" (by omega) (by omega)
  have l : v.bits.toNat < 256 := by rcases toInt_cases v with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega
  obtain ⟨b, hb, hs, e0⟩ : ∃ b, pack [v] = pure b ∧ b.data.size = 1 ∧
      b.byte 0 = v.bits.toNat % 256 :=
    ⟨_, pack_eq _ (by simp; omega) (by simp), rfl, by simp [Bytes.byte]⟩
  refine ⟨b, by simp only [write_u8, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u8_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z] at hcv
  rw [e0] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_i8` never halts, and `read_i8` at offset 0 of its bytes
gives the value back. -/
theorem write_i8_round_trip (v : AInt) (h0 : -128 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 127) :
    ∃ b, write_i8 v = pure (.ok b) ∧ b.data.size = 1 ∧
      read_i8 b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hn : AInt.neg (AInt.ofInt 128) = .ok (AInt.ofInt (-128)) := rfl
  have hl : (AInt.ofInt (-128)).bits.toInt = -128 := by decide
  have hh : (AInt.ofInt 127).bits.toInt = 127 := by decide
  have hf := fits_ok v (AInt.ofInt (-128)) (AInt.ofInt 127) "i8" (by omega) (by omega)
  have l := and_255 v
  obtain ⟨b, hb, hs, e0⟩ : ∃ b, pack [AInt.bit_and v (AInt.ofInt 255)] = pure b ∧
      b.data.size = 1 ∧
      b.byte 0 = v.bits.toNat % 256 :=
    ⟨_, pack_eq _ (by simp; omega) (by simp), rfl, by simp [Bytes.byte]; omega⟩
  refine ⟨b, by simp only [write_i8, hn, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i8_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z] at hcv
  rw [e0] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u16_be` never halts, and `read_u16_be` at offset 0 of its bytes
gives the value back. -/
theorem write_u16_be_round_trip (v : AInt) (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 65535) :
    ∃ b, write_u16_be v = pure (.ok b) ∧ b.data.size = 2 ∧
      read_u16_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 65535).bits.toInt = 65535 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 65535) "u16" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1⟩ := bytes2_be_eq v
  refine ⟨b, by simp only [write_u16_be, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u16_be_toInt b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_i16_be` never halts, and `read_i16_be` at offset 0 of its bytes
gives the value back. -/
theorem write_i16_be_round_trip (v : AInt)
    (h0 : -32768 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 32767) :
    ∃ b, write_i16_be v = pure (.ok b) ∧ b.data.size = 2 ∧
      read_i16_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hn : AInt.neg (AInt.ofInt 32768) = .ok (AInt.ofInt (-32768)) := rfl
  have hl : (AInt.ofInt (-32768)).bits.toInt = -32768 := by decide
  have hh : (AInt.ofInt 32767).bits.toInt = 32767 := by decide
  have hf := fits_ok v (AInt.ofInt (-32768)) (AInt.ofInt 32767) "i16" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1⟩ := bytes2_be_eq v
  refine ⟨b, by simp only [write_i16_be, hn, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i16_be_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u16_le` never halts, and `read_u16_le` at offset 0 of its bytes
gives the value back. -/
theorem write_u16_le_round_trip (v : AInt) (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 65535) :
    ∃ b, write_u16_le v = pure (.ok b) ∧ b.data.size = 2 ∧
      read_u16_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 65535).bits.toInt = 65535 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 65535) "u16" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1⟩ := bytes2_le_eq v
  refine ⟨b, by simp only [write_u16_le, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u16_le_toInt b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_i16_le` never halts, and `read_i16_le` at offset 0 of its bytes
gives the value back. -/
theorem write_i16_le_round_trip (v : AInt)
    (h0 : -32768 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 32767) :
    ∃ b, write_i16_le v = pure (.ok b) ∧ b.data.size = 2 ∧
      read_i16_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hn : AInt.neg (AInt.ofInt 32768) = .ok (AInt.ofInt (-32768)) := rfl
  have hl : (AInt.ofInt (-32768)).bits.toInt = -32768 := by decide
  have hh : (AInt.ofInt 32767).bits.toInt = 32767 := by decide
  have hf := fits_ok v (AInt.ofInt (-32768)) (AInt.ofInt 32767) "i16" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1⟩ := bytes2_le_eq v
  refine ⟨b, by simp only [write_i16_le, hn, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i16_le_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u32_be` never halts, and `read_u32_be` at offset 0 of its bytes
gives the value back. -/
theorem write_u32_be_round_trip (v : AInt)
    (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 4294967295) :
    ∃ b, write_u32_be v = pure (.ok b) ∧ b.data.size = 4 ∧
      read_u32_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 4294967295) "u32" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3⟩ := bytes4_be_eq v
  refine ⟨b, by simp only [write_u32_be, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u32_be_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, be32] at hcv
  rw [e0, e1, e2, e3] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_i32_be` never halts, and `read_i32_be` at offset 0 of its bytes
gives the value back. -/
theorem write_i32_be_round_trip (v : AInt)
    (h0 : -2147483648 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 2147483647) :
    ∃ b, write_i32_be v = pure (.ok b) ∧ b.data.size = 4 ∧
      read_i32_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hn : AInt.neg (AInt.ofInt 2147483648) = .ok (AInt.ofInt (-2147483648)) := rfl
  have hl : (AInt.ofInt (-2147483648)).bits.toInt = -2147483648 := by decide
  have hh : (AInt.ofInt 2147483647).bits.toInt = 2147483647 := by decide
  have hf := fits_ok v (AInt.ofInt (-2147483648)) (AInt.ofInt 2147483647) "i32"
    (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3⟩ := bytes4_be_eq v
  refine ⟨b, by simp only [write_i32_be, hn, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i32_be_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, be32] at hcv
  rw [e0, e1, e2, e3] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u32_le` never halts, and `read_u32_le` at offset 0 of its bytes
gives the value back. -/
theorem write_u32_le_round_trip (v : AInt)
    (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 4294967295) :
    ∃ b, write_u32_le v = pure (.ok b) ∧ b.data.size = 4 ∧
      read_u32_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 4294967295) "u32" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3⟩ := bytes4_le_eq v
  refine ⟨b, by simp only [write_u32_le, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u32_le_toInt b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1, e2, e3] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_i32_le` never halts, and `read_i32_le` at offset 0 of its bytes
gives the value back. -/
theorem write_i32_le_round_trip (v : AInt)
    (h0 : -2147483648 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 2147483647) :
    ∃ b, write_i32_le v = pure (.ok b) ∧ b.data.size = 4 ∧
      read_i32_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hn : AInt.neg (AInt.ofInt 2147483648) = .ok (AInt.ofInt (-2147483648)) := rfl
  have hl : (AInt.ofInt (-2147483648)).bits.toInt = -2147483648 := by decide
  have hh : (AInt.ofInt 2147483647).bits.toInt = 2147483647 := by decide
  have hf := fits_ok v (AInt.ofInt (-2147483648)) (AInt.ofInt 2147483647) "i32"
    (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3⟩ := bytes4_le_eq v
  refine ⟨b, by simp only [write_i32_le, hn, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i32_le_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add] at hcv
  rw [e0, e1, e2, e3] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u64_le` never halts, and `read_u64_le` at offset 0 of its bytes
gives the value back. -/
theorem write_u64_le_round_trip (v : AInt)
    (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 9223372036854775807) :
    ∃ b, write_u64_le v = pure (.ok b) ∧ b.data.size = 8 ∧
      read_u64_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 9223372036854775807).bits.toInt = 9223372036854775807 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 9223372036854775807) "u64" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytes8_le_eq v
  refine ⟨b, by simp only [write_u64_le, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_u64_le_toInt b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
    (by rw [z, Nat.zero_add, e7]; rcases toInt_cases v with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, le64] at hcv
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- In range, `write_u64_be` never halts, and `read_u64_be` at offset 0 of its bytes
gives the value back. -/
theorem write_u64_be_round_trip (v : AInt)
    (h0 : 0 ≤ v.bits.toInt) (h1 : v.bits.toInt ≤ 9223372036854775807) :
    ∃ b, write_u64_be v = pure (.ok b) ∧ b.data.size = 8 ∧
      read_u64_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  have hl : (AInt.ofInt 0).bits.toInt = 0 := by decide
  have hh : (AInt.ofInt 9223372036854775807).bits.toInt = 9223372036854775807 := by decide
  have hf := fits_ok v (AInt.ofInt 0) (AInt.ofInt 9223372036854775807) "u64" (by omega) (by omega)
  obtain ⟨b, hb, hs, e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytes8_be_eq v
  refine ⟨b, by simp only [write_u64_be, hf, hb, bind, Except.bind]; rfl, hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ :=
    (read_u64_be_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)).1
    (by rw [z, e0]; rcases toInt_cases v with ⟨ha, _⟩ | ⟨ha, _⟩ <;> omega)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, be64] at hcv
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- `write_i64_be` never halts, and `read_i64_be` at offset 0 of its bytes
gives the value back. -/
theorem write_i64_be_round_trip (v : AInt) :
    ∃ b, write_i64_be v = pure b ∧ b.data.size = 8 ∧
      read_i64_be b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  obtain ⟨b, hb, hs, e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytes8_be_eq v
  refine ⟨b, by simp only [write_i64_be, hb], hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i64_be_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, be64] at hcv
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at hcv
  have := digits8 v.bits.toNat v.bits.isLt
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

/-- `write_i64_le` never halts, and `read_i64_le` at offset 0 of its bytes
gives the value back. -/
theorem write_i64_le_round_trip (v : AInt) :
    ∃ b, write_i64_le v = pure b ∧ b.data.size = 8 ∧
      read_i64_le b (AInt.ofInt 0) = pure (.ok v) := by
  have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
  obtain ⟨b, hb, hs, e0, e1, e2, e3, e4, e5, e6, e7⟩ := bytes8_le_eq v
  refine ⟨b, by simp only [write_i64_le, hb], hs, ?_⟩
  obtain ⟨c, hc, hcv⟩ := read_i64_le_in_range b (AInt.ofInt 0) (by decide) (by rw [hs]; decide)
  rw [hc, aint_eq c v ?_]
  simp only [z, Nat.zero_add, le64] at hcv
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at hcv
  rcases toInt_cases v with ⟨ha, hv⟩ | ⟨ha, hv, hv'⟩ <;> (try split at hcv) <;> omega

end Agentica.Std.Binary
