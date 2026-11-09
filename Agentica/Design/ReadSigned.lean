import Agentica.Design.ReadU32Le
import Agentica.Prelude.Int.ShiftRight

/-!
# Design target: the signed readers, translated by hand

A hand translation of `extend`, `read_i16_le` and `read_i32_le` of
`stdlib/binary.agc` (agentica 0.27.0), with the rules of `ReadU16Le.lean`.
`extend` moves the sign bit of a `bits`-bit value to bit 63 and back with an
arithmetic shift.

```ruby
def extend(value: Int, bits: Int) -> Int
  return value.shift_left(64 - bits).shift_right(64 - bits)
end

export def read_i16_le(data: Bytes, offset: Int) -> Result[Int]
  value = try load16_le(data, offset, "i16")
  return ok(extend(value, 16))
end

export def read_i32_le(data: Bytes, offset: Int) -> Result[Int]
  value = try load32_le(data, offset, "i32")
  return ok(extend(value, 32))
end
```
-/

namespace Agentica.Design

def extend (value bits : AInt) : M AInt := do
  let k1 ← Agentica.AInt.sub (Agentica.AInt.ofInt 64) bits
  let s ← Agentica.AInt.shift_left value k1
  let k2 ← Agentica.AInt.sub (Agentica.AInt.ofInt 64) bits
  Agentica.AInt.shift_right s k2

def read_i16_le (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load16_le data offset "i16" with
  | .error message => return .error message
  | .ok value =>
    let v ← extend value (Agentica.AInt.ofInt 16)
    return .ok v

def read_i32_le (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load32_le data offset "i32" with
  | .error message => return .error message
  | .ok value =>
    let v ← extend value (Agentica.AInt.ofInt 32)
    return .ok v

/-- `extend v n` for `0 < n < 64` never halts: it shifts `v` left by `64 - n`
and back, so the result is the signed 64-bit value of `v * 2^(64-n)`,
divided by `2^(64-n)`. -/
theorem extend_core (v n : Nat) (hn : 0 < n) (hn64 : n < 64) (hv : v < 2 ^ 64) :
    ∃ c, extend ⟨BitVec.ofNat 64 v⟩ (AInt.ofInt n) = pure c ∧
      c.bits.toInt = (BitVec.ofNat 64 (v * 2 ^ (64 - n))).toInt / ((2 ^ (64 - n) : Nat) : Int) := by
  have hni : (AInt.ofInt n).bits.toInt = n := AInt.ofInt_toInt (by omega)
  have h64 : (AInt.ofInt 64).bits.toInt = 64 := AInt.ofInt_toInt (n := 64) (by omega)
  obtain ⟨k, hk, hkv⟩ := AInt.sub_ok (AInt.ofInt 64) (AInt.ofInt n) (by omega) (by omega)
  have hkn : k.bits.toInt = ((64 - n : Nat) : Int) := by omega
  have hl := AInt.shift_left_of_lt_64 ⟨BitVec.ofNat 64 v⟩ k (64 - n) hkn (by omega)
  obtain ⟨c, hc, hcv⟩ := AInt.shift_right_eq_div
    ⟨BitVec.ofNat 64 ((BitVec.ofNat 64 v).toNat * 2 ^ (64 - n))⟩ k (64 - n) hkn (by omega)
  refine ⟨c, ?_, ?_⟩
  · simp only [extend, hk, pure_bind]
    rw [hl]
    exact hc
  · rw [hcv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

/-- `extend v 16` of a 16-bit `v` is its two's complement value. -/
theorem extend_16 (v : Nat) (hv : v < 2 ^ 16) :
    ∃ c, extend ⟨BitVec.ofNat 64 v⟩ (AInt.ofInt 16) = pure c ∧
      c.bits.toInt = if v < 2 ^ 15 then (v : Int) else v - 2 ^ 16 := by
  obtain ⟨c, hc, hv'⟩ := extend_core v 16 (by omega) (by omega) (by omega)
  refine ⟨c, by simpa using hc, ?_⟩
  rw [hv', BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> split <;> omega

/-- `extend v 32` of a 32-bit `v` is its two's complement value. -/
theorem extend_32 (v : Nat) (hv : v < 2 ^ 32) :
    ∃ c, extend ⟨BitVec.ofNat 64 v⟩ (AInt.ofInt 32) = pure c ∧
      c.bits.toInt = if v < 2 ^ 31 then (v : Int) else v - 2 ^ 32 := by
  obtain ⟨c, hc, hv'⟩ := extend_core v 32 (by omega) (by omega) (by omega)
  refine ⟨c, by simpa using hc, ?_⟩
  rw [hv', BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> split <;> omega

/-- In range, `read_i16_le` never halts and is the two's complement value of
`v = b0 + 256 * b1`: `v` below `2^15`, else `v - 2^16`. -/
theorem read_i16_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    let v : Nat := data.byte offset.bits.toNat + 256 * data.byte (offset.bits.toNat + 1)
    ∃ c, read_i16_le data offset = pure (.ok c) ∧
      c.bits.toInt = if v < 2 ^ 15 then (v : Int) else v - 2 ^ 16 := by
  intro v
  have := Bytes.byte_lt data offset.bits.toNat
  have := Bytes.byte_lt data (offset.bits.toNat + 1)
  obtain ⟨c, hc, hcv⟩ := extend_16 v (by omega)
  refine ⟨c, ?_, hcv⟩
  rw [read_i16_le, load16_le_in_range data offset "i16" h0 h2]
  simp only [pure_bind]
  rw [hc]
  rfl

/-- In range, `read_i32_le` never halts and is the two's complement value of
the 32-bit little-endian `v`: `v` below `2^31`, else `v - 2^32`. -/
theorem read_i32_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    let v : Nat := data.byte offset.bits.toNat + 2 ^ 8 * data.byte (offset.bits.toNat + 1) +
      2 ^ 16 * data.byte (offset.bits.toNat + 2) + 2 ^ 24 * data.byte (offset.bits.toNat + 3)
    ∃ c, read_i32_le data offset = pure (.ok c) ∧
      c.bits.toInt = if v < 2 ^ 31 then (v : Int) else v - 2 ^ 32 := by
  intro v
  have lt := Bytes.byte_lt data
  have := lt offset.bits.toNat
  have := lt (offset.bits.toNat + 1)
  have := lt (offset.bits.toNat + 2)
  have := lt (offset.bits.toNat + 3)
  obtain ⟨c, hc, hcv⟩ := extend_32 v (by omega)
  refine ⟨c, ?_, hcv⟩
  rw [read_i32_le, load32_le_in_range data offset "i32" h0 h4]
  simp only [pure_bind]
  rw [hc]
  rfl

/-- Out of range, `read_i16_le` never halts and gives the documented error. -/
theorem read_i16_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 2) :
    read_i16_le data offset = pure (.error ("i16 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  rw [read_i16_le, load16_le, window_out data offset _ "i16" (by omega) (by omega)
    (by omega)]
  rfl

/-- Out of range, `read_i32_le` never halts and gives the documented error. -/
theorem read_i32_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_i32_le data offset = pure (.error ("i32 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_i32_le, load32_le, window_out data offset _ "i32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
