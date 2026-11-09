import Agentica.Design.ReadU32Le

/-!
# Design target: `read_u64_le` and `read_i64_le`, translated by hand

A hand translation of `load64_le`, `unsigned64`, `read_u64_le` and
`read_i64_le` of `stdlib/binary.agc` (agentica 0.27.0), with the rules of
`ReadU16Le.lean`. `try e` followed by more code is a `match` whose `ok` arm
holds the rest.

```ruby
def load64_le(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 8, type)
  a = data[offset]
  ...
  h = data[offset + 7]
  low = d.shift_left(24).bit_or(c.shift_left(16)).bit_or(b.shift_left(8)).bit_or(a)
  high = h.shift_left(24).bit_or(g.shift_left(16)).bit_or(f.shift_left(8)).bit_or(e)
  return ok(high.shift_left(32).bit_or(low))
end

def unsigned64(value: Int, offset: Int) -> Result[Int]
  if value < 0
    return error("u64 at offset #{offset} does not fit in Int")
  end
  return ok(value)
end

export def read_u64_le(data: Bytes, offset: Int) -> Result[Int]
  value = try load64_le(data, offset, "u64")
  return unsigned64(value, offset)
end

export def read_i64_le(data: Bytes, offset: Int) -> Result[Int]
  return load64_le(data, offset, "i64")
end
```
-/

namespace Agentica.Design

def load64_le (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
  match ← window data offset (Agentica.AInt.ofInt 8) type with
  | .error message => return .error message
  | .ok _ => pure ()
  let a ← Agentica.Bytes.at data offset
  let i1 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 1)
  let b ← Agentica.Bytes.at data i1
  let i2 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 2)
  let c ← Agentica.Bytes.at data i2
  let i3 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 3)
  let d ← Agentica.Bytes.at data i3
  let i4 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 4)
  let e ← Agentica.Bytes.at data i4
  let i5 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 5)
  let f ← Agentica.Bytes.at data i5
  let i6 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 6)
  let g ← Agentica.Bytes.at data i6
  let i7 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 7)
  let h ← Agentica.Bytes.at data i7
  let s1 ← Agentica.AInt.shift_left d (Agentica.AInt.ofInt 24)
  let s2 ← Agentica.AInt.shift_left c (Agentica.AInt.ofInt 16)
  let o1 := Agentica.AInt.bit_or s1 s2
  let s3 ← Agentica.AInt.shift_left b (Agentica.AInt.ofInt 8)
  let o2 := Agentica.AInt.bit_or o1 s3
  let low := Agentica.AInt.bit_or o2 a
  let t1 ← Agentica.AInt.shift_left h (Agentica.AInt.ofInt 24)
  let t2 ← Agentica.AInt.shift_left g (Agentica.AInt.ofInt 16)
  let p1 := Agentica.AInt.bit_or t1 t2
  let t3 ← Agentica.AInt.shift_left f (Agentica.AInt.ofInt 8)
  let p2 := Agentica.AInt.bit_or p1 t3
  let high := Agentica.AInt.bit_or p2 e
  let u ← Agentica.AInt.shift_left high (Agentica.AInt.ofInt 32)
  return .ok (Agentica.AInt.bit_or u low)

def unsigned64 (value offset : AInt) : M (Result AInt) := do
  if Agentica.AInt.lt value (Agentica.AInt.ofInt 0) then
    return .error ("u64 at offset " ++ Agentica.String.from_int offset ++ " does not fit in Int")
  return .ok value

def read_u64_le (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load64_le data offset "u64" with
  | .error message => return .error message
  | .ok value => unsigned64 value offset

def read_i64_le (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load64_le data offset "i64"

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
  have s8 := shift_left_lit 8 (by omega)
  have s16 := shift_left_lit 16 (by omega)
  have s24 := shift_left_lit 24 (by omega)
  have s32 := shift_left_lit 32 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 a2 a3 a4 a5 a6 a7 s8 s16 s24 s32
  rw [load64_le, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, a2, b2, a3, b3, a4, b4, a5, b5, a6, b6, a7, b7, s8, s16,
    s24, s32, AInt.bit_or]
  have lt := Bytes.byte_lt data
  rw [AInt.or_bytes4 _ _ _ _ (lt _) (lt _) (lt _) (lt _),
    AInt.or_bytes4 _ _ _ _ (lt _) (lt _) (lt _) (lt _)]
  have := lt offset.bits.toNat
  have := lt (offset.bits.toNat + 1)
  have := lt (offset.bits.toNat + 2)
  have := lt (offset.bits.toNat + 3)
  have := lt (offset.bits.toNat + 4)
  have := lt (offset.bits.toNat + 5)
  have := lt (offset.bits.toNat + 6)
  have := lt (offset.bits.toNat + 7)
  rw [AInt.or_halves _ _ (by omega) (by omega)]
  rfl

/-- In range, `read_i64_le` never halts and is the little-endian value read as
two's complement (`toInt` of the 64 bits). -/
theorem read_i64_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    read_i64_le data offset = pure (.ok ⟨BitVec.ofNat 64 (le64 data offset.bits.toNat)⟩) :=
  load64_le_in_range data offset "i64" h0 h8

/-- In range, `read_u64_le` never halts. When the top byte is below 128 it is
the little-endian value; otherwise the value is above `Int.MAX` and it is the
documented error. -/
theorem read_u64_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    read_u64_le data offset =
      if data.byte (offset.bits.toNat + 7) < 128 then
        pure (.ok ⟨BitVec.ofNat 64 (le64 data offset.bits.toNat)⟩)
      else
        pure (.error ("u64 at offset " ++ String.from_int offset ++ " does not fit in Int")) := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  have lt := Bytes.byte_lt data
  have hsum : le64 data offset.bits.toNat < 2 ^ 64 := by
    have := lt offset.bits.toNat
    have := lt (offset.bits.toNat + 1)
    have := lt (offset.bits.toNat + 2)
    have := lt (offset.bits.toNat + 3)
    have := lt (offset.bits.toNat + 4)
    have := lt (offset.bits.toNat + 5)
    have := lt (offset.bits.toNat + 6)
    have := lt (offset.bits.toNat + 7)
    unfold le64; omega
  have hneg : (BitVec.ofNat 64 (le64 data offset.bits.toNat)).toInt < 0 ↔
      ¬ data.byte (offset.bits.toNat + 7) < 128 := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsum]
    have := lt offset.bits.toNat
    have := lt (offset.bits.toNat + 1)
    have := lt (offset.bits.toNat + 2)
    have := lt (offset.bits.toNat + 3)
    have := lt (offset.bits.toNat + 4)
    have := lt (offset.bits.toNat + 5)
    have := lt (offset.bits.toNat + 6)
    have := lt (offset.bits.toNat + 7)
    unfold le64
    split <;> omega
  rw [read_u64_le, load64_le_in_range data offset "u64" h0 h8]
  simp only [pure_bind, unsigned64, AInt.lt, h0i]
  by_cases hb : data.byte (offset.bits.toNat + 7) < 128
  · have : ¬ (BitVec.ofNat 64 (le64 data offset.bits.toNat)).toInt < 0 := by
      rw [hneg]; exact fun h => h hb
    simp only [hb, this, decide_false, ↓reduceIte, Bool.false_eq_true]
  · have : (BitVec.ofNat 64 (le64 data offset.bits.toNat)).toInt < 0 := hneg.mpr hb
    simp only [hb, this, decide_true, ↓reduceIte]

/-- Out of range, `read_u64_le` never halts and gives the documented error. -/
theorem read_u64_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_u64_le data offset = pure (.error ("u64 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_u64_le, load64_le, window_out data offset _ "u64" (by omega) (by omega)
    (by omega)]
  rfl

/-- Out of range, `read_i64_le` never halts and gives the documented error. -/
theorem read_i64_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_i64_le data offset = pure (.error ("i64 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_i64_le, load64_le, window_out data offset _ "i64" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
