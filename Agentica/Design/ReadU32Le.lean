import Agentica.Design.ReadU16Le

/-!
# Design target: `read_u32_le`, translated by hand

A hand translation of `load32_le` and `read_u32_le` of `stdlib/binary.agc`
(agentica 0.27.0), with the rules of `ReadU16Le.lean`. A chain of calls runs
left to right: `d.shift_left(24).bit_or(c.shift_left(16))` shifts `d`, then
`c`, then ORs.

```ruby
def load32_le(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 4, type)
  a = data[offset]
  b = data[offset + 1]
  c = data[offset + 2]
  d = data[offset + 3]
  return ok(d.shift_left(24).bit_or(c.shift_left(16)).bit_or(b.shift_left(8)).bit_or(a))
end

export def read_u32_le(data: Bytes, offset: Int) -> Result[Int]
  return load32_le(data, offset, "u32")
end
```
-/

namespace Agentica.Design

def load32_le (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
  match ← window data offset (Agentica.AInt.ofInt 4) type with
  | .error message => return .error message
  | .ok _ => pure ()
  let a ← Agentica.Bytes.at data offset
  let i1 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 1)
  let b ← Agentica.Bytes.at data i1
  let i2 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 2)
  let c ← Agentica.Bytes.at data i2
  let i3 ← Agentica.AInt.add offset (Agentica.AInt.ofInt 3)
  let d ← Agentica.Bytes.at data i3
  let s1 ← Agentica.AInt.shift_left d (Agentica.AInt.ofInt 24)
  let s2 ← Agentica.AInt.shift_left c (Agentica.AInt.ofInt 16)
  let o1 := Agentica.AInt.bit_or s1 s2
  let s3 ← Agentica.AInt.shift_left b (Agentica.AInt.ofInt 8)
  let o2 := Agentica.AInt.bit_or o1 s3
  return .ok (Agentica.AInt.bit_or o2 a)

def read_u32_le (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load32_le data offset "u32"

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
  have s8 := shift_left_lit 8 (by omega)
  have s16 := shift_left_lit 16 (by omega)
  have s24 := shift_left_lit 24 (by omega)
  simp only [Int.cast_ofNat_Int] at a1 a2 a3 s8 s16 s24
  rw [load32_le, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, ha, a1, b1, a2, b2, a3, b3, s8, s16, s24, AInt.bit_or]
  rw [AInt.or_bytes4 _ _ _ _ (Bytes.byte_lt _ _) (Bytes.byte_lt _ _) (Bytes.byte_lt _ _)
    (Bytes.byte_lt _ _)]

/-- In range, `read_u32_le` never halts and is the little-endian value. -/
theorem read_u32_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    read_u32_le data offset = pure (.ok ⟨BitVec.ofNat 64 (data.byte offset.bits.toNat +
      2 ^ 8 * data.byte (offset.bits.toNat + 1) + 2 ^ 16 * data.byte (offset.bits.toNat + 2) +
      2 ^ 24 * data.byte (offset.bits.toNat + 3))⟩) :=
  load32_le_in_range data offset "u32" h0 h4

/-- Out of range, `read_u32_le` never halts and gives the documented error. -/
theorem read_u32_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_u32_le data offset = pure (.error ("u32 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_u32_le, load32_le, window_out data offset _ "u32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
