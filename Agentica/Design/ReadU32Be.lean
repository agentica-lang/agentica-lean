import Agentica.Design.ReadU32Le

/-!
# Design target: `read_u32_be`, translated by hand

A hand translation of `load32_be` and `read_u32_be` of `stdlib/binary.agc`
(agentica 0.27.0), with the rules of `ReadU16Le.lean`. It is `load32_le` with
the bytes in the other order, so `or_bytes4` of `ReadU32Le.lean` proves it too.

```ruby
def load32_be(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 4, type)
  a = data[offset]
  b = data[offset + 1]
  c = data[offset + 2]
  d = data[offset + 3]
  return ok(a.shift_left(24).bit_or(b.shift_left(16)).bit_or(c.shift_left(8)).bit_or(d))
end

export def read_u32_be(data: Bytes, offset: Int) -> Result[Int]
  return load32_be(data, offset, "u32")
end
```
-/

namespace Agentica.Design

def load32_be (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
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
  let s1 ← Agentica.AInt.shift_left a (Agentica.AInt.ofInt 24)
  let s2 ← Agentica.AInt.shift_left b (Agentica.AInt.ofInt 16)
  let o1 := Agentica.AInt.bit_or s1 s2
  let s3 ← Agentica.AInt.shift_left c (Agentica.AInt.ofInt 8)
  let o2 := Agentica.AInt.bit_or o1 s3
  return .ok (Agentica.AInt.bit_or o2 d)

def read_u32_be (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load32_be data offset "u32"

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
    load32_be data offset type = pure (.ok ⟨BitVec.ofNat 64 (be32 data offset.bits.toNat)⟩) := by
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
    read_u32_be data offset = pure (.error ("u32 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_u32_be, load32_be, window_out data offset _ "u32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
