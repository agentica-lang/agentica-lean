import Agentica.Design.ReadU64Le

/-!
# Design target: `read_u64_be` and `read_i64_be`, translated by hand

A hand translation of `load64_be`, `read_u64_be` and `read_i64_be` of
`stdlib/binary.agc` (agentica 0.31.1), with the rules of `ReadU16Le.lean`.
`unsigned64` is in `ReadU64Le.lean`.

```ruby
def load64_be(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 8, type)
  a = data[offset]
  b = data[offset + 1]
  c = data[offset + 2]
  d = data[offset + 3]
  e = data[offset + 4]
  f = data[offset + 5]
  g = data[offset + 6]
  h = data[offset + 7]
  high = a.shift_left(24).bit_or(b.shift_left(16)).bit_or(c.shift_left(8)).bit_or(d)
  low = e.shift_left(24).bit_or(f.shift_left(16)).bit_or(g.shift_left(8)).bit_or(h)
  ok(high.shift_left(32).bit_or(low))
end

def read_u64_be(data: Bytes, offset: Int) -> Result[Int]
  value = try load64_be(data, offset, "u64")
  unsigned64(value, offset)
end

def read_i64_be(data: Bytes, offset: Int) -> Result[Int] = load64_be(data, offset, "i64")
```
-/

namespace Agentica.Design

def load64_be (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
  match ← window data offset (Agentica.AInt.ofInt 8) type with
  | .error e => return .error e
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
  let s1 ← Agentica.AInt.shift_left a (Agentica.AInt.ofInt 24)
  let s2 ← Agentica.AInt.shift_left b (Agentica.AInt.ofInt 16)
  let o1 := Agentica.AInt.bit_or s1 s2
  let s3 ← Agentica.AInt.shift_left c (Agentica.AInt.ofInt 8)
  let o2 := Agentica.AInt.bit_or o1 s3
  let high := Agentica.AInt.bit_or o2 d
  let t1 ← Agentica.AInt.shift_left e (Agentica.AInt.ofInt 24)
  let t2 ← Agentica.AInt.shift_left f (Agentica.AInt.ofInt 16)
  let p1 := Agentica.AInt.bit_or t1 t2
  let t3 ← Agentica.AInt.shift_left g (Agentica.AInt.ofInt 8)
  let p2 := Agentica.AInt.bit_or p1 t3
  let low := Agentica.AInt.bit_or p2 h
  let u ← Agentica.AInt.shift_left high (Agentica.AInt.ofInt 32)
  return .ok (Agentica.AInt.bit_or u low)

def read_u64_be (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load64_be data offset "u64" with
  | .error e => return .error e
  | .ok value => unsigned64 value offset

def read_i64_be (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load64_be data offset "i64"

/-! ## Theorems -/

/-- The eight bytes at `o`, big-endian: `2^56 b0 + ... + 2^8 b6 + b7`. -/
def be64 (data : Bytes) (o : Nat) : Nat :=
  data.byte (o + 7) + 2 ^ 8 * data.byte (o + 6) + 2 ^ 16 * data.byte (o + 5) +
    2 ^ 24 * data.byte (o + 4) + 2 ^ 32 * (data.byte (o + 3) + 2 ^ 8 * data.byte (o + 2) +
    2 ^ 16 * data.byte (o + 1) + 2 ^ 24 * data.byte o)

/-- `be64` fits in 64 bits, and is below `2^63` exactly when the first byte is
below 128. -/
theorem be64_bounds (data : Bytes) (o : Nat) :
    be64 data o < 2 ^ 64 ∧ (be64 data o < 2 ^ 63 ↔ data.byte o < 128) := by
  have lt := Bytes.byte_lt data
  have := lt o
  have := lt (o + 1)
  have := lt (o + 2)
  have := lt (o + 3)
  have := lt (o + 4)
  have := lt (o + 5)
  have := lt (o + 6)
  have := lt (o + 7)
  unfold be64; omega

/-- `load64_be` in range never halts and is the 64 bits of `be64`. -/
theorem load64_be_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    load64_be data offset type =
      pure (.ok ⟨BitVec.ofNat 64 (be64 data offset.bits.toNat)⟩) := by
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
  rw [load64_be, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
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

/-- In range, `read_i64_be` never halts and is the big-endian value read as
two's complement. -/
theorem read_i64_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    ∃ c, read_i64_be data offset = pure (.ok c) ∧
      c.bits.toInt = if be64 data offset.bits.toNat < 2 ^ 63
        then (be64 data offset.bits.toNat : Int)
        else be64 data offset.bits.toNat - 2 ^ 64 := by
  have := (be64_bounds data offset.bits.toNat).1
  refine ⟨_, load64_be_in_range data offset "i64" h0 h8, ?_⟩
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]
  split <;> split <;> omega

/-- In range, `read_u64_be` never halts. When the first byte is below 128 it
is the big-endian value; otherwise the value is above `Int.MAX` and it is the
documented error. -/
theorem read_u64_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h8 : offset.bits.toInt + 8 ≤ data.data.size) :
    (data.byte offset.bits.toNat < 128 → ∃ c, read_u64_be data offset = pure (.ok c) ∧
      c.bits.toInt = be64 data offset.bits.toNat) ∧
    (128 ≤ data.byte offset.bits.toNat → read_u64_be data offset =
      pure (.error { kind := "number.range", message := (
        "u64 at offset " ++ String.from_int offset ++ " does not fit in Int") })) := by
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := AInt.ofInt_toInt (n := 0) (by omega)
  obtain ⟨hlt, hiff⟩ := be64_bounds data offset.bits.toNat
  have ht : (BitVec.ofNat 64 (be64 data offset.bits.toNat)).toInt =
      if be64 data offset.bits.toNat < 2 ^ 63 then (be64 data offset.bits.toNat : Int)
      else be64 data offset.bits.toNat - 2 ^ 64 := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    split <;> split <;> omega
  rw [read_u64_be, load64_be_in_range data offset "u64" h0 h8]
  simp only [pure_bind, unsigned64, AInt.lt, h0i]
  constructor
  · intro hb
    have hpos := hiff.mpr hb
    have : ¬ (BitVec.ofNat 64 (be64 data offset.bits.toNat)).toInt < 0 := by
      rw [ht, ite_eq_left hpos]; omega
    refine ⟨_, by simp only [this, decide_false, ↓reduceIte, Bool.false_eq_true]; rfl, ?_⟩
    rw [ht, ite_eq_left hpos]
  · intro hb
    have : (BitVec.ofNat 64 (be64 data offset.bits.toNat)).toInt < 0 := by
      rw [ht, ite_eq_right (fun h => by have := hiff.mp h; omega)]; omega
    simp only [this, decide_true, ↓reduceIte]

/-- Out of range, `read_u64_be` never halts and gives the documented error. -/
theorem read_u64_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_u64_be data offset = pure (.error { kind := "argument", message := (
      "u64 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_u64_be, load64_be, window_out data offset _ "u64" (by omega) (by omega)
    (by omega)]
  rfl

/-- Out of range, `read_i64_be` never halts and gives the documented error. -/
theorem read_i64_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 8) :
    read_i64_be data offset = pure (.error { kind := "argument", message := (
      "i64 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h8i : (AInt.ofInt 8).bits.toInt = 8 := AInt.ofInt_toInt (n := 8) (by omega)
  rw [read_i64_be, load64_be, window_out data offset _ "i64" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
