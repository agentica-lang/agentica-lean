import Agentica.Design.ReadSigned
import Agentica.Design.ReadU16Be
import Agentica.Design.ReadU32Be

/-!
# Design target: the big-endian signed readers, translated by hand

A hand translation of `read_i16_be` and `read_i32_be` of `stdlib/binary.agc`
(agentica 0.27.0), with the rules of `ReadU16Le.lean`. `extend` is in
`ReadSigned.lean`.

```ruby
export def read_i16_be(data: Bytes, offset: Int) -> Result[Int]
  value = try load16_be(data, offset, "i16")
  return ok(extend(value, 16))
end

export def read_i32_be(data: Bytes, offset: Int) -> Result[Int]
  value = try load32_be(data, offset, "i32")
  return ok(extend(value, 32))
end
```
-/

namespace Agentica.Design

def read_i16_be (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load16_be data offset "i16" with
  | .error message => return .error message
  | .ok value =>
    let v ← extend value (Agentica.AInt.ofInt 16)
    return .ok v

def read_i32_be (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load32_be data offset "i32" with
  | .error message => return .error message
  | .ok value =>
    let v ← extend value (Agentica.AInt.ofInt 32)
    return .ok v

/-- In range, `read_i16_be` never halts and is the two's complement value of
`v = 256 * b0 + b1`: `v` below `2^15`, else `v - 2^16`. -/
theorem read_i16_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    let v : Nat := data.byte (offset.bits.toNat + 1) + 256 * data.byte offset.bits.toNat
    ∃ c, read_i16_be data offset = pure (.ok c) ∧
      c.bits.toInt = if v < 2 ^ 15 then (v : Int) else v - 2 ^ 16 := by
  intro v
  have := Bytes.byte_lt data offset.bits.toNat
  have := Bytes.byte_lt data (offset.bits.toNat + 1)
  obtain ⟨c, hc, hcv⟩ := extend_16 v (by omega)
  refine ⟨c, ?_, hcv⟩
  rw [read_i16_be, load16_be_in_range data offset "i16" h0 h2]
  simp only [pure_bind]
  rw [hc]
  rfl

/-- In range, `read_i32_be` never halts and is the two's complement value of
the big-endian `be32`: below `2^31` it is itself, else it is less `2^32`. -/
theorem read_i32_be_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h4 : offset.bits.toInt + 4 ≤ data.data.size) :
    ∃ c, read_i32_be data offset = pure (.ok c) ∧
      c.bits.toInt = if be32 data offset.bits.toNat < 2 ^ 31
        then (be32 data offset.bits.toNat : Int)
        else be32 data offset.bits.toNat - 2 ^ 32 := by
  obtain ⟨c, hc, hcv⟩ := extend_32 (be32 data offset.bits.toNat) (be32_lt data _)
  refine ⟨c, ?_, hcv⟩
  rw [read_i32_be, load32_be_in_range data offset "i32" h0 h4]
  simp only [pure_bind]
  rw [hc]
  rfl

/-- Out of range, `read_i16_be` never halts and gives the documented error. -/
theorem read_i16_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 2) :
    read_i16_be data offset = pure (.error ("i16 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := AInt.ofInt_toInt (n := 2) (by omega)
  rw [read_i16_be, load16_be, window_out data offset _ "i16" (by omega) (by omega)
    (by omega)]
  rfl

/-- Out of range, `read_i32_be` never halts and gives the documented error. -/
theorem read_i32_be_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 4) :
    read_i32_be data offset = pure (.error ("i32 at offset " ++ String.from_int offset ++
      " is outside bytes of length " ++ String.from_int (Bytes.length data))) := by
  have h4i : (AInt.ofInt 4).bits.toInt = 4 := AInt.ofInt_toInt (n := 4) (by omega)
  rw [read_i32_be, load32_be, window_out data offset _ "i32" (by omega) (by omega)
    (by omega)]
  rfl

end Agentica.Design
