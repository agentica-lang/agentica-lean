import Agentica.Design.ReadSigned

/-!
# Design target: `read_u8` and `read_i8`, translated by hand

A hand translation of `load8`, `read_u8` and `read_i8` of `stdlib/binary.agc`
(agentica 0.31.1), with the rules of `ReadU16Le.lean`. `extend` is in
`ReadSigned.lean`.

```ruby
def load8(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 1, type)
  a = data[offset]
  ok(a)
end

def read_u8(data: Bytes, offset: Int) -> Result[Int] = load8(data, offset, "u8")

def read_i8(data: Bytes, offset: Int) -> Result[Int]
  value = try load8(data, offset, "i8")
  ok(extend(value, 8))
end
```
-/

namespace Agentica.Design

def load8 (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
  match ← window data offset (Agentica.AInt.ofInt 1) type with
  | .error e => return .error e
  | .ok _ => pure ()
  let a ← Agentica.Bytes.at data offset
  return .ok a

def read_u8 (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load8 data offset "u8"

def read_i8 (data : Bytes) (offset : AInt) : M (Result AInt) := do
  match ← load8 data offset "i8" with
  | .error e => return .error e
  | .ok value =>
    let v ← extend value (Agentica.AInt.ofInt 8)
    return .ok v

/-! ## Theorems -/

/-- `load8` in range never halts and is the byte at `offset`. -/
theorem load8_in_range (data : Bytes) (offset : AInt) (type : String)
    (h0 : 0 ≤ offset.bits.toInt) (h1 : offset.bits.toInt + 1 ≤ data.data.size) :
    load8 data offset type =
      pure (.ok ⟨BitVec.ofNat 64 (data.byte offset.bits.toNat)⟩) := by
  have h1i : (AInt.ofInt 1).bits.toInt = 1 := AInt.ofInt_toInt (n := 1) (by omega)
  rw [load8, window_ok data offset _ type (by omega) (by omega) h0 (by omega)]
  simp only [pure_bind, at_byte data offset h0 (by omega)]

/-- `extend v 8` of an 8-bit `v` is its two's complement value. -/
theorem extend_8 (v : Nat) (hv : v < 2 ^ 8) :
    ∃ c, extend ⟨BitVec.ofNat 64 v⟩ (AInt.ofInt 8) = pure c ∧
      c.bits.toInt = if v < 2 ^ 7 then (v : Int) else v - 2 ^ 8 := by
  obtain ⟨c, hc, hv'⟩ := extend_core v 8 (by omega) (by omega) (by omega)
  refine ⟨c, by simpa using hc, ?_⟩
  rw [hv', BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> split <;> omega

/-- In range, `read_u8` never halts and is the byte at `offset`. -/
theorem read_u8_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h1 : offset.bits.toInt + 1 ≤ data.data.size) :
    ∃ c, read_u8 data offset = pure (.ok c) ∧ c.bits.toInt = data.byte offset.bits.toNat := by
  have := Bytes.byte_lt data offset.bits.toNat
  refine ⟨_, load8_in_range data offset "u8" h0 h1, ?_⟩
  exact AInt.toInt_ofNat_of_lt (by omega)

/-- In range, `read_i8` never halts and is the two's complement value of the
byte `v`: `v` below `2^7`, else `v - 2^8`. -/
theorem read_i8_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h1 : offset.bits.toInt + 1 ≤ data.data.size) :
    let v : Nat := data.byte offset.bits.toNat
    ∃ c, read_i8 data offset = pure (.ok c) ∧
      c.bits.toInt = if v < 2 ^ 7 then (v : Int) else v - 2 ^ 8 := by
  intro v
  obtain ⟨c, hc, hcv⟩ := extend_8 v (Bytes.byte_lt data _)
  refine ⟨c, ?_, hcv⟩
  rw [read_i8, load8_in_range data offset "i8" h0 h1]
  simp only [pure_bind]
  rw [hc]
  rfl

/-- Out of range, `read_u8` never halts and gives the documented error. -/
theorem read_u8_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 1) :
    read_u8 data offset = pure (.error { kind := "argument", message := (
      "u8 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h1i : (AInt.ofInt 1).bits.toInt = 1 := AInt.ofInt_toInt (n := 1) (by omega)
  rw [read_u8, load8, window_out data offset _ "u8" (by omega) (by omega) (by omega)]
  rfl

/-- Out of range, `read_i8` never halts and gives the documented error. -/
theorem read_i8_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 1) :
    read_i8 data offset = pure (.error { kind := "argument", message := (
      "i8 at offset " ++ String.from_int offset ++
        " is outside bytes of length " ++ String.from_int (Bytes.length data)) }) := by
  have h1i : (AInt.ofInt 1).bits.toInt = 1 := AInt.ofInt_toInt (n := 1) (by omega)
  rw [read_i8, load8, window_out data offset _ "i8" (by omega) (by omega) (by omega)]
  rfl

end Agentica.Design
