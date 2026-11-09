import Agentica.Prelude.Int

/-!
# Design target: `read_u16_le` of `std/binary`, translated by hand

This file is a **hand translation**. It shows the Lean that the translator of
`docs/translator.md` must write for `window`, `load16_le` and `read_u16_le` of
`stdlib/binary.agc` (agentica 0.27.0), and one proof about it. The tool must
reproduce the three definitions; the file goes away when it does.

The prelude pieces below (`RuntimeError`, `Result`, `Bytes` and the `AInt`
operations) are drafts in this namespace only. Each moves to
`Agentica/Prelude/` in its own PR, with its VM contract. The draft
`RuntimeError` stands in for `Agentica.RuntimeError`: its constructors become
new constructors there, each with its `code`.
-/

namespace Agentica.Design

/-! ## Draft prelude -/

/-- A runtime error that halts the program: its diagnostic code. -/
inductive RuntimeError where
  /-- Signed overflow of `+`, `-`, `*` (`vm/interp.c`, `agc_op_add_i`). -/
  | integerOverflow
  /-- `b[i]` outside the bytes (`vm/bytes.c`, `builtin_at`). -/
  | indexOutOfRange
  /-- A count outside its allowed range, for example a negative shift. -/
  | invalidCount
  deriving DecidableEq, Repr

/-- The diagnostic code, as the VM reports it. -/
def RuntimeError.code : RuntimeError → String
  | .integerOverflow => "RUNTIME-INTEGER-OVERFLOW"
  | .indexOutOfRange => "RUNTIME-INDEX-OUT-OF-RANGE"
  | .invalidCount => "RUNTIME-INVALID-COUNT"

/-- A translated function and a builtin that can halt run in `M`. -/
abbrev M := Except RuntimeError

/-- Agentica `Result[T]`: a value, or an error with its message. It is a value
of the program, unlike `RuntimeError`. -/
inductive Result (α : Type) where
  | ok (value : α)
  | error (message : String)
  deriving DecidableEq, Repr

/-- `a + b`: fails on signed overflow (`vm/interp.c`, `agc_op_add_i`). -/
def AInt.add (a b : AInt) : M AInt :=
  if a.bits.saddOverflow b.bits then .error .integerOverflow else pure ⟨a.bits + b.bits⟩

/-- `a - b`: fails on signed overflow (`vm/interp.c`, `agc_op_sub_i`). -/
def AInt.sub (a b : AInt) : M AInt :=
  if a.bits.ssubOverflow b.bits then .error .integerOverflow else pure ⟨a.bits - b.bits⟩

/-- `a < b`, signed. -/
def AInt.lt (a b : AInt) : Bool := decide (a.bits.toInt < b.bits.toInt)

/-- `a > b`, signed. -/
def AInt.gt (a b : AInt) : Bool := decide (a.bits.toInt > b.bits.toInt)

/-- `Int.bit_or`. -/
def AInt.bit_or (a b : AInt) : AInt := ⟨a.bits ||| b.bits⟩

/-- `Int.shift_left`: the low 64 bits (`vm/numbers.c`,
`builtin_int_shift_left`). -/
def AInt.shift_left (a count : AInt) : M AInt :=
  if count.bits.toInt < 0 then .error .invalidCount
  else if count.bits.toNat ≥ 64 then pure ⟨0⟩
  else pure ⟨a.bits <<< count.bits.toNat⟩

/-- An `Int` in a string interpolation: its decimal digits (`vm/text.c`,
`snprintf` with `PRId64`). -/
def AInt.to_s (a : AInt) : String := toString a.bits.toInt

/-- Agentica `Bytes`. Its size is an `Int`, so it is below `2^63`. -/
structure Bytes where
  data : Array UInt8
  small : data.size < 2 ^ 63

/-- `Bytes.length`, which `data.size` resolves to (`vm/bytes.c`,
`builtin_length`). -/
def Bytes.length (b : Bytes) : AInt := ⟨BitVec.ofNat 64 b.data.size⟩

/-- `b[i]` (`Bytes.at`): the byte at `i`, from 0 to 255 (`vm/bytes.c`,
`builtin_at`). -/
def Bytes.at (b : Bytes) (i : AInt) : M AInt :=
  if h : 0 ≤ i.bits.toInt ∧ i.bits.toInt < b.data.size then
    pure ⟨BitVec.ofNat 64 (b.data[i.bits.toNat]'(by
      rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega)).toNat⟩
  else .error .indexOutOfRange

/-! ## The hand translation

The source, from `stdlib/binary.agc`:

```ruby
def window(data: Bytes, offset: Int, n: Int, type: String) -> Result[Void]
  if offset < 0 or offset > data.size - n
    return error("#{type} at offset #{offset} is outside bytes of length #{data.size}")
  end
  return ok()
end

def load16_le(data: Bytes, offset: Int, type: String) -> Result[Int]
  try window(data, offset, 2, type)
  a = data[offset]
  b = data[offset + 1]
  return ok(b.shift_left(8).bit_or(a))
end

export def read_u16_le(data: Bytes, offset: Int) -> Result[Int]
  return load16_le(data, offset, "u16")
end
```

Each step that can halt is a `←`, in the order of the source. `or` does not
evaluate its right side when the left is true, and `try` returns the error.
`data.size` is the alias of `Bytes.length`: the translator writes the name the
checker resolved.
-/

def window (data : Bytes) (offset n : AInt) (type : String) : M (Result Unit) := do
  let out ← if AInt.lt offset (AInt.ofInt 0) then pure true else do
    let limit ← AInt.sub (Bytes.length data) n
    pure (AInt.gt offset limit)
  if out then
    return .error (type ++ " at offset " ++ AInt.to_s offset ++
      " is outside bytes of length " ++ AInt.to_s (Bytes.length data))
  return .ok ()

def load16_le (data : Bytes) (offset : AInt) (type : String) : M (Result AInt) := do
  match ← window data offset (AInt.ofInt 2) type with
  | .error message => return .error message
  | .ok _ => pure ()
  let a ← Bytes.at data offset
  let i ← AInt.add offset (AInt.ofInt 1)
  let b ← Bytes.at data i
  let s ← AInt.shift_left b (AInt.ofInt 8)
  return .ok (AInt.bit_or s a)

def read_u16_le (data : Bytes) (offset : AInt) : M (Result AInt) :=
  load16_le data offset "u16"

/-! ## Lemmas the prelude would give -/

theorem toInt_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

theorem ofInt_toInt {n : Nat} (h : n < 2 ^ 63) : (AInt.ofInt n).bits.toInt = n := by
  simp only [AInt.ofInt, BitVec.ofInt_natCast]
  exact toInt_ofNat_small h

theorem length_toInt (data : Bytes) : (Bytes.length data).bits.toInt = data.data.size :=
  toInt_ofNat_small data.small

theorem at_ok (data : Bytes) (i : AInt) (h0 : 0 ≤ i.bits.toInt)
    (h1 : i.bits.toInt < data.data.size) :
    Bytes.at data i = pure ⟨BitVec.ofNat 64 (data.data[i.bits.toNat]!).toNat⟩ := by
  have := AInt.toInt_eq_toNat_of_nonneg h0
  have hlt : i.bits.toNat < data.data.size := by omega
  simp only [Bytes.at, h0, h1, and_self, ↓reduceDIte, getElem!_pos data.data i.bits.toNat hlt]

theorem add_ok (a b : AInt) (h : -2 ^ 63 ≤ a.bits.toInt + b.bits.toInt)
    (h' : a.bits.toInt + b.bits.toInt < 2 ^ 63) :
    ∃ c, AInt.add a b = pure c ∧ c.bits.toInt = a.bits.toInt + b.bits.toInt := by
  have hno : ¬ a.bits.saddOverflow b.bits = true := by
    simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  exact ⟨_, by simp only [AInt.add, hno, ↓reduceIte, Bool.false_eq_true],
    BitVec.toInt_add_of_not_saddOverflow hno⟩

theorem sub_ok (a b : AInt) (h : -2 ^ 63 ≤ a.bits.toInt - b.bits.toInt)
    (h' : a.bits.toInt - b.bits.toInt < 2 ^ 63) :
    ∃ c, AInt.sub a b = pure c ∧ c.bits.toInt = a.bits.toInt - b.bits.toInt := by
  have hno : ¬ a.bits.ssubOverflow b.bits = true := by
    simp only [BitVec.ssubOverflow, Bool.or_eq_true, decide_eq_true_eq]; omega
  exact ⟨_, by simp only [AInt.sub, hno, ↓reduceIte, Bool.false_eq_true],
    BitVec.toInt_sub_of_not_ssubOverflow hno⟩

/-- The high byte shifted by 8, ORed with the low byte, is `low + 256 * high`. -/
theorem or_shift_8 (lo hi : Nat) (hlo : lo < 256) (hhi : hi < 256) :
    (BitVec.ofNat 64 hi <<< 8 ||| BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo + 256 * hi) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := hi) (by omega),
    Nat.mod_eq_of_lt (a := lo) (by omega), Nat.mod_eq_of_lt (a := hi * 2 ^ 8) (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm hi, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

/-! ## The theorems -/

/-- In range, `read_u16_le` never halts and is `b0 + 256 * b1`. -/
theorem read_u16_le_in_range (data : Bytes) (offset : AInt)
    (h0 : 0 ≤ offset.bits.toInt) (h2 : offset.bits.toInt + 2 ≤ data.data.size) :
    read_u16_le data offset = pure (.ok ⟨BitVec.ofNat 64
      ((data.data[offset.bits.toNat]!).toNat +
        256 * (data.data[offset.bits.toNat + 1]!).toNat)⟩) := by
  have := data.small
  have := AInt.toInt_eq_toNat_of_nonneg h0
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := ofInt_toInt (n := 2) (by omega)
  have h1i : (AInt.ofInt 1).bits.toInt = 1 := ofInt_toInt (n := 1) (by omega)
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := ofInt_toInt (n := 0) (by omega)
  have hsz := length_toInt data
  obtain ⟨lim, hlim, hlimv⟩ := sub_ok (Bytes.length data) (AInt.ofInt 2) (by omega) (by omega)
  obtain ⟨i, hi, hiv⟩ := add_ok offset (AInt.ofInt 1) (by omega) (by omega)
  have hinat : i.bits.toNat = offset.bits.toNat + 1 := by
    have := AInt.toInt_eq_toNat_of_nonneg (x := i.bits) (by omega)
    omega
  have hlt : ¬ AInt.lt offset (AInt.ofInt 0) = true := by
    simp only [AInt.lt, decide_eq_true_eq]; omega
  have hgt : AInt.gt offset lim = false := by
    simp only [AInt.gt, decide_eq_false_iff_not]; omega
  have hw : window data offset (AInt.ofInt 2) "u16" = pure (.ok ()) := by
    simp only [window, hlt, Bool.false_eq_true, ↓reduceIte, hlim, pure_bind, hgt]
  have ha := at_ok data offset h0 (by omega)
  have hb := at_ok data i (by omega) (by omega)
  rw [hinat] at hb
  have hs : ∀ x : AInt, AInt.shift_left x (AInt.ofInt 8) = pure ⟨x.bits <<< 8⟩ :=
    fun _ => rfl
  rw [read_u16_le, load16_le, hw]
  simp only [pure_bind, ha, hi, hb, hs, AInt.bit_or]
  rw [or_shift_8 _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _)]

/-- Out of range, `read_u16_le` never halts and gives the documented error:
a negative offset, or one where two bytes do not fit (up to `Int.MAX`). -/
theorem read_u16_le_out_of_range (data : Bytes) (offset : AInt)
    (h : offset.bits.toInt < 0 ∨ data.data.size < offset.bits.toInt + 2) :
    read_u16_le data offset = pure (.error ("u16 at offset " ++ AInt.to_s offset ++
      " is outside bytes of length " ++ AInt.to_s (Bytes.length data))) := by
  have := data.small
  have h0i : (AInt.ofInt 0).bits.toInt = 0 := ofInt_toInt (n := 0) (by omega)
  have h2i : (AInt.ofInt 2).bits.toInt = 2 := ofInt_toInt (n := 2) (by omega)
  have hsz := length_toInt data
  by_cases hneg : offset.bits.toInt < 0
  · have hlt : AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    simp only [read_u16_le, load16_le, window, hlt, ↓reduceIte, pure_bind]
    rfl
  · have hlt : ¬ AInt.lt offset (AInt.ofInt 0) = true := by
      simp only [AInt.lt, decide_eq_true_eq]; omega
    obtain ⟨lim, hlim, hlimv⟩ :=
      sub_ok (Bytes.length data) (AInt.ofInt 2) (by omega) (by omega)
    have hgt : AInt.gt offset lim = true := by
      simp only [AInt.gt, decide_eq_true_eq]; omega
    simp only [read_u16_le, load16_le, window, hlt, Bool.false_eq_true, ↓reduceIte, hlim,
      pure_bind, hgt]
    rfl

/-! ## The cases compared with agentica

`Binary.read_u16_le` on the bytes `[1, 2, 255]` printed these results (agentica
0.24.1, by hand); the kernel checks the translation gives the same. -/

/-- The bytes `[1, 2, 255]`. -/
def sample : Bytes := ⟨#[1, 2, 255], by decide⟩

example : read_u16_le sample (AInt.ofInt (-1)) =
    pure (.error "u16 at offset -1 is outside bytes of length 3") := rfl

example : read_u16_le sample (AInt.ofInt 0) = pure (.ok (AInt.ofInt 513)) := rfl

example : read_u16_le sample (AInt.ofInt 1) = pure (.ok (AInt.ofInt 65282)) := rfl

example : read_u16_le sample (AInt.ofInt 2) =
    pure (.error "u16 at offset 2 is outside bytes of length 3") := rfl

example : read_u16_le sample (AInt.ofInt 9223372036854775807) =
    pure (.error "u16 at offset 9223372036854775807 is outside bytes of length 3") := by
  rfl

end Agentica.Design
