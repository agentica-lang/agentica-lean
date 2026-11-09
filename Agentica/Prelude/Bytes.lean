import Agentica.Prelude.Int

/-!
# `Bytes`, `Bytes.length` and `Bytes.at`

An Agentica `Bytes` is a sequence of bytes (`agc_bytes` in `vm/value.h`: a
`size_t len` and the data).

**The size bound.** `Bytes.length` returns `(int64_t)b->len`
(`vm/bytes.c`, `builtin_length`), so the model needs `len < 2^63` for the
length to be the `Int` it should be. The VM has no explicit limit: the bound
holds because no allocation that large succeeds. `agc_new_bytes`
(`vm/value.c`) allocates `sizeof(agc_bytes) + len` bytes, and the address
space of the 64-bit platforms agentica supports is far below `2^63` bytes, so
the allocator stops the program with out of memory first. This is a model
assumption, like the other resource limits that are not modelled.

**Names.** `Agentica.Bytes` is a type of its own. `Agentica.String` is only a
namespace for the builtins of `String` (`Agentica.String.from_int`): an
Agentica `String` is Lean's `String`. So translated code refers to them this
way:

- types by their short names (`AInt`, `Bytes`, `Result`, `M`, `String`),
  inside a namespace under `Agentica`. The only type name Lean shares is
  `String`, and it is the one meant;
- every prelude call by its full name (`Agentica.Bytes.at`,
  `Agentica.String.from_int`). Lean has its own `String.length` and others,
  so a short name could reach a Lean function when the prelude lacks the
  builtin; with the full name that is a build error.
-/

namespace Agentica

/-- Agentica `Bytes`. `small` is the size bound above. -/
structure Bytes where
  /-- The bytes. -/
  data : Array UInt8
  /-- The length fits in an `Int`. -/
  small : data.size < 2 ^ 63

/-- Agentica `Bytes.length`, which `b.size` resolves to
(`compiler/check/check_tables.agc`; `vm/bytes.c`, `builtin_length`). It never
halts. -/
def Bytes.length (b : Bytes) : AInt := ⟨BitVec.ofNat 64 b.data.size⟩

/-- Agentica `Bytes.at(b, i)`, also `b[i]` (`vm/bytes.c`, `builtin_at`). It
follows the C code: `i < 0 || (uint64_t)i >= len` is
`RUNTIME-INDEX-OUT-OF-RANGE`, else the byte as an `Int` from 0 to 255. -/
def Bytes.at (b : Bytes) (i : AInt) : M AInt :=
  if h : i.bits.toInt < 0 ∨ b.data.size ≤ i.bits.toNat then .error .indexOutOfRange
  else .ok ⟨BitVec.ofNat 64 (b.data[i.bits.toNat]'(by omega)).toNat⟩

namespace Bytes

/-- The length is the number of bytes, as a signed value. -/
theorem length_toInt (b : Bytes) : (Bytes.length b).bits.toInt = b.data.size :=
  AInt.toInt_ofNat_of_lt b.small

/-- In range, `b[i]` is the byte at `i`. -/
theorem at_ok (b : Bytes) (i : AInt) (h0 : 0 ≤ i.bits.toInt)
    (h1 : i.bits.toInt < b.data.size) :
    Bytes.at b i = pure ⟨BitVec.ofNat 64 (b.data[i.bits.toNat]!).toNat⟩ := by
  have := AInt.toInt_eq_toNat_of_nonneg h0
  have hlt : i.bits.toNat < b.data.size := by omega
  have hc : ¬ (i.bits.toInt < 0 ∨ b.data.size ≤ i.bits.toNat) := by omega
  simp only [Bytes.at, hc, ↓reduceDIte, getElem!_pos b.data i.bits.toNat hlt]
  rfl

/-- A negative index halts with `RUNTIME-INDEX-OUT-OF-RANGE`. -/
theorem at_neg (b : Bytes) (i : AInt) (h : i.bits.toInt < 0) :
    Bytes.at b i = .error .indexOutOfRange := by
  simp only [Bytes.at, h, true_or, ↓reduceDIte]

/-- An index at the length or above halts with `RUNTIME-INDEX-OUT-OF-RANGE`. -/
theorem at_ge_length (b : Bytes) (i : AInt) (h : b.data.size ≤ i.bits.toInt) :
    Bytes.at b i = .error .indexOutOfRange := by
  have := AInt.toInt_eq_toNat_of_nonneg (x := i.bits) (by omega)
  have hc : i.bits.toInt < 0 ∨ b.data.size ≤ i.bits.toNat := by omega
  simp only [Bytes.at, hc, ↓reduceDIte]

/-- A byte read is an `Int` from 0 to 255. -/
theorem at_range (b : Bytes) (i v : AInt) (h : Bytes.at b i = .ok v) :
    0 ≤ v.bits.toInt ∧ v.bits.toInt < 256 := by
  unfold Bytes.at at h
  split at h
  · cases h
  · cases h
    have := UInt8.toNat_lt (b.data[i.bits.toNat]'(by omega))
    rw [AInt.toInt_ofNat_of_lt (by omega)]
    omega

/-! The cases, checked by the kernel (`rfl`) on the bytes `[1, 2, 255]`. The
results were compared with agentica 0.24.1 by hand. -/

/-- The bytes `[1, 2, 255]`. -/
def sample : Bytes := ⟨#[1, 2, 255], by decide⟩

example : Bytes.length sample = AInt.ofInt 3 := rfl

example : Bytes.at sample (AInt.ofInt 0) = .ok (AInt.ofInt 1) := rfl

example : Bytes.at sample (AInt.ofInt 2) = .ok (AInt.ofInt 255) := rfl

example : Bytes.at sample (AInt.ofInt 3) = .error .indexOutOfRange := rfl

example : Bytes.at sample (AInt.ofInt (-1)) = .error .indexOutOfRange := rfl

example : Bytes.at sample (AInt.ofInt (-9223372036854775808)) = .error .indexOutOfRange := rfl

end Bytes

end Agentica
