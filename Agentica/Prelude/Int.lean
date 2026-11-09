import Agentica.Prelude.RuntimeError

/-!
# The Agentica `Int`

An Agentica `Int` is a signed 64-bit integer in two's complement, as in the
VM (`int64_t`). Here it is `AInt`, a structure around its 64 bits:
`x.bits.toInt` reads them as signed (the Agentica value), `x.bits.toNat` as
unsigned.

`AInt` is a structure, not `BitVec 64` itself, so that the operators of
`BitVec` do not apply to it: they wrap on overflow and compare unsigned,
while the VM's `+`, `-` and `*` fail on overflow and its comparisons are
signed. Each VM operation comes as a prelude function with its own contract.

A builtin that can fail returns `M`, that is `Except RuntimeError`
(`Agentica/Prelude/RuntimeError.lean`): the error is the diagnostic code of
the VM, never its message.
-/

namespace Agentica

/-- An Agentica `Int`: 64 bits, read as signed with `bits.toInt`. It has no
arithmetic or order instances; use the prelude functions. -/
structure AInt where
  /-- The 64 bits of the value, two's complement. -/
  bits : BitVec 64
  deriving DecidableEq, Repr

/-- The Agentica `Int` with value `n`, wrapped to 64 bits: for literals, such
as `AInt.ofInt (-1)`. -/
def AInt.ofInt (n : Int) : AInt := ⟨BitVec.ofInt 64 n⟩

/-- If the signed value of `x` is not negative, it equals the unsigned one. -/
theorem AInt.toInt_eq_toNat_of_nonneg {x : BitVec 64} (h : 0 ≤ x.toInt) :
    x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split <;> omega

/-- A natural number below `2^63` keeps its value as a signed 64-bit one. -/
theorem AInt.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  split <;> omega

/-- A literal from 0 to `2^63 - 1` has its value. -/
theorem AInt.ofInt_toInt {n : Nat} (h : n < 2 ^ 63) : (AInt.ofInt n).bits.toInt = n := by
  simp only [AInt.ofInt, BitVec.ofInt_natCast]
  exact toInt_ofNat_of_lt h

end Agentica
