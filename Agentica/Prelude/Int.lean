/-!
# The Agentica `Int`

An Agentica `Int` is a signed 64-bit integer in two's complement, as in the
VM (`int64_t`). Here it is the 64 bits, a `BitVec 64`: `x.toInt` reads them
as signed (the Agentica value), `x.toNat` as unsigned.

A builtin that can fail returns `Except RuntimeError`: the error is the
diagnostic code of the VM, never its message.
-/

namespace Agentica

/-- An Agentica `Int`: 64 bits, read as signed with `toInt`. -/
abbrev AInt := BitVec 64

/-- The runtime errors of the builtins modelled so far. One constructor per
diagnostic code; `code` gives the text the VM prints. -/
inductive RuntimeError where
  /-- A count below zero, for example a negative shift. -/
  | invalidCount
  deriving DecidableEq, Repr

/-- The diagnostic code, as the VM reports it. -/
def RuntimeError.code : RuntimeError → String
  | .invalidCount => "RUNTIME-INVALID-COUNT"

/-- The Agentica `Int` with value `n`, wrapped to 64 bits. -/
abbrev AInt.ofInt (n : Int) : AInt := BitVec.ofInt 64 n

/-- If the signed value of `x` is not negative, it equals the unsigned one. -/
theorem AInt.toInt_eq_toNat_of_nonneg {x : AInt} (h : 0 ≤ x.toInt) :
    x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split <;> omega

end Agentica
