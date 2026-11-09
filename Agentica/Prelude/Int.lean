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

A builtin that can fail returns `Except RuntimeError`: the error is the
diagnostic code of the VM, never its message.
-/

namespace Agentica

/-- An Agentica `Int`: 64 bits, read as signed with `bits.toInt`. It has no
arithmetic or order instances; use the prelude functions. -/
structure AInt where
  /-- The 64 bits of the value, two's complement. -/
  bits : BitVec 64
  deriving DecidableEq, Repr

/-- The runtime errors of the builtins modelled so far. One constructor per
diagnostic code; `code` gives the text the VM prints. -/
inductive RuntimeError where
  /-- A count outside its allowed range, for example a negative shift. -/
  | invalidCount
  deriving DecidableEq, Repr

/-- The diagnostic code, as the VM reports it. -/
def RuntimeError.code : RuntimeError → String
  | .invalidCount => "RUNTIME-INVALID-COUNT"

/-- The Agentica `Int` with value `n`, wrapped to 64 bits: for literals, such
as `AInt.ofInt (-1)`. -/
def AInt.ofInt (n : Int) : AInt := ⟨BitVec.ofInt 64 n⟩

/-- If the signed value of `x` is not negative, it equals the unsigned one. -/
theorem AInt.toInt_eq_toNat_of_nonneg {x : BitVec 64} (h : 0 ≤ x.toInt) :
    x.toInt = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  split <;> omega

end Agentica
