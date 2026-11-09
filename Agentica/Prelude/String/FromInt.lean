import Agentica.Prelude.Int
import Std.Data.String.ToInt

/-!
# `String.from_int` (`Int.to_s`)

`n.to_s` is an alias: the checker resolves it to `String.from_int`
(`compiler/check/check_tables.agc`). The VM writes the decimal digits of the
signed value with `snprintf` and `PRId64` (`vm/builtins.c`,
`builtin_from_int`, through `agc_scalar_text` in `vm/text.c`): a `-` before a
negative value, no `+`, no leading zeros. An `Int` in a string interpolation
takes the same path (`TO_TEXT`, `agc_text`), so the translator writes this
function for it too. It never halts.
-/

namespace Agentica

/-- Agentica `String.from_int(n)`, also `n.to_s` and `"#{n}"`: the decimal
text of the signed value. -/
def String.from_int (n : AInt) : String := n.bits.toInt.repr

namespace String

/-- The text is Lean's decimal form of the signed value. -/
theorem from_int_eq (n : AInt) : String.from_int n = toString n.bits.toInt := rfl

/-- Reading the text back as an `Int` gives the value. -/
theorem toInt?_from_int (n : AInt) : (String.from_int n).toInt? = some n.bits.toInt :=
  Int.toInt?_repr _

/-- A value that is not negative is written as its digits alone. -/
theorem from_int_of_nonneg (n : AInt) (h : 0 ≤ n.bits.toInt) :
    String.from_int n = Nat.repr n.bits.toInt.toNat := by
  unfold String.from_int
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le h
  rw [hm]
  rfl

/-- A negative value is `-` and the digits of its absolute value. -/
theorem from_int_of_neg (n : AInt) (h : n.bits.toInt < 0) :
    String.from_int n = "-" ++ Nat.repr n.bits.toInt.natAbs := by
  unfold String.from_int
  obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat (Int.le_of_lt h)
  have hm0 : m ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  rw [hm]
  rfl

/-! The cases, checked by the kernel (`rfl`). The values were compared with
agentica 0.24.1 by hand. -/

example : String.from_int (AInt.ofInt 0) = "0" := rfl

example : String.from_int (AInt.ofInt 42) = "42" := rfl

example : String.from_int (AInt.ofInt (-42)) = "-42" := rfl

example : String.from_int (AInt.ofInt 9223372036854775807) = "9223372036854775807" := rfl

example : String.from_int (AInt.ofInt (-9223372036854775808)) = "-9223372036854775808" := rfl

end String

end Agentica
