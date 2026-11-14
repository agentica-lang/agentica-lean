import Agentica.Prelude.Bytes
import Agentica.Prelude.Result
import Agentica.Prelude.String.FromInt

/-!
# `Bytes.from_list`

`Bytes.from_list(items)` (`vm/bytes.c`, `builtin_from_list`) is `ok` of the
bytes of `items`, or, for the first item outside 0 to 255, the error
`item K is X, not a byte (0 to 255)` with its index `K` from 0 and kind
`argument`. It never halts. A `List[Int]` is a Lean `List AInt`; a list of
`2^63` items or more is out of memory in the VM first (the size bound of
`Agentica/Prelude/Bytes.lean`), and the model gives `ok` of no bytes then.
-/

namespace Agentica

/-- The first item outside 0 to 255, from index `k`, with its index. -/
def Bytes.firstNonByte : Nat → List AInt → Option (Nat × AInt)
  | _, [] => none
  | k, x :: rest =>
    if x.bits.toInt < 0 ∨ 255 < x.bits.toInt then some (k, x) else Bytes.firstNonByte (k + 1) rest

/-- Agentica `Bytes.from_list(items)` (`builtin_from_list`). -/
def Bytes.from_list (items : List AInt) : Result Bytes :=
  match Bytes.firstNonByte 0 items with
  | some (k, x) =>
    .error { kind := "argument", message := (
      "item " ++ toString k ++ " is " ++ String.from_int x ++ ", not a byte (0 to 255)") }
  | none =>
    if h : items.length < 2 ^ 63 then
      .ok ⟨(items.map fun x => x.bits.toNat.toUInt8).toArray, by simpa using h⟩
    else .ok ⟨#[], by decide⟩

/-! Edge cases, checked by the kernel (`rfl`). -/

example : Bytes.from_list [] = .ok ⟨#[], by decide⟩ := rfl

example : Bytes.from_list [AInt.ofInt 1, AInt.ofInt 255] = .ok ⟨#[1, 255], by decide⟩ := rfl

example : Bytes.from_list [AInt.ofInt 1, AInt.ofInt 256, AInt.ofInt (-1)] =
    .error { kind := "argument", message := "item 1 is 256, not a byte (0 to 255)" } := rfl

end Agentica
