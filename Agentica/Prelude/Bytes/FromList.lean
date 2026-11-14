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

namespace Bytes

/-- No item from `k` on is outside 0 to 255 exactly when every item is a byte. -/
theorem firstNonByte_none_iff (k : Nat) (items : List AInt) :
    Bytes.firstNonByte k items = none ↔
      ∀ x ∈ items, 0 ≤ x.bits.toInt ∧ x.bits.toInt ≤ 255 := by
  induction items generalizing k with
  | nil => simp [Bytes.firstNonByte]
  | cons x rest ih =>
    by_cases hx : x.bits.toInt < 0 ∨ 255 < x.bits.toInt
    · simp only [Bytes.firstNonByte, hx, ↓reduceIte, reduceCtorEq, false_iff]
      intro h
      have := h x (List.mem_cons_self ..)
      omega
    · simp only [Bytes.firstNonByte, hx, ↓reduceIte, ih (k + 1), List.mem_cons,
        forall_eq_or_imp]
      constructor
      · intro h; exact ⟨by omega, h⟩
      · intro h; exact h.2

/-- The first item outside 0 to 255, at index `j`, is found with index `k + j`. -/
theorem firstNonByte_some (k : Nat) (items : List AInt) (j : Nat) (hj : j < items.length)
    (bad : items[j].bits.toInt < 0 ∨ 255 < items[j].bits.toInt)
    (good : ∀ i (hi : i < j), 0 ≤ (items[i]'(by omega)).bits.toInt ∧
      (items[i]'(by omega)).bits.toInt ≤ 255) :
    Bytes.firstNonByte k items = some (k + j, items[j]) := by
  induction items generalizing k j with
  | nil => simp at hj
  | cons x rest ih =>
    cases j with
    | zero => simp only [List.getElem_cons_zero] at bad; simp [Bytes.firstNonByte, bad]
    | succ j =>
      have hx := good 0 (by omega)
      simp only [List.getElem_cons_zero] at hx
      have hc : ¬ (x.bits.toInt < 0 ∨ 255 < x.bits.toInt) := by omega
      simp only [Bytes.firstNonByte, hc, ↓reduceIte]
      rw [ih (k + 1) j (by simpa using hj) (by simpa using bad)
        (fun i hi => by simpa using good (i + 1) (by omega))]
      simp only [List.getElem_cons_succ, Option.some.injEq, Prod.mk.injEq, and_true]
      omega

/-- When every item is a byte (and the list is below the size bound),
`Bytes.from_list` is `ok` of those bytes. -/
theorem from_list_ok (items : List AInt)
    (h : ∀ x ∈ items, 0 ≤ x.bits.toInt ∧ x.bits.toInt ≤ 255)
    (hl : items.length < 2 ^ 63) :
    Bytes.from_list items =
      .ok ⟨(items.map fun x => x.bits.toNat.toUInt8).toArray, by simpa using hl⟩ := by
  simp only [Bytes.from_list, (firstNonByte_none_iff 0 items).mpr h, hl, ↓reduceDIte]

/-- When item `j` is the first one outside 0 to 255, `Bytes.from_list` is the
documented error for index `j`. -/
theorem from_list_error (items : List AInt) (j : Nat) (hj : j < items.length)
    (bad : items[j].bits.toInt < 0 ∨ 255 < items[j].bits.toInt)
    (good : ∀ i (hi : i < j), 0 ≤ (items[i]'(by omega)).bits.toInt ∧
      (items[i]'(by omega)).bits.toInt ≤ 255) :
    Bytes.from_list items = .error { kind := "argument", message := (
      "item " ++ toString j ++ " is " ++ String.from_int items[j] ++
        ", not a byte (0 to 255)") } := by
  simp only [Bytes.from_list, firstNonByte_some 0 items j hj bad good, Nat.zero_add]

/-- `Bytes.from_list` is `ok` exactly when every item is a byte. -/
theorem from_list_ok_iff (items : List AInt) :
    (∃ b, Bytes.from_list items = .ok b) ↔
      ∀ x ∈ items, 0 ≤ x.bits.toInt ∧ x.bits.toInt ≤ 255 := by
  rw [← firstNonByte_none_iff 0 items]
  rcases hf : Bytes.firstNonByte 0 items with _ | ⟨k, x⟩
  · simp only [Bytes.from_list, hf, iff_true]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · simp [Bytes.from_list, hf]

end Bytes

/-! Edge cases, checked by the kernel (`rfl`). -/

example : Bytes.from_list [] = .ok ⟨#[], by decide⟩ := rfl

example : Bytes.from_list [AInt.ofInt 1, AInt.ofInt 255] = .ok ⟨#[1, 255], by decide⟩ := rfl

example : Bytes.from_list [AInt.ofInt 1, AInt.ofInt 256, AInt.ofInt (-1)] =
    .error { kind := "argument", message := "item 1 is 256, not a byte (0 to 255)" } := rfl

end Agentica
