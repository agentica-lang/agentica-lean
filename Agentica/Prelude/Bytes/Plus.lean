import Agentica.Prelude.Bytes

/-!
# `Bytes` `+`

`a + b` (`vm/bytes.c`, `builtin_plus`) is a new `Bytes` with the bytes of `a`
then those of `b`. It never halts with a runtime error. Its length is the sum,
which `agc_size_add` stops with out of memory on a `size_t` overflow; like
the size bound of `Agentica/Prelude/Bytes.lean`, a sum of `2^63` bytes or more
is out of memory in the VM long before. The model gives `a` then: no program
reaches it.
-/

namespace Agentica

/-- Agentica `a + b` on `Bytes` (`builtin_plus`). -/
def Bytes.plus (a b : Bytes) : Bytes :=
  if h : a.data.size + b.data.size < 2 ^ 63 then
    ⟨a.data ++ b.data, by simp only [Array.size_append]; exact h⟩
  else a

namespace Bytes

/-- Below the size bound, `a + b` holds the bytes of `a` then those of `b`. -/
theorem plus_data (a b : Bytes) (h : a.data.size + b.data.size < 2 ^ 63) :
    (Bytes.plus a b).data = a.data ++ b.data := by
  simp only [Bytes.plus, h, ↓reduceDIte]

end Bytes

end Agentica
