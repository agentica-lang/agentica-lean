/-!
# Runtime errors

A runtime error halts an Agentica program with a diagnostic code. In Lean it
is a value of `RuntimeError`, and code that can halt runs in
`M := Except RuntimeError`. It is not an Agentica `Result`: a `Result` is a
value the program handles, a runtime error ends it.

There is one constructor per diagnostic code of the VM, and nothing else, so
`RuntimeError.code` is total over VM codes. (The fuel of a translated loop
runs out in the loop's own type, not here.)
-/

namespace Agentica

/-- The runtime errors of the builtins modelled so far: one constructor per
diagnostic code. -/
inductive RuntimeError where
  /-- A count outside its allowed range, for example a negative shift. -/
  | invalidCount
  /-- Signed overflow of `+`, `-` or `*` (`vm/interp.c`, `agc_op_add_i`). -/
  | integerOverflow
  /-- An index outside a collection, for example `b[i]` outside the bytes. -/
  | indexOutOfRange
  /-- `r.unwrap!` on an error (`vm/builtins.c`, `builtin_result_unwrap`). -/
  | unwrapError
  deriving DecidableEq, Repr

/-- The diagnostic code, as the VM reports it. -/
def RuntimeError.code : RuntimeError → String
  | .invalidCount => "RUNTIME-INVALID-COUNT"
  | .integerOverflow => "RUNTIME-INTEGER-OVERFLOW"
  | .indexOutOfRange => "RUNTIME-INDEX-OUT-OF-RANGE"
  | .unwrapError => "RUNTIME-UNWRAP-ERROR"

/-- Code that can halt: translated functions and the builtins that can fail. -/
abbrev M := Except RuntimeError

end Agentica
