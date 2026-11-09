/-!
# `Result[T]`

An Agentica `Result[T]` is `ok(value)`, or `error(message)` with a `String`
message (`docs/grammar/06-semantics.md` of agentica). It is a value that the
program handles, unlike a `RuntimeError`, which halts it. `Result[Void]` is
`Result Unit`.

`try e` in a function that returns a `Result` is, in translated code,
`match ← e with | .error m => return .error m | .ok v => ...`.
-/

namespace Agentica

/-- Agentica `Result[T]`: a value, or an error with its message. -/
inductive Result (α : Type) where
  /-- `ok(value)`. -/
  | ok (value : α)
  /-- `error(message)`. -/
  | error (message : String)
  deriving DecidableEq, Repr

end Agentica
