/-!
# `Result[T]`

An Agentica `Result[T]` is `ok(value)`, or `error(...)`, which holds an
`Error` record (`site/content/library/errors/` of agentica). It is a value
that the program handles, unlike a `RuntimeError`, which halts it.
`Result[Void]` is `Result Unit`.

`Error` keeps the `kind` and the `message`. The VM's record also has `code`,
`details` and `cause`, which the code translated so far never sets, and
`location`, the `path:line:col` of the `error(...)` call; the prelude does
not model them.

`error("text")` is `.error { message := "text" }` (the kind is `"error"`),
and `error("text", kind: "argument")` is
`.error { kind := "argument", message := "text" }`. `try e` in a function
that returns a `Result` passes the same `Error` on:
`match ← e with | .error e => return .error e | .ok v => ...`.
-/

namespace Agentica

/-- The record a failed Agentica `Result` holds: its kind and its message. -/
structure Error where
  /-- A dotted name for the sort of failure; `error("text")` gives `"error"`. -/
  kind : String := "error"
  /-- The text for people. -/
  message : String
  deriving DecidableEq, Repr

/-- Agentica `Result[T]`: a value, or an `Error`. -/
inductive Result (α : Type) where
  /-- `ok(value)`. -/
  | ok (value : α)
  /-- `error(...)`. -/
  | error (error : Error)
  deriving DecidableEq, Repr

end Agentica
