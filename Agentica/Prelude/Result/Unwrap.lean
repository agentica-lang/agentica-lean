import Agentica.Prelude.Result
import Agentica.Prelude.RuntimeError

/-!
# `Result.unwrap!`

`r.unwrap!` (`vm/builtins.c`, `builtin_result_unwrap`) gives the value of
`ok(value)` and halts with `RUNTIME-UNWRAP-ERROR` on `error(...)`. The halt
text names the error; a runtime error is its code only.
-/

namespace Agentica

/-- Agentica `r.unwrap!` (`builtin_result_unwrap`). -/
def Result.unwrap! {α : Type} : Result α → M α
  | .ok value => pure value
  | .error _ => .error .unwrapError

namespace Result

theorem unwrap!_ok {α : Type} (value : α) : Result.unwrap! (.ok value) = pure value := rfl

theorem unwrap!_error {α : Type} (e : Error) :
    Result.unwrap! (α := α) (.error e) = .error .unwrapError := rfl

end Result

end Agentica
