-- The imports of every module under Agentica/ go here, at the top of the file:
-- an import below the module doc would not parse.
import Agentica.Design.ReadU16Le
import Agentica.Prelude.Int
import Agentica.Prelude.Int.Arith
import Agentica.Prelude.Int.Compare
import Agentica.Prelude.Int.ShiftRightUnsigned
import Agentica.Prelude.RuntimeError

/-!
# Agentica in Lean

The root of the `Agentica` library, which imports every module under
`Agentica/`: the prelude (`Agentica/Prelude/`, the model of the VM's types and
builtins), and later the translated code and its proofs.
-/
