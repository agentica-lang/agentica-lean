-- The imports of every module under Agentica/ go here, at the top of the file:
-- an import below the module doc would not parse.
import Agentica.Prelude.Bytes
import Agentica.Prelude.Int
import Agentica.Prelude.Int.Arith
import Agentica.Prelude.Int.Bits
import Agentica.Prelude.Int.Compare
import Agentica.Prelude.Int.ShiftLeft
import Agentica.Prelude.Int.ShiftRight
import Agentica.Prelude.Int.ShiftRightUnsigned
import Agentica.Prelude.Result
import Agentica.Prelude.RuntimeError
import Agentica.Prelude.String.FromInt
import Agentica.Std.Binary
import Agentica.Std.Binary.Proofs.Read8
import Agentica.Std.Binary.Proofs.ReadFrameLength
import Agentica.Std.Binary.Proofs.ReadSigned
import Agentica.Std.Binary.Proofs.ReadSignedBe
import Agentica.Std.Binary.Proofs.ReadU16Be
import Agentica.Std.Binary.Proofs.ReadU16Le
import Agentica.Std.Binary.Proofs.ReadU32Be
import Agentica.Std.Binary.Proofs.ReadU32Le
import Agentica.Std.Binary.Proofs.ReadU64Be
import Agentica.Std.Binary.Proofs.ReadU64Le

/-!
# Agentica in Lean

The root of the `Agentica` library, which imports every module under
`Agentica/`: the prelude (`Agentica/Prelude/`, the model of the VM's types and
builtins), and later the translated code and its proofs.
-/
