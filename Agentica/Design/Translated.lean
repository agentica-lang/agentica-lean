import Agentica.Design.Read8
import Agentica.Design.ReadSigned
import Agentica.Design.ReadSignedBe
import Agentica.Design.ReadU16Be
import Agentica.Design.ReadU16Le
import Agentica.Design.ReadU32Be
import Agentica.Design.ReadU32Le
import Agentica.Design.ReadU64Be
import Agentica.Design.ReadU64Le
import Agentica.Std.Binary

/-!
# The translator writes the hand translations

`Agentica/Std/Binary.lean`, which `translator/main.agc` writes from
`std/binary`, has the same definitions as the hand translations of this
folder: the kernel checks each pair by `rfl`. Until the proofs move to the
generated file, this ties them to it.
-/

namespace Agentica.Design

example : Std.Binary.window = window := rfl

example : Std.Binary.load8 = load8 := rfl

example : Std.Binary.read_u8 = read_u8 := rfl

example : Std.Binary.extend = extend := rfl

example : Std.Binary.read_i8 = read_i8 := rfl

example : Std.Binary.load16_be = load16_be := rfl

example : Std.Binary.read_u16_be = read_u16_be := rfl

example : Std.Binary.load16_le = load16_le := rfl

example : Std.Binary.read_u16_le = read_u16_le := rfl

example : Std.Binary.read_i16_be = read_i16_be := rfl

example : Std.Binary.read_i16_le = read_i16_le := rfl

example : Std.Binary.load32_be = load32_be := rfl

example : Std.Binary.read_u32_be = read_u32_be := rfl

example : Std.Binary.load32_le = load32_le := rfl

example : Std.Binary.read_u32_le = read_u32_le := rfl

example : Std.Binary.read_i32_be = read_i32_be := rfl

example : Std.Binary.read_i32_le = read_i32_le := rfl

example : Std.Binary.load64_be = load64_be := rfl

example : Std.Binary.unsigned64 = unsigned64 := rfl

example : Std.Binary.read_u64_be = read_u64_be := rfl

example : Std.Binary.load64_le = load64_le := rfl

example : Std.Binary.read_u64_le = read_u64_le := rfl

example : Std.Binary.read_i64_be = read_i64_be := rfl

example : Std.Binary.read_i64_le = read_i64_le := rfl

end Agentica.Design
