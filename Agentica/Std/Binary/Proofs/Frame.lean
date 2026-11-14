import Agentica.Std.Binary.Proofs.Write
import Agentica.Std.Binary.Proofs.ReadFrameLength

/-!
# `frame`

Theorems about `frame` of `Agentica/Std/Binary.lean`: the payload after its
big-endian u32 length, which `read_frame_length` reads back.
-/

namespace Agentica.Std.Binary

/-! ## Theorems -/

/-- The bytes of `a + c` start with those of `a`. -/
theorem byte_plus_left (a c : Bytes) (h : a.data.size + c.data.size < 2 ^ 63) (k : Nat)
    (hk : k < a.data.size) : (Bytes.plus a c).byte k = a.byte k := by
  simp only [Bytes.byte, Bytes.plus_data a c h]
  rw [getElem!_pos (a.data ++ c.data) k (by simp; omega), getElem!_pos a.data k hk,
    Array.getElem_append_left hk]

/-- A payload of at most `2^32 - 1` bytes: `frame` never halts, its bytes after the
first 4 are the payload, and `read_frame_length` at offset 0 gives the payload
length when the limit allows it. -/
theorem frame_round_trip (payload : Bytes) (max : AInt) (h : payload.data.size ≤ 4294967295)
    (hm : payload.data.size ≤ max.bits.toInt) :
    ∃ b, frame payload = pure (.ok b) ∧ b.data.extract 4 b.data.size = payload.data ∧
      read_frame_length b (AInt.ofInt 0) max = pure (.ok (Bytes.length payload)) := by
  have hl := Bytes.length_toInt payload
  have hn : (Bytes.length payload).bits.toNat = payload.data.size := by
    simp only [Bytes.length, BitVec.toNat_ofNat]; omega
  have hg : AInt.gt (Bytes.length payload) (AInt.ofInt 4294967295) = false := by
    have : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
    simp only [AInt.gt, decide_eq_false_iff_not]; omega
  obtain ⟨h4, hb, hs, e0, e1, e2, e3⟩ := bytes4_be_eq (Bytes.length payload)
  have hsum : h4.data.size + payload.data.size < 2 ^ 63 := by omega
  have hf : frame payload = pure (.ok (Bytes.plus h4 payload)) := by
    simp only [frame, hg, hb, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
    rfl
  refine ⟨Bytes.plus h4 payload, hf, ?_, ?_⟩
  · rw [Bytes.plus_data h4 payload hsum]
    simp [Array.extract_append, hs]
  · have z : (AInt.ofInt 0).bits.toNat = 0 := rfl
    have hsz : (Bytes.plus h4 payload).data.size = 4 + payload.data.size := by
      rw [Bytes.plus_data h4 payload hsum, Array.size_append, hs]
    rw [read_frame_length_in_range _ _ max (by omega) (by decide) (by
      rw [hsz]; have : (AInt.ofInt 0).bits.toInt = 0 := by decide
      omega)]
    simp only [z, be32, Nat.zero_add, byte_plus_left h4 payload hsum 0 (by omega),
      byte_plus_left h4 payload hsum 1 (by omega), byte_plus_left h4 payload hsum 2 (by omega),
      byte_plus_left h4 payload hsum 3 (by omega), e0, e1, e2, e3, hn]
    have d : payload.data.size % 256 + 2 ^ 8 * (payload.data.size / 2 ^ 8 % 256) +
        2 ^ 16 * (payload.data.size / 2 ^ 16 % 256) + 2 ^ 24 * (payload.data.size / 2 ^ 24 % 256) =
        payload.data.size := by omega
    rw [d]
    simp only [hm, ↓reduceIte]
    rfl

/-- A payload above `2^32 - 1` bytes is the documented error. -/
theorem frame_too_large (payload : Bytes) (h : 4294967295 < payload.data.size) :
    frame payload = pure (.error { kind := "argument", message := (
      "payload of " ++ String.from_int (Bytes.length payload) ++
        " bytes does not fit in a u32 length") }) := by
  have hl := Bytes.length_toInt payload
  have hg : AInt.gt (Bytes.length payload) (AInt.ofInt 4294967295) = true := by
    have : (AInt.ofInt 4294967295).bits.toInt = 4294967295 := by decide
    simp only [AInt.gt, decide_eq_true_eq]; omega
  simp only [frame, hg, ↓reduceIte]

end Agentica.Std.Binary
