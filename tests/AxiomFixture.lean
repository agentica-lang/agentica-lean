import Std.Tactic.BVDecide

/-!
Bad proofs for `scripts/check.sh`. It copies this file into `Spec/`, imports
it from `Spec.lean`, and expects `Check/Axioms.lean` to reject each one.
-/

theorem axiomFixtureSorry : 1 = 2 := sorry

theorem axiomFixtureNative : 2 + 2 = 4 := by native_decide

theorem axiomFixtureBvDecide (x y : BitVec 64) : (x &&& y) + (x ||| y) = x + y := by
  bv_decide
