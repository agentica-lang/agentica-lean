import Std.Tactic.BVDecide

/-!
Bad declarations for `scripts/check.sh`. It copies this file into
`Agentica/`, imports it from `Agentica.lean`, and expects `Check/Axioms.lean`
to reject each one.
-/

theorem axiomFixtureSorry : 1 = 2 := sorry

theorem axiomFixtureNative : 2 + 2 = 4 := by native_decide

theorem axiomFixtureBvDecide (x y : BitVec 64) : (x &&& y) + (x ||| y) = x + y := by
  bv_decide

unsafe def axiomFixtureUnsafe : Nat := 1

def axiomFixtureImpl : Nat := 2

@[implemented_by axiomFixtureImpl]
def axiomFixtureImplementedBy : Nat := 1

opaque axiomFixtureExtern : Nat → Nat

attribute [extern "axiom_fixture_extern"] axiomFixtureExtern
