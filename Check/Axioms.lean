import Lean
import Spec

/-!
# Axiom check

Building this module fails when a declaration of the `Spec` library depends on
an axiom outside `allowedAxioms`. It catches a `sorry` (`sorryAx`) even where
`--wfail` would not, for example one hidden behind a macro, and a new `axiom`.

Only the three standard axioms of Lean are allowed. `bv_decide` needs no
other: the kernel checks its certificate. `native_decide` adds an axiom per
use (it trusts the compiled code), so the check rejects it.
-/

open Lean Elab Command

/-- The axioms a spec may use. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The name of the module that declares `n`, if it comes from an import. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

run_cmd do
  let env ← getEnv
  let mut bad : Array MessageData := #[]
  for (n, _) in env.constants.map₁.toList do
    let some m := moduleOf env n | continue
    unless (`Spec).isPrefixOf m do continue
    let axioms ← collectAxioms n
    let extra := axioms.filter (fun a => !allowedAxioms.contains a)
    unless extra.isEmpty do
      bad := bad.push m!"{n} uses {extra.toList}"
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside the allowed list:\n{MessageData.joinSep bad.toList "\n"}"
