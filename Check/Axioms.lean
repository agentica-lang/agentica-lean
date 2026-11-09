import Lean
import Spec

/-!
# Axiom check

Building this module fails when a declaration of the `Spec` library depends on
an axiom outside `allowedAxioms`. It catches a `sorry` (`sorryAx`) even where
`--wfail` would not, for example one hidden behind a macro, and a new `axiom`.

Only the three standard axioms of Lean are allowed, so every proof is checked
by the kernel. `native_decide` and `bv_decide` add an axiom per use
(`_native.native_decide.ax_*`, `_native.bv_decide.ax_*`): they trust compiled
code, the decision procedure or the LRAT checker of `bv_decide`. The check
rejects both.

It also fails on escapes that add no axiom but skip the kernel or replace the
code: an `unsafe` constant, and a constant with `@[implemented_by]` or
`@[extern]` (also when set later with `attribute [...]`). The option
`debug.skipKernelTC` leaves no trace on a constant; `scripts/check.sh` greps
for it.

It sees only the modules that `Spec.lean` imports; `scripts/check.sh` fails
when a file under `Spec/` is missing there.
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
  for (n, info) in env.constants.map₁.toList do
    let some m := moduleOf env n | continue
    unless (`Spec).isPrefixOf m do continue
    if info.isUnsafe then
      bad := bad.push m!"{n} is unsafe"
    if (Compiler.getImplementedBy? env n).isSome then
      bad := bad.push m!"{n} has implemented_by"
    if isExtern env n then
      bad := bad.push m!"{n} is extern"
    let axioms ← collectAxioms n
    let extra := axioms.filter (fun a => !allowedAxioms.contains a)
    unless extra.isEmpty do
      bad := bad.push m!"{n} uses {extra.toList}"
  unless bad.isEmpty do
    throwError m!"declarations with axioms outside the allowed list, or with escapes:\n{MessageData.joinSep bad.toList "\n"}"
