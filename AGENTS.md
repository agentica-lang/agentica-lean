# agentica-lean

A translator of pure Agentica functions to Lean 4, a Lean prelude that models
the VM's types and builtins, and proofs of the translated code. The plan is
issue #3; `README.md` says what is trusted (the translator, the prelude's
model of the VM, the Lean kernel).

## Map

```text
lean-toolchain   the pinned Lean version
lakefile.toml    the Lake project: the `Agentica` and `Check` libraries
Agentica.lean    the library root; imports every module under Agentica/
Agentica/        the checked Lean code: Prelude/ (the model of the VM),
                 later the translations and their proofs
Check/Axioms.lean  fails the build when an Agentica declaration uses an axiom
                 other than propext, Classical.choice and Quot.sound
scripts/check.sh the checks around the build (imports, escapes, self-test)
tests/AxiomFixture.lean  bad proofs that the axiom check must reject
.github/         CI: elan, `lake build --wfail`, then `scripts/check.sh`
```

## Commands

- `lake build --wfail`: build and check every proof and the axioms; a warning
  fails it.
- `scripts/check.sh`: the imports of `Agentica.lean`, the banned escapes, and
  a test that the axiom check fails on a bad fixture. Run it after the build.

## Rules

- Every proof is checked by the kernel. No `sorry`, `admit`, `native_decide`,
  `bv_decide` or new `axiom`: `bv_decide` adds an axiom that trusts its
  compiled LRAT checker. Use `bv_omega`, `omega`, `simp` with `BitVec`
  lemmas, or `decide +kernel`. CI fails on a warning, and `Check/Axioms.lean`
  fails on any axiom but `propext`, `Classical.choice` and `Quot.sound`.
- No escapes that add no axiom: `unsafe`, `@[implemented_by]`, `@[extern]`
  (`Check/Axioms.lean` fails on them) and `set_option debug.skipKernelTC`
  (`scripts/check.sh` fails on it).
- `Agentica.lean` imports every file under `Agentica/`; `scripts/check.sh`
  fails otherwise.
- No Mathlib unless a proof needs it; then the PR says why.
- A builtin in the prelude follows the real contract: read the VM code
  (`vm/`), the catalog row (`compiler/catalog/builtins_data.agc`) and the
  site page (`site/content/library/`) of agentica first.
- An Agentica `Int` is a `BitVec 64`. A runtime error is its diagnostic code
  (`RUNTIME-...`), never its message.
- Differential tests compare values and diagnostic codes, never message text.
- Translated files are generated: change the translator or the `.agc` source,
  never the output by hand.
- Pin every tool and action: Lean in `lean-toolchain`, elan and actions by
  version and hash in CI.
- Each PR says `Part of #N` or `Closes #N`.
- Use simple words in the docs.
