# agentica-lean

Lean 4 specifications of Agentica builtins, their proofs, and differential
tests against the real `agentica` binary. `README.md` says what is proved and
what is not.

## Map

```text
lean-toolchain   the pinned Lean version
lakefile.toml    the Lake project: the `Spec` and `Check` libraries
Spec.lean        the library root; imports every spec
Spec/            one module per builtin: Spec/<Type>/<Method>.lean
Check/Axioms.lean  fails the build when a Spec declaration uses an axiom
                 other than propext, Classical.choice and Quot.sound
scripts/check.sh the checks around the build (imports, escapes, self-test)
tests/AxiomFixture.lean  bad proofs that the axiom check must reject
.github/         CI: elan, `lake build --wfail`, then `scripts/check.sh`
```

## Commands

- `lake build --wfail`: build and check every proof and the axioms; a warning
  fails it.
- `scripts/check.sh`: the imports of `Spec.lean`, the banned escapes, and a
  test that the axiom check fails on a bad fixture. Run it after the build.

## Rules

- Every proof is checked by the kernel. No `sorry`, `admit`, `native_decide`,
  `bv_decide` or new `axiom`: `bv_decide` adds an axiom that trusts its
  compiled LRAT checker. Use `bv_omega`, `omega`, `simp` with `BitVec`
  lemmas, or `decide +kernel`. CI fails on a warning, and `Check/Axioms.lean`
  fails on any axiom but `propext`, `Classical.choice` and `Quot.sound`.
- No escapes that add no axiom: `unsafe`, `@[implemented_by]`, `@[extern]`
  (`Check/Axioms.lean` fails on them) and `set_option debug.skipKernelTC`
  (`scripts/check.sh` fails on it).
- `Spec.lean` imports every file under `Spec/`; `scripts/check.sh` fails
  otherwise.
- No Mathlib unless a proof needs it; then the PR says why.
- A spec follows the real contract: read the VM code (`vm/`), the catalog row
  (`compiler/catalog/builtins_data.agc`) and the site page
  (`site/content/library/`) of agentica first.
- An Agentica `Int` is a `BitVec 64` in a spec. An error is its diagnostic
  code (`RUNTIME-...`), never its message.
- Differential tests compare values and diagnostic codes, never message text.
- Pin every tool and action: Lean in `lean-toolchain`, elan and actions by
  version and hash in CI.
- One builtin per PR; each PR says `Part of #N` or `Closes #N`.
- Use simple words in the docs.
