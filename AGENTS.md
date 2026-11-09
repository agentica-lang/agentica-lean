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
.github/         CI: elan, then `lake build --wfail`
```

## Commands

- `lake build --wfail`: build and check every proof and the axioms; a warning
  fails it.

## Rules

- No `sorry`, no `admit`, no `native_decide` and no new `axiom`. CI fails on
  a warning, and `Check/Axioms.lean` fails on any axiom but the standard
  three. `bv_decide` is fine: the kernel checks its proof.
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
