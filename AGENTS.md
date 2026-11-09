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
  Prelude/RuntimeError.lean  RuntimeError (one constructor per VM code)
                 and M := Except RuntimeError
  Prelude/Int.lean  AInt (an Agentica Int: a structure of 64 bits)
  Prelude/Int/<Method>.lean  one builtin of Int, with its theorems;
                 Arith (+, -) and Compare (==, <, ...) hold the operators,
                 Bits the bit_* builtins
  Prelude/String/<Method>.lean  one builtin of String
  Design/          hand translations: the output the translator must
                 reproduce (docs/translator.md)
docs/translator.md  the design of the translator
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
- An Agentica `Int` is `AInt`, a structure around `bits : BitVec 64`
  (`bits.toInt` reads it as signed). It has no arithmetic or order instances:
  the operators of `BitVec` wrap and compare unsigned, the VM does not. The
  prelude and translated code reach an `Int` only through prelude functions,
  and the translator emits qualified calls (`AInt.shift_right_unsigned a c`).
- A builtin that can fail returns `Except RuntimeError`, one constructor per
  diagnostic code (`RUNTIME-...`), never its message.
- A builtin keeps its Agentica name: `Int.shift_right_unsigned` is
  `AInt.shift_right_unsigned`. Its definition follows the C code step by step,
  and its doc comment names the C function.
- Differential tests compare values and diagnostic codes, never message text.
- Translated files are generated: change the translator or the `.agc` source,
  never the output by hand.
- Pin every tool and action: Lean in `lean-toolchain`, elan and actions by
  version and hash in CI.
- Each PR says `Part of #N` or `Closes #N`.
- Use simple words in the docs.
