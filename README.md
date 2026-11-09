# agentica-lean

Translate pure [Agentica](https://github.com/agentica-lang/agentica) functions to Lean 4, and prove things about the translated code.

## What this repo does

The plan is in issue #3. It has three parts:

- **A translator** from `.agc` to Lean, for pure functions: no I/O, tasks, channels or FFI. It reads the checked program and writes one Lean definition per function. A function outside the subset it knows is refused with a clear message.
- **A Lean prelude** that models the Agentica types and builtins the translated code calls. An `Int` is 64 bits, as in the VM, and a runtime error is its diagnostic code (`RUNTIME-...`), never its message. Each builtin in the prelude comes with theorems about it.
- **Proofs** about the translated functions, beside them, checked by the Lean kernel. The first target is the little-endian readers of `std/binary`: the shifts and ORs equal `b0 + 256*b1 + ...`.

## What is trusted

A proof here is about the Lean code. It says something about the real program only if these hold:

- **The translator** writes Lean that means the same as the `.agc` source. It is not proved. CI checks that the committed translation matches its source (a `--check` mode), and a differential test runs the same inputs through the real `agentica` binary and through the Lean code, comparing values and diagnostic codes.
- **The prelude** models the VM: each builtin in Lean does what the C code does. This is not proved either. The prelude follows the VM code, the builtin catalog and the site page of agentica, and the differential tests check it on their inputs. A bug on an input that no test covers can still pass.
- **The Lean kernel** checks every proof (see below).

The C code of the VM is not proved here, only tested through the binary. The tests run one pinned `agentica` release; a new release is checked when CI moves to it. Proofs of the C code itself (for example with CBMC) belong in the agentica repo.

## Use it

Install [elan](https://github.com/leanprover/elan); it reads the Lean version from `lean-toolchain`. Then:

```sh
lake build --wfail
```

The build checks every proof. `--wfail` makes a `sorry` (or any other warning) fail it, and `Check/Axioms.lean` fails it when a proof uses an axiom other than the three standard ones of Lean (`propext`, `Classical.choice`, `Quot.sound`). So every proof is checked by the Lean kernel. `sorry`, `native_decide` and `bv_decide` are out: the last two add an axiom that trusts compiled code (for `bv_decide`, its LRAT checker).

```sh
scripts/check.sh
```

The axiom check also fails on escapes that add no axiom: an `unsafe` constant, and `@[implemented_by]` or `@[extern]`. `scripts/check.sh` runs the checks that the build cannot do alone: every file under `Spec/` is imported by `Spec.lean` (so the axiom check sees it), no file turns off the kernel with `debug.skipKernelTC`, and the axiom check itself still fails on a `sorry`, a `native_decide`, a `bv_decide` and each escape (`tests/AxiomFixture.lean`). CI runs it.

## License

MIT, see [LICENSE](LICENSE).
