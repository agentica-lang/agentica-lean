# agentica-lean

Translate pure [Agentica](https://github.com/agentica-lang/agentica) functions to Lean 4, and prove things about the translated code.

## What this repo does

The plan is in issue #3, and the design in [docs/translator.md](docs/translator.md). It has three parts:

- **A translator** from `.agc` to Lean, for pure functions: no I/O, tasks, channels or FFI. It reads the checked program and writes one Lean definition per function. A function outside the subset it knows is refused with a clear message.
- **A Lean prelude** that models the Agentica types and builtins the translated code calls. An `Int` is 64 bits, as in the VM, and a runtime error is its diagnostic code (`RUNTIME-...`), never its message. Each builtin in the prelude comes with theorems about it; the first one is `Int.shift_right_unsigned` (`Agentica/Prelude/Int/ShiftRightUnsigned.lean`).
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

The axiom check also fails on escapes that add no axiom: an `unsafe` constant, and `@[implemented_by]` or `@[extern]`. `scripts/check.sh` runs the checks that the build cannot do alone: every file under `Agentica/` is imported by `Agentica.lean` (so the axiom check sees it), no file turns off the kernel with `debug.skipKernelTC`, and the axiom check itself still fails on a `sorry`, a `native_decide`, a `bv_decide` and each escape (`tests/AxiomFixture.lean`). CI runs it.

## The differential test

```sh
AGENTICA=/path/to/agentica python3 scripts/difftest.py
```

`lake exe diffcases` prints the cases with the results of the Lean prelude: the edges of every function and random cases from a fixed seed. `diff/run.agc` runs the same cases on the `agentica` binary, and the script compares the values and the diagnostic codes (and the text of a `Result` error, which is a value). A failing case prints its arguments, the Lean result and the VM result. The script also fails when its own run cannot be trusted: no cases, a function without its cases, a case the harness cannot read, or a halt outside the builtin under test. `--self-test` plants each of these and checks that it fails; CI runs it. Without a binary the script skips.

The prelude is checked against **agentica 0.27.0**: CI installs that release and checks its SHA-256. To move to a new release, change the version and the `linux-x86_64` SHA-256 (from the release's `SHA256SUMS`) in `.github/workflows/ci.yml`, run the test, and read the release notes for changed builtins. A difference is a change of the VM: fix the prelude function, its doc comment and its theorems to match, or report it to agentica if it is a bug there.

## License

MIT, see [LICENSE](LICENSE).
