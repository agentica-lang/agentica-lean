# agentica-lean

Lean 4 specifications and proofs of [Agentica](https://github.com/agentica-lang/agentica) builtins, tied to the real VM by differential tests.

## What this repo does

For a builtin, it has:

- **A specification.** A Lean definition that says what the builtin returns, or which error it raises, for every input. The Lean types follow the VM: an Agentica `Int` is 64 bits.
- **Proofs.** Theorems about that definition, checked by the Lean kernel when you run `lake build`.
- **Differential tests.** A Lean program prints the expected result of a table of cases. An Agentica program runs the same cases on the real `agentica` binary. A script compares the two: the values, and the diagnostic codes of the errors (never the message text).

The first builtin is `Int.shift_right_unsigned` (issue #1).

## What it proves, and what it does not

- The theorems are about the Lean definition only. They show that the specification says what we mean, for all inputs.
- The C code of the VM is **not** proved. It is tested through the binary, on the cases of the differential tests. A bug on an input that no case covers can still pass.
- The tests run one pinned `agentica` release. A new release is checked when CI moves to it.
- Proofs of the C code itself (for example with CBMC) belong in the agentica repo, in their own issue.

## Use it

Install [elan](https://github.com/leanprover/elan); it reads the Lean version from `lean-toolchain`. Then:

```sh
lake build --wfail
```

The build checks every proof. `--wfail` makes a `sorry` (or any other warning) fail it, and `Check/Axioms.lean` fails it when a proof uses an axiom other than the three standard ones of Lean (`propext`, `Classical.choice`, `Quot.sound`). So `sorry` and `native_decide` are out; `bv_decide` is fine, since the kernel checks its proof.

## License

MIT, see [LICENSE](LICENSE).
