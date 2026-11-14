# The translator: design

The plan of #3: translate pure Agentica functions to Lean and prove things
about them. This page records the decisions. The first target is the
integer readers of `stdlib/binary.agc`: `Agentica/Std/Binary.lean` is their
translation, and `Agentica/Std/Binary/Proofs/` holds the theorems.

## What agentica gives today

Checked against agentica 0.32.0-alpha.1 (`stdlib/analysis.agc`,
`site/content/library/analysis.md`, the query commands of the CLI).

- `std/analysis` answers `check`, `outline` (declarations and signatures),
  `type_at`, `symbol`, `refs` and `native_modules`. The CLI has the same
  queries: `outline`, `type-at`, `symbol`, `refs`.
- It also has `bodies` (and `bodies_json`, agentica#1159): the functions of a
  file with their bodies as a typed tree, the resolved call targets and
  whether each is pure. It is experimental, its shape may change between
  releases, and it has no CLI form. `translator/` reads it.
- Inside the compiler, the checker keeps no typed tree either. `Checked`
  (`compiler/check/checker.agc`) is a set of side tables over the untyped
  AST: the type of each node by id, what each method call or field resolved
  to, and the prelude function each call of a prelude builtin runs.
  `bodies` (`compiler/analysis/bodies.agc`) builds its typed tree from the
  AST and these tables.
- agentica#1159 asked for `Analysis.bodies(session, path)` and its JSON form:
  the functions of a file with resolved types, the body as a typed tree with
  resolved call targets, whether each function is pure (with the reason when
  not), struct and enum types, and spans. It was written for an SMT tool,
  `agentica-lang/verify`, also written in Agentica.

## What the readers need

The readers and their helpers (`window`, `load*`, `extend`, `unsigned64`)
use:

- `Int`: literals, `+`, `-` and unary `-` (they halt on overflow), `<` and
  `>`, `or`, and `shift_left`, `shift_right`, `bit_or`, `bit_and`;
- `Bytes`: `data.size` (an alias of `Bytes.length`), `data[i]` (it halts
  outside the bytes), `+` and `Bytes.from_list`;
- `List[Int]`: list literals;
- `Result`: `ok`, `error` with a message and a kind, `unwrap!`, and `try` as
  a statement and as an expression;
- a string interpolation of `String` and `Int`;
- local bindings, `if`, `return`, and calls of private functions of the same
  file.

The float readers and writers need `Float.from_bits` and `Float.to_bits`:
a later step.

## Options

1. **Written in Agentica, on `std/analysis`** with #1159. It reads the
   checker's own answer: the resolved types, call targets and purity come
   from the same code the VM runs. The same shape serves `verify`. It is
   blocked until a release has #1159.
2. **A tool that reads a JSON dump** of the checked program, written in Lean
   as a `lake exe`. #1159 already gives a versioned JSON form, so this adds
   only a CLI command in agentica.
3. **Its own front end** (parser and type rules of the subset). It is not
   blocked. But it is a second copy of the checker: method resolution,
   literal types, `try`, default arguments and the prelude builtins. A
   difference from the checker is a wrong translation that a proof cannot
   catch, and the differential tests catch only the inputs they try.

**Recommendation: option 1.** One language for `verify` and this tool, so
they share the reading of the tree, and no tree decoder to write in Lean.
Until #1159 ships, this repo grows the prelude
(below), writes more hand translations as goldens, and builds the
differential harness, so the translator is the last piece.

What #1159 must give for step 1:

- every function of a file, private ones too (the readers call private
  helpers), with its linked name, and its generic parameters and the type
  arguments of each generic call;
- the typed tree of the step 1 subset: literals, locals and rebinding, calls
  with the resolved target (user function, or builtin such as `Int.shift_left`
  and `Bytes.at` for `data[i]`), operators with their operand type, `and`,
  `or`, `not`, `if`/`elsif`/`else`, `case` with patterns, `return`, `try`,
  `ok`/`error`, `Optional`, and the parts of a string interpolation with
  their types;
- purity, through every call, with the reason when a function is impure. A
  builtin that can halt (`+`, `b[i]`, `unwrap!`) still counts as pure: the
  halt is a value of the model;
- the body of a prelude builtin that is written in Agentica (`Checked.bodies`),
  or its name, so the prelude can model it;
- a span on every node, and a version field in the JSON;
- a release that this repo can pin.

## The Lean shape

`window`, `load16_le` and `read_u16_le` of `Agentica/Std/Binary.lean` show
all of it.

- **Types.** `Int` is `AInt` (a structure around `BitVec 64`, with no
  operators), `Bool` is `Bool`, `String` is `String`, `Bytes` is a structure
  around `Array UInt8` with a size below `2^63`, `Void` is `Unit`,
  `Optional[T]` is `Option`, and `Result[T]` is the prelude's `Result`: `ok`,
  or `error` with an `Error` (its kind and message). Structs and enums
  (step 2) become structures and inductives.
- **Runtime errors.** A runtime error halts the program, so it is not a
  `Result`: every translated function returns `M T`, with
  `M := Except RuntimeError`, one constructor per diagnostic code
  (`RUNTIME-INTEGER-OVERFLOW`, `RUNTIME-INDEX-OUT-OF-RANGE`, ...). A builtin
  that can halt (`+`, `data[i]`, `shift_left`) returns `M`; one that cannot
  (`<`, `bit_or`) is a plain function. Each is a prelude function, called by
  its full name (`Agentica.Bytes.at`): Lean has its own `String.length` and
  others, so a short name could reach one when the prelude lacks the
  builtin. Types keep their short names (`AInt`, `Bytes`, `Result`, `M`).
- **Order.** Each step that can halt is a `←` in `do` notation, in the order
  the VM evaluates it (left to right). `a or b` is
  `if a then true else b`, so `b` runs only when it does in the VM.
- **`case`, `Result`, `try`.** `case` is `match`, with the same patterns.
  `try e` is `match ← e with | .error e => return .error e | .ok v => ...`.
  `return` is `return`.
- **Literals.** `AInt.ofInt 2`; an interpolation is `++`, with
  `String.from_int` for an `Int` part (the VM's `TO_TEXT` writes the same
  text as `n.to_s`).
- **Names.** A call takes the name the checker resolved, not the one written:
  `data.size` is `Bytes.length` (an alias, `compiler/check/check_tables.agc`).
  A call of a function of the file is written by its full name
  (`Agentica.Std.Binary.window`), so a local or a Lean name (`pure`) cannot
  hide it; the code the translator adds is qualified too (`Pure.pure`), and its
  fresh names (`t1`, ...) avoid every name of the file.
- **Arguments.** They run in the order of the source, which is the order
  `Analysis.bodies` gives them in. A named argument is a `named` node with the
  parameter name, so the translator binds it first and passes it in the place
  of its parameter.
- **Recursion (step 1).** A recursive function becomes a Lean `def`. If Lean
  cannot prove that it ends, the build fails, and the function stays out of
  the translation until a later step adds termination hints. In practice
  step 1 accepts almost no recursion over `Int`: Lean finds no structural
  measure on `AInt` and needs `termination_by`. A `def` by well-founded
  recursion is irreducible, so a golden over it needs `decide +kernel` or
  `unseal`, not `rfl`. `partial` is not used: it gives nothing to prove.
- **Loops (step 3).** A loop becomes a function with fuel, with the top call
  given `2^64` steps. Running out is its own constructor, `outOfFuel`, in the
  fuel wrapper's own type, not in `RuntimeError`, which keeps one constructor
  per VM code (so `RuntimeError.code` stays total). The differential test
  fails if it ever sees it. The definition stays total. A theorem that
  a call does not halt says `∃ v, f x = pure v` (or `f x = pure v`), never
  `f x ≠ .error e`, since that also holds when the fuel runs out.
- **Not modelled.** The stack depth (`RUNTIME-STACK-OVERFLOW`), the step
  limit (`RUNTIME-STEP-LIMIT`, `--max-steps`) and memory. A theorem may give
  a value where the VM runs out of them.

## Layout and the `--check` mode

- `translator/`: the Agentica program. `main.agc` lists the jobs (a `std/`
  module, the functions to translate, the Lean file); `lean.agc` writes Lean
  from `Analysis.bodies`; `lean_test.agc` is its tests (`agentica test
  translator`).
- `Agentica/Std/Binary.lean`: generated from `std/binary`, with the integer
  readers and writers, `read_frame_length`, `frame` and the helpers they
  call. Its header says that it is generated. The source comes from the
  binary itself (`std/binary` without a buffer), so pinning the binary pins
  the source.
- `Agentica/Std/Binary/Proofs/`: the theorems about the generated code,
  written by hand, one file per group of readers, then `Write.lean` (the
  writers), `RoundTrip.lean` (each writer read back) and `Frame.lean`.
- `agentica translator/main.agc` writes the files; `--check` translates
  again in memory and exits 1 naming each stale file. CI runs it with the
  pinned release.
- The differential test: a `lake exe` and an `.agc` program print the results
  of the same inputs, and a script compares the values and the diagnostic
  codes.

## The prelude needs first

Each with its VM contract, in its own PR (all in `Agentica/Prelude/` now):

- `AInt.add`, `AInt.sub`: `RUNTIME-INTEGER-OVERFLOW` on signed overflow
  (`vm/interp.c`, `agc_op_add_i`, `agc_op_sub_i`).
- `AInt.lt`, `AInt.le`, `AInt.gt`, `AInt.ge`, `AInt.eq`: signed comparisons.
- `AInt.shift_left`, `AInt.shift_right` (`vm/numbers.c`): a negative count
  is `RUNTIME-INVALID-COUNT`, and a count of 64 or more gives 0 (or -1 for
  `shift_right` of a negative value). `AInt.bit_or`, `AInt.bit_and`.
- `String.from_int` (`n.to_s`): the decimal digits, for interpolation
  (`vm/builtins.c`, `builtin_from_int`).
- `Bytes`, `Bytes.length` (`vm/bytes.c`, `builtin_length`), and `Bytes.at`
  (`b[i]`, `builtin_at`): a byte from 0 to 255, or
  `RUNTIME-INDEX-OUT-OF-RANGE`.
- `Result`, and `RuntimeError` with the codes above.
