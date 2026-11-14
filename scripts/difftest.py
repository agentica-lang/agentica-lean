#!/usr/bin/env python3
"""Differential test: the Lean prelude against the agentica binary.

`lake exe diffcases` prints the cases with the Lean results (the only source
of cases). `diff/run.agc` runs the same cases on agentica. A case that halts
ends that run; this script records its diagnostic code and starts again after
it. Then it compares each case, values and diagnostic codes only (a message
is compared only when it is a `Result` value).

The binary is `$AGENTICA`, or `agentica` on PATH. Without one the test skips,
unless `REQUIRE_AGENTICA=1` (CI), which makes it fail.

`--self-test` plants broken inputs and checks that each one fails.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

# The functions diff/run.agc runs. The cases must cover exactly these, each
# with at least MIN_CASES, so a lost function or a shrunken list fails.
FUNCTIONS = {
    "add", "sub", "bit_and", "bit_or", "bit_xor", "bit_not", "from_int", "shift_left",
    "shift_right", "shift_right_unsigned", "eq", "ne", "lt", "le", "gt", "ge", "length", "at",
    "read_u16_le", "read_u16_be", "read_u32_le", "read_u64_le", "read_i64_le", "read_i16_le",
    "read_i32_le", "read_u8", "read_i8", "read_u32_be", "read_u64_be", "read_i16_be",
    "read_i32_be", "read_i64_be", "read_frame_length",
}
MIN_CASES = 40

# The functions of diff/run.agc. A halt is a result only when the first of
# them on the stack (from the top; frames of std/ come before) is a `call_`
# function of diff/run.agc, the one that calls the builtin.
HARNESS = {"main", "run_case", "arity", "takes_bytes", "parse_bytes", "result_text"}
PROGRAM = "diff/run.agc"

RUN_TIMEOUT = 60


class HarnessError(Exception):
    """The test cannot trust its own run: not a difference of the VM."""


def find_agentica() -> str | None:
    path = os.environ.get("AGENTICA") or shutil.which("agentica")
    return path if path and os.access(path, os.X_OK) else None


def read_cases(text: str) -> list[tuple[int, str, str, str]]:
    cases = []
    for line in text.splitlines():
        id_, fn, args, expected = line.split("\t")
        cases.append((int(id_), fn, args, expected))
    if not cases:
        raise HarnessError("no cases")
    counts: dict[str, int] = {}
    for _, fn, _, _ in cases:
        counts[fn] = counts.get(fn, 0) + 1
    if set(counts) != FUNCTIONS:
        raise HarnessError(f"functions differ: missing {sorted(FUNCTIONS - set(counts))}, "
                           f"unknown {sorted(set(counts) - FUNCTIONS)}")
    few = sorted(fn for fn, n in counts.items() if n < MIN_CASES)
    if few:
        raise HarnessError(f"fewer than {MIN_CASES} cases for {few}")
    return cases


def halt_frame(stack: list[dict]) -> str | None:
    """The first function of the harness on the stack, from the top."""
    for frame in stack:
        name = frame.get("function", "")
        file = frame.get("file", "")
        if name.startswith("call_") and (file == PROGRAM or file.endswith("/" + PROGRAM)):
            return name
        if name.startswith("call_") or name in HARNESS:
            return f"{name} ({frame.get('file', '')})"
    return None


def run_vm(agentica: str, cases_path: str, count: int,
           program: str = PROGRAM) -> dict[int, str]:
    """Runs every case on agentica, restarting after each halt."""
    actual: dict[int, str] = {}
    start = 0
    while start < count:
        try:
            proc = subprocess.run(
                [agentica, "--json", program, cases_path, str(start)],
                capture_output=True, text=True, check=False, timeout=RUN_TIMEOUT)
        except subprocess.TimeoutExpired as err:
            raise HarnessError(f"agentica ran over {RUN_TIMEOUT} s from case {start}") from err
        last = start - 1
        for line in proc.stdout.splitlines():
            if line.startswith("harness ") or "\t" not in line:
                raise HarnessError(line)
            id_, result = line.split("\t", 1)
            if result.startswith("harness "):
                raise HarnessError(f"case {id_}: {result}")
            actual[int(id_)] = result
            last = int(id_)
        if proc.returncode == 0:
            break
        halted = last + 1
        if halted >= count:
            raise HarnessError(f"agentica failed after the last case:\n{proc.stderr}")
        try:
            diagnostic = json.loads(proc.stderr.strip().splitlines()[-1])
        except (ValueError, IndexError) as err:
            raise HarnessError(f"case {halted}: agentica failed without a diagnostic:\n"
                               f"{proc.stderr}") from err
        code = diagnostic.get("code", "")
        if not code.startswith("RUNTIME-"):
            raise HarnessError(f"case {halted}: {code} is not a runtime error:\n{proc.stderr}")
        frame = halt_frame(diagnostic.get("stack") or [])
        if frame is None or " (" in frame:
            raise HarnessError(f"case {halted}: the harness halted in {frame}:\n{proc.stderr}")
        actual[halted] = f"halt {code}"
        start = halted + 1
    return actual


def compare(agentica: str, text: str) -> int:
    """Runs the cases of `text`; returns the number of differences."""
    cases = read_cases(text)
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "cases.tsv")
        with open(path, "w", encoding="utf-8") as f:
            f.write(text)
        actual = run_vm(agentica, path, len(cases))
    failures = 0
    for id_, fn, args, expected in cases:
        got = actual.get(id_, "<no result>")
        if got != expected:
            failures += 1
            print(f"case {id_}: {fn}({args.replace(' ', ', ')})")
            print(f"  Lean: {expected}")
            print(f"  VM:   {got}")
    print(f"difftest: {len(cases) - failures}/{len(cases)} cases agree")
    return failures


def self_test(agentica: str, text: str) -> int:
    """Each planted input must fail, for its own reason."""
    lines = text.splitlines(keepends=True)

    def planted_missing_argument() -> str:
        # The first `at` case that halts, with its index argument dropped: it
        # must not pass as the halt of Bytes.at.
        out = list(lines)
        for k, line in enumerate(out):
            id_, fn, args, expected = line.rstrip("\n").split("\t")
            if fn == "at" and expected.startswith("halt"):
                out[k] = "\t".join([id_, fn, args.split(" ")[0], expected]) + "\n"
                return "".join(out)
        raise AssertionError("no halting at case")

    def planted_changed_value() -> str:
        out = list(lines)
        id_, fn, args, expected = out[0].rstrip("\n").split("\t")
        out[0] = "\t".join([id_, fn, args, expected + "1"]) + "\n"
        return "".join(out)

    def planted_wrong_kind() -> str:
        # The first Result error, with another kind and the same message.
        out = list(lines)
        for k, line in enumerate(out):
            id_, fn, args, expected = line.rstrip("\n").split("\t")
            if expected.startswith("error argument "):
                wrong = expected.replace("error argument ", "error number.range ", 1)
                out[k] = "\t".join([id_, fn, args, wrong]) + "\n"
                return "".join(out)
        raise AssertionError("no error argument case")

    def planted_halt(function: str, expected: str) -> tuple[bool, str]:
        # A halt in `function` of a program other than diff/run.agc: the run
        # must be refused, naming that frame.
        with tempfile.TemporaryDirectory() as tmp:
            program = os.path.join(tmp, "halts.agc")
            with open(program, "w", encoding="utf-8") as f:
                f.write(f"def {function}(n: Int) -> Int\n  return [1][n]\nend\n\n"
                        f"def main() -> Void\n  puts({function}(System.args().size))\nend\n")
            try:
                run_vm(agentica, os.path.join(tmp, "none.tsv"), 1, program)
            except HarnessError as err:
                return expected in str(err), f"harness error: {str(err).splitlines()[0]}"
            return False, "no error"

    halt_bad = 0
    for name, function, expected in [
        ("a halt in the harness", "run_case", "halted in run_case"),
        ("a call_ frame in another file", "call_at", "halted in call_at ("),
    ]:
        ok, got = planted_halt(function, expected)
        print(f"self-test: {name}: {'fails as it should' if ok else 'NOT CAUGHT'} ({got})")
        halt_bad += 0 if ok else 1

    planted = [
        ("an empty case file", "", "no cases"),
        ("a case list without add", "".join(l for l in lines if "\tadd\t" not in l),
         "functions differ"),
        ("a case with a missing argument", planted_missing_argument(), "harness bad case"),
        ("a changed expected value", planted_changed_value(), None),
        ("a wrong error kind", planted_wrong_kind(), None),
    ]
    bad = 0
    for name, planted_text, reason in planted:
        try:
            failures = compare(agentica, planted_text)
            ok = reason is None and failures > 0
            got = f"{failures} differences"
        except HarnessError as err:
            ok = reason is not None and reason in str(err)
            got = f"harness error: {str(err).splitlines()[0]}"
        print(f"self-test: {name}: {'fails as it should' if ok else 'NOT CAUGHT'} ({got})")
        bad += 0 if ok else 1
    return 1 if bad or halt_bad else 0


def main() -> int:
    agentica = find_agentica()
    if agentica is None:
        if os.environ.get("REQUIRE_AGENTICA") == "1":
            print("difftest: no agentica binary (set AGENTICA or PATH)", file=sys.stderr)
            return 1
        print("difftest: skipped, no agentica binary (set AGENTICA or put it on PATH)")
        return 0
    version = subprocess.run([agentica, "--version"], capture_output=True, text=True,
                             check=True).stdout.strip()
    print(f"difftest: agentica {version}")
    if os.environ.get("DIFF_CASES"):
        with open(os.environ["DIFF_CASES"], encoding="utf-8") as f:
            text = f.read()
    else:
        text = subprocess.run(["lake", "exe", "diffcases"], capture_output=True, text=True,
                              check=True).stdout
    try:
        if sys.argv[1:] == ["--self-test"]:
            return self_test(agentica, text)
        return 1 if compare(agentica, text) else 0
    except HarnessError as err:
        print(f"difftest: harness error: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
