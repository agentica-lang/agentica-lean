#!/usr/bin/env python3
"""Differential test: the Lean prelude against the agentica binary.

`lake exe diffcases` prints the cases with the Lean results (the only source
of cases). `diff/run.agc` runs the same cases on agentica. A case that halts
ends that run; this script records its diagnostic code and starts again after
it. Then it compares each case, values and diagnostic codes only (a message
is compared only when it is a `Result` value).

The binary is `$AGENTICA`, or `agentica` on PATH. Without one the test skips,
unless `REQUIRE_AGENTICA=1` (CI), which makes it fail.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile

# The functions of diff/run.agc that read the cases: a halt there is a bug of
# the harness, not a result.
HARNESS_FUNCTIONS = {"main", "int_arg", "bytes_arg"}


def find_agentica() -> str | None:
    path = os.environ.get("AGENTICA") or shutil.which("agentica")
    return path if path and os.access(path, os.X_OK) else None


def read_cases(text: str) -> list[tuple[int, str, str, str]]:
    cases = []
    for line in text.splitlines():
        id_, fn, args, expected = line.split("\t")
        cases.append((int(id_), fn, args, expected))
    return cases


def run_vm(agentica: str, cases_path: str, count: int) -> dict[int, str]:
    """Runs every case on agentica, restarting after each halt."""
    actual: dict[int, str] = {}
    start = 0
    while start < count:
        proc = subprocess.run(
            [agentica, "--json", "diff/run.agc", cases_path, str(start)],
            capture_output=True, text=True, check=False)
        last = start - 1
        for line in proc.stdout.splitlines():
            id_, result = line.split("\t", 1)
            actual[int(id_)] = result
            last = int(id_)
        if proc.returncode == 0:
            break
        halted = last + 1
        try:
            diagnostic = json.loads(proc.stderr.strip().splitlines()[-1])
        except (ValueError, IndexError):
            sys.exit(f"case {halted}: agentica failed without a diagnostic:\n{proc.stderr}")
        top = (diagnostic.get("stack") or [{}])[0]
        if top.get("file") == "diff/run.agc" and top.get("function") in HARNESS_FUNCTIONS:
            sys.exit(f"case {halted}: the harness halted outside a case:\n{proc.stderr}")
        actual[halted] = f"halt {diagnostic['code']}"
        start = halted + 1
    return actual


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
    cases_text = os.environ.get("DIFF_CASES")
    if cases_text:
        with open(cases_text, encoding="utf-8") as f:
            text = f.read()
    else:
        text = subprocess.run(["lake", "exe", "diffcases"], capture_output=True, text=True,
                              check=True).stdout
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
    print(f"difftest: {len(cases) - failures}/{len(cases)} cases agree (agentica {version})")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
