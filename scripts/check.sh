#!/usr/bin/env bash
# The checks around `lake build --wfail` (see AGENTS.md). Run it from the repo
# root after a build. It leaves the tree as it found it.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

# 1. Spec.lean imports every file under Spec/: Check/Axioms.lean imports
#    Spec, so it sees only those modules. Reads `import A B`, `public import`
#    and a trailing `--` comment.
imports=$(sed -E 's/--.*$//' Spec.lean |
  awk '$1 == "public" { $1 = "" } { $0 = $0 } $1 == "import" { for (i = 2; i <= NF; i++) print $i }')
while IFS= read -r file; do
  module=$(echo "${file%.lean}" | tr / .)
  if ! grep -qxF "$module" <<<"$imports"; then
    echo "Spec.lean does not import $module ($file)"
    status=1
  fi
done < <(find Spec -name '*.lean' | sort)

# 2. debug.skipKernelTC leaves no trace on a constant, so Check/Axioms.lean
#    cannot see it. (It catches unsafe, implemented_by and extern itself.)
if grep -rn 'skipKernelTC' Spec Spec.lean; then
  echo "Spec turns off the kernel check (see AGENTS.md)"
  status=1
fi

# 3. Self-test: the axiom check rejects each bad declaration of the fixture.
#    The fixture goes in, the build must fail naming each one with its
#    axiom or escape, and the tree is put back.
fixture=Spec/AxiomCheckFixture.lean
backup=$(mktemp)
cp Spec.lean "$backup"
restore() {
  cp "$backup" Spec.lean
  rm -f "$fixture" "$backup"
}
trap restore EXIT
cp tests/AxiomFixture.lean "$fixture"
# Imports must come first in a Lean file.
sed -i '1i import Spec.AxiomCheckFixture' Spec.lean
if output=$(lake build 2>&1); then
  echo "the axiom check passed a fixture it must reject"
  status=1
else
  expected=(
    'axiomFixtureSorry uses [sorryAx]'
    'axiomFixtureNative uses [axiomFixtureNative._native.native_decide.ax_'
    'axiomFixtureBvDecide uses [axiomFixtureBvDecide._native.bv_decide.ax_'
    'axiomFixtureUnsafe is unsafe'
    'axiomFixtureImplementedBy has implemented_by'
    'axiomFixtureExtern is extern'
  )
  for line in "${expected[@]}"; do
    if ! grep -qF "$line" <<<"$output"; then
      echo "the axiom check did not report: $line"
      status=1
    fi
  done
  if [ "$status" -ne 0 ]; then echo "$output"; fi
fi
restore
trap - EXIT
# Rebuild the clean tree, so .lake does not keep the fixture's modules.
lake build --wfail

if [ "$status" -eq 0 ]; then echo "check.sh: ok"; fi
exit "$status"
