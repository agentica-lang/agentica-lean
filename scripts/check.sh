#!/usr/bin/env bash
# The checks around `lake build --wfail` (see AGENTS.md). Run it from the repo
# root after a build. It leaves the tree as it found it.
set -euo pipefail
cd "$(dirname "$0")/.."

status=0

# 1. Spec.lean imports every file under Spec/: Check/Axioms.lean imports
#    Spec, so it sees only those modules.
while IFS= read -r file; do
  module=$(echo "${file%.lean}" | tr / .)
  if ! grep -qx "import $module" Spec.lean; then
    echo "Spec.lean does not import $module ($file)"
    status=1
  fi
done < <(find Spec -name '*.lean' | sort)

# 2. Escapes that add no axiom, so the axiom check cannot see them.
if grep -rnE 'skipKernelTC|implemented_by|@\[extern|\bunsafe\b' Spec Spec.lean; then
  echo "Spec uses an escape that skips the kernel (see AGENTS.md)"
  status=1
fi

# 3. Self-test: the axiom check rejects a sorry, a native_decide and a
#    bv_decide. The fixture goes in, the build must fail naming all three,
#    and the tree is put back.
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
  for name in axiomFixtureSorry axiomFixtureNative axiomFixtureBvDecide; do
    if ! grep -q "^$name uses" <<<"$output"; then
      echo "the axiom check did not report $name"
      status=1
    fi
  done
fi
restore
trap - EXIT
# Rebuild the clean tree, so .lake does not keep the fixture's modules.
lake build --wfail > /dev/null

if [ "$status" -eq 0 ]; then echo "check.sh: ok"; fi
exit "$status"
